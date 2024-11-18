//! Implementation of `rustc` driver for `pallet-verifier`.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hash;
extern crate rustc_session;

mod cli_utils;

use rustc_hash::{FxHashMap, FxHashSet};

use std::{
    env,
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::exit,
};

use itertools::Itertools;

use cli_utils::{ENV_DEP_ANNOTATE_CRATE, ENV_DEP_FEATURE_CRATE, ENV_DEP_RENAMES};
use pallet_verifier::{
    DefaultCallbacks, DependencyCallbacks, EntryPointsCallbacks, EntrysPointInfo,
    VerifierCallbacks, VirtualFileLoader, CONTRACTS_MOD_NAME, ENTRY_POINTS_MOD_NAME,
};

const COMMAND: &str = "pallet-verifier";

fn main() {
    // Initializes loggers (if necessary).
    init_loggers();

    // Shows help and version messages (and exits, if necessary).
    cli_utils::handle_meta_args(COMMAND);

    // Retrieves command line arguments.
    let mut args: Vec<_> = env::args().collect();
    // Setting `RUSTC_WRAPPER` causes `cargo` to pass 'rustc' as the first argument.
    // We're invoking the compiler programmatically, so we remove it (if present).
    // Ref: <https://doc.rust-lang.org/cargo/reference/config.html#buildrustc-wrapper>
    // Ref: <https://doc.rust-lang.org/cargo/reference/environment-variables.html#environment-variables-cargo-reads>
    // Ref: <https://github.com/rust-lang/rust-clippy/blob/caad063933e5012b152d883a6c03f1d0ad5ec6a8/src/driver.rs#L244-L251>
    let is_rustc_wrapper_mode = args.get(1).is_some_and(|arg| cli_utils::is_rustc_path(arg));
    if is_rustc_wrapper_mode {
        args.remove(1);
    }

    // The `PALLET_VERIFIER_DEP_FEATURE_CRATE` env var is only set when compiling a dependency crate
    // that needs some unstable features to be enabled, so we invoke an appropriate compiler and exit.
    if env::var(ENV_DEP_FEATURE_CRATE).is_ok() {
        exit(compile_dependency(&args));
    }

    // Compiles `mirai-annotations` crate and adds it as a dependency (if necessary).
    let mut annotations_source_info = None;
    if !has_mirai_annotations_dep() {
        let Ok((annotations_out_file, annotations_path, annotations_content)) =
            compile_annotations_crate()
        else {
            // Exit if `mirai-annotations` crate compilation failed,
            // presumably, the compiler already emitted an error in this case.
            exit(rustc_driver::EXIT_FAILURE);
        };

        // Track annotations source map input path and content for later user by virtual file loaders.
        annotations_source_info = Some((annotations_path.clone(), annotations_content.to_owned()));

        // Add `mirai-annotations` crate as a dependency.
        // Ref: <https://doc.rust-lang.org/rustc/command-line-arguments.html#--extern-specify-where-an-external-library-is-located>
        args.extend([
            "--extern".to_owned(),
            format!("mirai_annotations={}", annotations_out_file.display()),
        ]);
    }

    // The `PALLET_VERIFIER_DEP_ANNOTATE_CRATE` env var is only set when compiling a dependency crate,
    // that needs annotations,so we invoke an appropriate compiler and exit.
    if env::var(ENV_DEP_ANNOTATE_CRATE).is_ok() {
        exit(compile_annotated_dependency(
            &args,
            annotations_source_info.clone(),
        ));
    }

    // If neither `CARGO_PKG_NAME` nor `CARGO_PRIMARY_PACKAGE`, then presumably this is
    // some kind of direct call to the `pallet-verifier` binary, instead of via `cargo verify-pallet`,
    // so we need to set some extra flags.
    // Ref: <https://doc.rust-lang.org/rustc/command-line-arguments.html>
    if env::var("CARGO_PKG_NAME").is_err() || env::var("CARGO_PRIMARY_PACKAGE").is_err() {
        args.extend(
            [
                // Enables compilation of unit tests and test harness generation.
                // Ref: <https://doc.rust-lang.org/rustc/command-line-arguments.html#--test-build-a-test-harness>
                "--test",
                // Enables dumping MIR for all functions.
                // Ref: <https://github.com/rust-lang/rust/blob/master/compiler/rustc_session/src/options.rs#L1632>
                // Ref: <https://hackmd.io/@rust-compiler-team/r1JECK_76#metadata-and-depinfo>
                "-Zalways-encode-mir=yes",
                // Disables debug assertions.
                // Ref: <https://doc.rust-lang.org/rustc/codegen-options/index.html#debug-assertions>
                "-Cdebug-assertions=no",
                // Enables overflow checks.
                // Ref: <https://doc.rust-lang.org/rustc/codegen-options/index.html#overflow-checks>
                "-Coverflow-checks=yes",
            ]
            .map(ToOwned::to_owned),
        );
    }

    // Generates "tractable" entry points for FRAME pallet (if possible).
    let Ok((entry_points_content, entry_points_info)) =
        generate_entry_points(&args, annotations_source_info.clone())
    else {
        // Exit if entry point generation failed,
        // presumably, the compiler already emitted an error in this case.
        exit(rustc_driver::EXIT_FAILURE);
    };

    // Analyzes FRAME pallet with MIRAI.
    // Enables compilation of MIRAI only code.
    args.push("--cfg=mirai".to_owned());
    exit(analyze_with_mirai(
        &args,
        entry_points_content,
        &entry_points_info,
        annotations_source_info,
    ));
}

/// Compiles and analyses target crate (presumably a FRAME pallet) to generate "tractable" entry points.
/// Returns a tuple of the raw entry point content (as a `String`),
/// as well some entry points metadata (as [`EntryPointsInfo`]) if successful.
fn generate_entry_points(
    args: &[String],
    annotations_source_info: AnnotationsSourceInfo,
) -> Result<(String, EntrysPointInfo), ()> {
    let dep_renames = env::var(ENV_DEP_RENAMES).ok().and_then(|dep_renames_json| {
        serde_json::from_str::<rustc_hash::FxHashMap<String, String>>(&dep_renames_json).ok()
    });
    let mut callbacks = EntryPointsCallbacks::new(&dep_renames);
    let mut compiler = rustc_driver::RunCompiler::new(args, &mut callbacks);
    let target_path = analysis_target_path(args);
    let file_loader = analysis_file_loader(target_path, &[], annotations_source_info, true);
    compiler.set_file_loader(Some(Box::new(file_loader)));
    compiler.run().map_err(|_| ()).and_then(|_| {
        callbacks
            .entry_points_content()
            .map(|content| (content, callbacks.entry_points_info()))
            .ok_or(())
    })
}

/// Analyzes FRAME pallet with MIRAI.
fn analyze_with_mirai(
    args: &[String],
    entry_points_content: String,
    entry_points_info: &EntrysPointInfo,
    annotations_source_info: AnnotationsSourceInfo,
) -> i32 {
    let mut callbacks = VerifierCallbacks::new(entry_points_info);
    let mut compiler = rustc_driver::RunCompiler::new(args, &mut callbacks);
    let target_path = analysis_target_path(args);
    let file_loader = analysis_file_loader(
        target_path,
        &[
            // Adds generated entry points.
            (ENTRY_POINTS_MOD_NAME, entry_points_content),
            // Adds MIRAI contracts for FRAME/Substrate functions.
            (
                CONTRACTS_MOD_NAME,
                include_str!("../artifacts/contracts.rs").to_owned(),
            ),
        ],
        annotations_source_info,
        true,
    );
    compiler.set_file_loader(Some(Box::new(file_loader)));
    match compiler.run() {
        Ok(_) => rustc_driver::EXIT_SUCCESS,
        Err(_) => rustc_driver::EXIT_FAILURE,
    }
}

/// Type alias for tracking input path and content used for compiling `mirai-annotations` crate (if any).
type AnnotationsSourceInfo = Option<(PathBuf, String)>;

/// Compiles annotated dependencies.
fn compile_annotated_dependency(
    args: &[String],
    annotations_source_info: AnnotationsSourceInfo,
) -> i32 {
    let mut callbacks = DependencyCallbacks;
    let mut compiler = rustc_driver::RunCompiler::new(args, &mut callbacks);
    let target_path = analysis_target_path(args);
    let file_loader = analysis_file_loader(target_path, &[], annotations_source_info, false);
    compiler.set_file_loader(Some(Box::new(file_loader)));
    match compiler.run() {
        Ok(_) => rustc_driver::EXIT_SUCCESS,
        Err(_) => rustc_driver::EXIT_FAILURE,
    }
}

/// Compiles dependencies.
fn compile_dependency(args: &[String]) -> i32 {
    let mut callbacks = DefaultCallbacks;
    let mut compiler = rustc_driver::RunCompiler::new(args, &mut callbacks);
    let target_path = analysis_target_path(args);
    let crate_name = cli_utils::arg_value("--crate-name").expect("Expected a target crate");
    let features = lang_features(&crate_name);
    if features.is_some() {
        let mut source_map = FxHashMap::default();
        source_map.insert(target_path, (None, features, None, None));
        let file_loader = VirtualFileLoader::new(source_map);
        compiler.set_file_loader(Some(Box::new(file_loader)));
    }
    match compiler.run() {
        Ok(_) => rustc_driver::EXIT_SUCCESS,
        Err(_) => rustc_driver::EXIT_FAILURE,
    }
}

/// Compiles `mirai-annotations` crate and returns output `rlib` path, the input path and content if successful.
fn compile_annotations_crate() -> Result<(PathBuf, PathBuf, String), ()> {
    let input_path = Path::new("$virtual/pallet-verifier/mirai_annotations/src/lib.rs");
    let mut out_dir = cli_utils::arg_value("--out-dir")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            let mut target_dir = env::current_dir().expect("Expected valid current dir");
            target_dir.push("target/debug/deps");
            target_dir
        });
    if !out_dir.ends_with("deps") {
        out_dir.push("deps");
        fs::create_dir_all(&out_dir).expect("Failed to create `deps` directory");
    }
    let mut out_path = out_dir.clone();
    let suffix = "pallet-verifier";
    out_path.push(format!("libmirai_annotations-{suffix}.rlib"));
    let mut args = [
        // NOTE: `rustc` ignores the first argument, so we set that to "pallet-verifier".
        "pallet-verifier",
        "--crate-name=mirai_annotations",
        "--edition=2021",
        &format!("{}", input_path.display()),
        "--crate-type=lib",
        "--emit=dep-info,metadata,link",
        "-Cembed-bitcode=no",
        &format!("-Cmetadata={suffix}"),
        &format!("-Cextra-filename=-{suffix}"),
        &format!("--out-dir={}", out_dir.display()),
        "--cfg=mirai",
        "-Zalways_encode_mir=yes",
        "--cap-lints=allow",
    ]
    .map(ToString::to_string)
    .to_vec();
    if let Some(target) = cli_utils::arg_value("--target") {
        args.push(format!("--target={target}"));
    }
    if let Some(error_format) = cli_utils::arg_value("--error-format") {
        args.push(format!("--error-format={error_format}"));
    }
    if let Some(json_config) = cli_utils::arg_value("--json") {
        args.push(format!("--json={json_config}"));
    }
    let mut callbacks = DefaultCallbacks;
    let input_content = include_str!("../artifacts/mirai_annotations.rs");
    let mut source_map = FxHashMap::default();
    source_map.insert(
        input_path.to_path_buf(),
        (Some(input_content.to_owned()), None, None, None),
    );
    let file_loader = VirtualFileLoader::new(source_map);
    let mut compiler = rustc_driver::RunCompiler::new(&args, &mut callbacks);
    compiler.set_file_loader(Some(Box::new(file_loader)));
    compiler
        .run()
        .map(|_| (out_path, input_path.to_path_buf(), input_content.to_owned()))
        .map_err(|_| ())
}

/// Creates "virtual" `FileLoader` for "analysis-only" external crates and "virtual" modules
/// (e.g. for entry point and "contracts" content).
fn analysis_file_loader(
    target_path: PathBuf,
    // `name` -> `content` map for "virtual" modules.
    virtual_mods: &[(&str, String)],
    annotations_source_info: AnnotationsSourceInfo,
    include_annotated_deps: bool,
) -> VirtualFileLoader {
    let crate_name = cli_utils::arg_value("--crate-name").unwrap_or_default();
    let mut extern_crates = None;
    if !has_mirai_annotations_dep()
        || fs::read_to_string(&target_path)
            .is_ok_and(|content| !content.contains("mirai_annotations"))
    {
        extern_crates = Some(FxHashSet::from_iter(["mirai_annotations"]));
    }
    let mut analysis_source_map = FxHashMap::default();
    analysis_source_map.insert(
        target_path.clone(),
        (
            None,
            lang_features(&crate_name),
            extern_crates.clone(),
            (!virtual_mods.is_empty()).then_some(virtual_mods.iter().cloned().collect()),
        ),
    );
    if let Some((annotations_path, annotations_content)) = annotations_source_info {
        analysis_source_map.insert(
            annotations_path,
            (Some(annotations_content), None, None, None),
        );
    }
    if include_annotated_deps {
        let mut is_extern_val_next = false;
        for arg in env::args() {
            if arg == "--extern" {
                is_extern_val_next = true;
                continue;
            }
            if !is_extern_val_next {
                continue;
            }
            is_extern_val_next = false;
            let Some((_, extern_path_str)) = arg.splitn(2, '=').collect_tuple() else {
                continue;
            };
            let extern_path = Path::new(extern_path_str);
            let is_rlib_path = extern_path.extension().is_some_and(|ext| ext == "rlib");
            if !is_rlib_path {
                continue;
            }
            let filename = extern_path
                .file_stem()
                .and_then(OsStr::to_str)
                .and_then(|name| name.strip_prefix("lib"));
            let Some(filename) = filename else {
                continue;
            };
            let Some((dep_crate_name, _)) = filename.splitn(2, '-').collect_tuple() else {
                continue;
            };
            let is_pallet_dep = arg.starts_with("pallet_");
            if !is_pallet_dep && !cli_utils::requires_unstable_features(dep_crate_name) {
                continue;
            }
            let mut dep_info_path = extern_path.to_path_buf();
            dep_info_path.set_file_name(format!("{filename}.d"));
            let dep_info =
                fs::read_to_string(&dep_info_path).expect("Expected test dependencies info");
            let lib_src_path = dep_info.lines().find_map(|line| {
                if !line.starts_with(char::is_whitespace) && !line.is_empty() {
                    let path_str = line.strip_suffix(':')?;
                    let path = Path::new(path_str);
                    let filename = path.file_stem()?.to_str()?;
                    let ext = path.extension()?;
                    if filename == "lib" && ext == "rs" {
                        return Some(path);
                    }
                }
                None
            });
            let Some(lib_src_path) = lib_src_path else {
                continue;
            };
            let abs_lib_src_path = if lib_src_path.is_relative() {
                env::current_dir()
                    .expect("Expected valid current working directory")
                    .join(lib_src_path)
            } else {
                lib_src_path.to_path_buf()
            };
            analysis_source_map.insert(
                abs_lib_src_path,
                (
                    None,
                    lang_features(dep_crate_name),
                    if is_pallet_dep {
                        extern_crates.clone()
                    } else {
                        None
                    },
                    None,
                ),
            );
        }
    }
    VirtualFileLoader::new(analysis_source_map)
}

// Reads the analysis target path as the "normalized" first `*.rs` argument from CLI args.
fn analysis_target_path(args: &[String]) -> PathBuf {
    let target_path_str = args
        .iter()
        .find(|arg| Path::new(arg).extension().is_some_and(|ext| ext == "rs"))
        .expect("Expected target path as the first `*.rs` argument");
    PathBuf::from(target_path_str)
}

/// Returns true if the `mirai-annotations` crate was already included as a dependency
/// in the original args passed to `pallet-verifier`.
fn has_mirai_annotations_dep() -> bool {
    env::args().enumerate().any(|(idx, arg)| {
        arg.starts_with("mirai_annotations")
            && env::args()
                .nth(idx - 1)
                .is_some_and(|arg| arg == "--extern")
    })
}

/// Returns a list of language features (if any) to enable for given crate.
fn lang_features(crate_name: &str) -> Option<FxHashSet<&'static str>> {
    match crate_name {
        // TODO: Remove when compiler is updated to >= 1.79
        // Ref: <https://github.com/paritytech/parity-scale-codec/blob/master/Cargo.toml#L73C1-L73C13>
        // Ref: <https://blog.rust-lang.org/2024/06/13/Rust-1.79.0.html#inline-const-expressions>
        "parity_scale_codec" => Some(FxHashSet::from_iter(["inline_const"])),
        // TODO: Remove when compiler is update to >= 1.80
        // Ref: <https://blog.rust-lang.org/2024/07/25/Rust-1.80.0.html#lazycell-and-lazylock>
        "sp_panic_handler" | "sp_trie" | "sp_core" | "sp_consensus_beefy" => {
            Some(FxHashSet::from_iter(["lazy_cell"]))
        }
        _ => None,
    }
}

/// Initializes loggers (if necessary).
fn init_loggers() {
    // Only continue if a log level is set via `PALLET_VERIFIER_LOG` env var.
    let Ok(log) = env::var("PALLET_VERIFIER_LOG") else {
        return;
    };

    // Initialize `rustc` logger.
    env::set_var("RUSTC_LOG", &log);
    env::set_var("RUSTC_LOG_COLOR", "always");
    let early_error_handler =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&early_error_handler);

    // Initialize `MIRAI` logger.
    env::set_var("MIRAI_LOG", &log);
    env::set_var("MIRAI_LOG_STYLE", "always");
    let e = env_logger::Env::new()
        .filter("MIRAI_LOG")
        .write_style("MIRAI_LOG_STYLE");
    env_logger::init_from_env(e);
}
