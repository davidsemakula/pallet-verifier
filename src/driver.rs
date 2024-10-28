//! Implementation of `rustc` driver for `pallet-verifier`.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hash;
extern crate rustc_session;

mod cli_utils;

use rustc_hash::FxHashSet;

use std::{
    env, fs,
    path::{Path, PathBuf},
    process,
};

use cli_utils::{ENV_DEP_CRATE, ENV_DEP_RENAMES};
use pallet_verifier::{
    DefaultCallbacks, DependencyCallbacks, EntryPointsCallbacks, VerifierCallbacks,
    VirtualFileLoader, CONTRACTS_MOD_NAME, ENTRY_POINTS_MOD_NAME,
};

const COMMAND: &str = "pallet-verifier";

fn main() {
    // Initializes loggers.
    if let Ok(log) = env::var("PALLET_VERIFIER_LOG") {
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

    // Shows help and version messages (and exits, if necessary).
    cli_utils::handle_meta_args(COMMAND);

    // Retrieves command line arguments.
    let mut cli_args: Vec<_> = env::args().collect();
    // Setting `RUSTC_WRAPPER` causes `cargo` to pass 'rustc' as the first argument.
    // We're invoking the compiler programmatically, so we remove it (if present).
    // Ref: <https://doc.rust-lang.org/cargo/reference/config.html#buildrustc-wrapper>
    // Ref: <https://doc.rust-lang.org/cargo/reference/environment-variables.html#environment-variables-cargo-reads>
    // Ref: <https://github.com/rust-lang/rust-clippy/blob/caad063933e5012b152d883a6c03f1d0ad5ec6a8/src/driver.rs#L244-L251>
    let is_rustc_wrapper_mode = cli_args
        .get(1)
        .is_some_and(|arg| cli_utils::is_rustc_path(arg));
    if is_rustc_wrapper_mode {
        cli_args.remove(1);
    }

    // Compiles `mirai-annotations` crate and adds it as a dependency (if necessary).
    // Ref: <https://doc.rust-lang.org/rustc/command-line-arguments.html>
    let has_mirai_annotations_dep = cli_args.iter().enumerate().any(|(idx, arg)| {
        arg.starts_with("mirai_annotations")
            && cli_args.get(idx - 1).is_some_and(|arg| arg == "--extern")
    });
    if !has_mirai_annotations_dep {
        let mut annotations_path = env::current_dir().expect("Expected valid current dir");
        annotations_path.push("__pallet_verifier_artifacts/mirai_annotations/src/lib.rs");
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
        let mut annotations_out_file = out_dir.clone();
        let suffix = "pallet-verifier";
        annotations_out_file.push(format!("libmirai_annotations-{suffix}.rlib"));
        let mut annotations_args = [
            // NOTE: `rustc` ignores the first argument, so we set that to "pallet-verifier".
            "pallet-verifier",
            "--crate-name=mirai_annotations",
            "--edition=2021",
            &format!("{}", annotations_path.display()),
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
            annotations_args.push(format!("--target={target}"));
        }
        let mut rustc_callbacks = DefaultCallbacks;
        let annotations_file_loader = VirtualFileLoader::new(
            annotations_path,
            Some(include_str!("../artifacts/mirai_annotations.rs").to_owned()),
            None,
            None,
        );
        let mut annotations_compiler =
            rustc_driver::RunCompiler::new(&annotations_args, &mut rustc_callbacks);
        annotations_compiler.set_file_loader(Some(Box::new(annotations_file_loader)));
        let annotations_result = annotations_compiler.run();
        if annotations_result.is_err() {
            process::exit(rustc_driver::EXIT_FAILURE);
        }
        cli_args.extend([
            // Add `mirai-annotations` crate as a dependency.
            // Ref: <https://doc.rust-lang.org/rustc/command-line-arguments.html#--extern-specify-where-an-external-library-is-located>
            "--extern".to_owned(),
            format!("mirai_annotations={}", annotations_out_file.display()),
        ]);
    }

    // Initializes "virtual" `FileLoader` for "analysis-only" external crates.
    // Reads the analysis target path as the "normalized" first `*.rs` argument from CLI args.
    let target_path_str = cli_args
        .iter()
        .find(|arg| Path::new(arg).extension().is_some_and(|ext| ext == "rs"))
        .expect("Expected target path as the first `*.rs` argument");
    let target_path = PathBuf::from(target_path_str);
    let mut extern_crates_opt = None;
    if !has_mirai_annotations_dep
        || fs::read_to_string(target_path.clone())
            .is_ok_and(|content| !content.contains("mirai_annotations"))
    {
        let mut extern_crates = FxHashSet::default();
        extern_crates.insert("mirai_annotations");
        extern_crates_opt = Some(extern_crates);
    }
    let analysis_file_loader =
        VirtualFileLoader::new(target_path.clone(), None, extern_crates_opt.as_ref(), None);

    // The `PALLET_VERIFIER_DEP_CRATE` env var is only set when compiling/annotating a dependency crate,
    // So we invoke an appropriate compiler and exit.
    if env::var(ENV_DEP_CRATE).is_ok() {
        let mut callbacks = DependencyCallbacks;
        let mut compiler = rustc_driver::RunCompiler::new(&cli_args, &mut callbacks);
        compiler.set_file_loader(Some(Box::new(analysis_file_loader)));
        let result = compiler.run();
        let exit_code = match result {
            Ok(_) => rustc_driver::EXIT_SUCCESS,
            Err(_) => rustc_driver::EXIT_FAILURE,
        };
        process::exit(exit_code);
    }

    // If neither `CARGO_PKG_NAME` nor `CARGO_PRIMARY_PACKAGE`, then presumably this is
    // some kind of direct call to the `pallet-verifier` binary, instead of via `cargo verify-pallet`,
    // so we need to set some extra flags.
    // Ref: <https://doc.rust-lang.org/rustc/command-line-arguments.html>
    if env::var("CARGO_PKG_NAME").is_err() || env::var("CARGO_PRIMARY_PACKAGE").is_err() {
        cli_args.extend(
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

    // Generates tractable entry points for FRAME pallet.
    let dep_renames = env::var(ENV_DEP_RENAMES).ok().and_then(|dep_renames_json| {
        serde_json::from_str::<rustc_hash::FxHashMap<String, String>>(&dep_renames_json).ok()
    });
    let mut entry_point_callbacks = EntryPointsCallbacks::new(&dep_renames);
    let mut entry_point_compiler =
        rustc_driver::RunCompiler::new(&cli_args, &mut entry_point_callbacks);
    entry_point_compiler.set_file_loader(Some(Box::new(analysis_file_loader)));
    let entry_point_result = entry_point_compiler.run();
    if entry_point_result.is_err() {
        process::exit(rustc_driver::EXIT_FAILURE);
    }
    let Some(entry_points_content) = entry_point_callbacks.entry_points_content() else {
        process::exit(rustc_driver::EXIT_FAILURE);
    };

    // Initializes "virtual" `FileLoader` for "analysis-only" external crates,
    // and entry point and "contracts" content.
    let verifier_file_loader = VirtualFileLoader::new(
        target_path,
        None,
        extern_crates_opt.as_ref(),
        Some(
            [
                // Adds generated entry points.
                (ENTRY_POINTS_MOD_NAME, entry_points_content),
                // Adds MIRAI contracts for FRAME/Substrate functions.
                (
                    CONTRACTS_MOD_NAME,
                    include_str!("../artifacts/contracts.rs").to_owned(),
                ),
            ]
            .into_iter()
            .collect(),
        ),
    );

    // Analyzes FRAME pallet with MIRAI.
    // Enables compilation of MIRAI only code.
    cli_args.push("--cfg=mirai".to_owned());
    let entry_points_info = entry_point_callbacks.entry_points_info();
    let mut verifier_callbacks = VerifierCallbacks::new(&entry_points_info);
    let mut verifier_compiler = rustc_driver::RunCompiler::new(&cli_args, &mut verifier_callbacks);
    verifier_compiler.set_file_loader(Some(Box::new(verifier_file_loader)));
    let verifier_result = verifier_compiler.run();

    let exit_code = match verifier_result {
        Ok(_) => rustc_driver::EXIT_SUCCESS,
        Err(_) => rustc_driver::EXIT_FAILURE,
    };
    process::exit(exit_code);
}
