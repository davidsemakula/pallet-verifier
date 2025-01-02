//! Implementation of `cargo verify-pallet` subcommand for `pallet-verifier`.

mod cli_utils;

use std::{
    collections::{HashMap, HashSet},
    env, fs,
    path::{Path, PathBuf},
    process::{exit, Command},
};

use owo_colors::OwoColorize;

use cli_utils::{
    ARG_ALLOW_HOOK_PANICS, ARG_AUTO_ANNOTATIONS_DEP, ARG_COMPILE_ANNOTATIONS, ARG_DEP_ANNOTATE,
    ARG_DEP_FEATURES, ARG_POINTER_WIDTH, ENV_DEP_RENAMES, ENV_OPTIONAL_DEPS, HOOKS,
};

const COMMAND: &str = "cargo verify-pallet";

/// Env var set to the name of the top-level package being analyzed
/// (i.e. the package name in the `Cargo.toml` in the directory where `cargo verify-pallet`) is invoked.
const ENV_PKG_NAME: &str = "PALLET_VERIFIER_PKG_NAME";
/// Env var set to the name current `rustc` target (if set).
/// Ref: <https://doc.rust-lang.org/rustc/targets/index.html>
const ENV_TARGET: &str = "PALLET_VERIFIER_TARGET";
/// Env var for tracking path for compiled `mirai-annotations` crate artifact for the "host" platform.
const ENV_ANNOTATIONS_RLIB_PATH_HOST: &str = "PALLET_VERIFIER_ANNOTATIONS_RLIB_PATH_HOST";
/// Env var for tracking path for compiled `mirai-annotations` crate artifact for the "target" platform.
const ENV_ANNOTATIONS_RLIB_PATH_TARGET: &str = "PALLET_VERIFIER_ANNOTATIONS_RLIB_PATH_TARGET";
/// Env var for tracking `--allow-hook-panics` arg passed directly to cargo sub command.
const ENV_ALLOW_HOOK_PANICS: &str = "PALLET_VERIFIER_ALLOW_HOOK_PANICS";

/// filename of compiled `mirai-annotations` crate artifact.
const ANNOTATIONS_RLIB_FILENAME: &str = "libmirai_annotations-pallet-verifier.rlib";

fn main() {
    // Shows help and version messages (and exits, if necessary).
    cli_utils::handle_meta_args(COMMAND);

    // Invokes appropriate command based on CLI args.
    let sub_command = env::args()
        .nth(1)
        .expect("Expected a valid cargo subcommand as the first argument.");
    match sub_command.as_str() {
        // Calls `cargo` with `pallet-verifier` (specifically this cargo subcommand) set as `RUSTC_WRAPPER`.
        "verify-pallet" => call_cargo(),
        // Calls `pallet-verifier` for the "primary" package, and `rustc` for dependencies and build scripts.
        // NOTE: Handles `cargo rustc` since `pallet-verifier` (specifically this cargo subcommand) is set as `RUSTC_WRAPPER`.
        // Ref: <https://doc.rust-lang.org/cargo/reference/environment-variables.html#environment-variables-cargo-reads>
        // Ref: <https://doc.rust-lang.org/cargo/reference/build-scripts.html>
        command if cli_utils::is_rustc_path(command) => {
            let is_primary_package = env::var("CARGO_PRIMARY_PACKAGE").is_ok();
            let is_analysis_target = || {
                let target_pkg_name = env::var(ENV_PKG_NAME);
                target_pkg_name.is_err()
                    || target_pkg_name.is_ok_and(|target_pkg| {
                        env::var("CARGO_PKG_NAME").is_ok_and(|cargo_pkg| target_pkg == cargo_pkg)
                    })
            };
            let is_test_build = || env::args().any(|arg| arg == "--test");
            if is_primary_package && is_analysis_target() && !is_build_script() && is_test_build() {
                // Analyzes "primary" package with `pallet-verifier`.
                // NOTE: Checking for presence of `--test` flag ensures that we don't invoke
                // `pallet-verifier` on a cyclic transitive dependency
                // (i.e. when the "primary" package is also a dependency of one or more of its
                // dependencies, typically under `[dev-dependencies]`).
                call_pallet_verifier(env::args().skip(2), std::iter::empty(), true);
            } else {
                // Adds some extra compilation flags for dependencies and build scripts (if necessary).
                let mut extra_args = Vec::new();
                let mut is_print = false;
                let mut has_check_cfg = false;
                let mut has_unstable_options = false;
                let mut has_cap_lints = false;
                env::args().for_each(|arg| {
                    if arg.contains("--print") {
                        is_print = true;
                    } else if arg.contains("--check-cfg") {
                        has_check_cfg = true;
                    } else if arg.contains("unstable-options") {
                        has_unstable_options = true;
                    } else if arg.contains("--cap-lints") {
                        has_cap_lints = true;
                    }
                });
                if !is_print {
                    // Enables the `unstable-options` flag (if necessary).
                    if has_check_cfg && !has_unstable_options {
                        extra_args.push("-Zunstable-options".to_owned());
                    }
                    // Silence all lints for dependencies and build scripts.
                    // Ref: <https://doc.rust-lang.org/rustc/lints/levels.html#capping-lints>
                    if !has_cap_lints {
                        extra_args.push("--cap-lints=allow".to_string());
                    }
                }

                // Compiles dependencies and build scripts.
                let args = env::args().skip(2).chain(extra_args);
                if is_build_script() {
                    compile_build_script(sub_command, args);
                } else {
                    compile_dependency(sub_command, args);
                }
            }
        }
        _ => {
            eprintln!("Expected a valid cargo subcommand as the first argument.");
            exit(1);
        }
    }
}

/// Calls `cargo` with `pallet-verifier` (specifically this cargo subcommand) set as `RUSTC_WRAPPER`.
fn call_cargo() {
    // Builds cargo command.
    // Ref: <https://doc.rust-lang.org/cargo/commands/cargo-test.html>
    let mut cmd = Command::new("cargo");
    cmd.arg("test");
    cmd.arg("--lib");
    cmd.arg("--no-run");

    // Sets `RUSTC_WRAPPER` to `pallet-verifier` (specifically this cargo subcommand).
    // Ref: <https://doc.rust-lang.org/cargo/reference/config.html#buildrustc-wrapper>
    let path = env::current_exe().expect("Expected valid executable path");
    cmd.env("RUSTC_WRAPPER", path);

    // Sets toolchain to match the compile time value (if any).
    if let Some(toolchain) = option_env!("RUSTUP_TOOLCHAIN") {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain);
    }

    // Enables dumping MIR for all functions, disables debug assertions, enables overflow checks,
    // and disables diagnostics deduplication.
    // Ref: <https://doc.rust-lang.org/cargo/reference/config.html#buildrustflags>
    // Ref: <https://doc.rust-lang.org/rustc/command-line-arguments.html>
    // Ref: <https://github.com/rust-lang/rust/blob/master/compiler/rustc_session/src/options.rs#L1632>
    // Ref: <https://hackmd.io/@rust-compiler-team/r1JECK_76#metadata-and-depinfo>
    // Ref: <https://doc.rust-lang.org/rustc/codegen-options/index.html#debug-assertions>
    // Ref: <https://doc.rust-lang.org/rustc/codegen-options/index.html#overflow-checks>
    let flags = "-Zalways-encode-mir=yes -Cdebug-assertions=no -Coverflow-checks=yes -Zdeduplicate-diagnostics=no";
    cmd.env(
        "RUSTFLAGS",
        env::var("RUSTFLAGS")
            .map(|var| format!("{var} {flags}"))
            .as_deref()
            .unwrap_or(flags),
    );

    // Sets an appropriate rustc `target` based on the passed `--pointer-width` arg value
    // (should be set as either 32 or 64, or skipped altogether).
    // Ref: <https://doc.rust-lang.org/rustc/command-line-arguments.html#--target-select-a-target-triple-to-build>
    // Ref: <https://doc.rust-lang.org/cargo/commands/cargo-test.html#compilation-options>
    let pointer_width = match cli_utils::arg_value(ARG_POINTER_WIDTH).as_deref() {
        Some("32") | None => 32,
        Some("64") => 64,
        _ => {
            eprintln!(
                "{}: Invalid `--pointer-width` arg value, expected `32` or `64`",
                "error".red().bold(),
            );
            exit(1);
        }
    };
    let mut target_platform = None;
    if pointer_width == 32 && cfg!(not(target_pointer_width = "32")) {
        cmd.arg("--target=wasm32-wasi");
        cmd.env(ENV_TARGET, "wasm32-wasi");
        target_platform = Some("wasm32-wasi");
    } else if pointer_width == 64 && cfg!(not(target_pointer_width = "64")) {
        eprintln!("Unsupported host for 64-bit analysis");
        exit(1);
    }
    let pointer_width_str = pointer_width.to_string();
    cmd.env("PALLET_VERIFIER_TARGET_POINTER_WIDTH", &pointer_width_str);
    cmd.env("MIRAI_TARGET_POINTER_WIDTH", &pointer_width_str);

    // Retrieves package metadata.
    let mut metadata_cmd = cargo_metadata::MetadataCommand::new();
    if let Some(manifest_path) = cli_utils::arg_value("--manifest-path") {
        metadata_cmd.manifest_path(manifest_path);
    }
    let metadata = metadata_cmd.exec();

    // Set target package (if necessary), and persists some package metadata.
    let pkg_arg = cli_utils::arg_value("-p").or_else(|| cli_utils::arg_value("--package"));
    let root_package = metadata
        .as_ref()
        .ok()
        .and_then(|metadata| metadata.root_package())
        .or_else(|| {
            pkg_arg.as_ref().and_then(|pkg_name| {
                metadata.as_ref().ok().and_then(|metadata| {
                    metadata
                        .workspace_packages()
                        .into_iter()
                        .find(|package| &package.name == pkg_name)
                })
            })
        });
    if let Some(root_package) = root_package {
        if pkg_arg.is_none() {
            cmd.args(["-p", &root_package.name]);
        }
        cmd.env(ENV_PKG_NAME, &root_package.name);

        let dep_renames: HashMap<_, _> = root_package
            .dependencies
            .iter()
            .filter_map(|dep| {
                dep.rename
                    .as_deref()
                    .map(|rename| (dep.name.replace('-', "_"), rename.replace('-', "_")))
            })
            .collect();
        if let Ok(dep_renames_json) = serde_json::to_string(&dep_renames) {
            cmd.env(ENV_DEP_RENAMES, dep_renames_json);
        }

        let optional_deps: HashSet<_> = root_package
            .dependencies
            .iter()
            .filter_map(|dep| dep.optional.then_some(dep.name.replace('-', "_")))
            .collect();
        if let Ok(optional_deps_json) = serde_json::to_string(&optional_deps) {
            cmd.env(ENV_OPTIONAL_DEPS, optional_deps_json);
        }
    }

    // Sets cargo `--target-dir` arg if it's not already set.
    let current_dir = env::current_dir().expect("Expected valid current dir");
    let target_dir = if let Some(target_dir) = cli_utils::arg_value("--target-dir") {
        PathBuf::from(target_dir)
    } else {
        let mut target_dir = env::var("CARGO_TARGET_DIR")
            .ok()
            .or_else(|| env::var("CARGO_BUILD_TARGET_DIR").ok())
            .as_deref()
            .or_else(|| {
                metadata
                    .as_ref()
                    .map(|metadata| metadata.target_directory.as_str())
                    .ok()
            })
            .map(PathBuf::from)
            .unwrap_or_else(|| current_dir.join("target"));
        target_dir.push("pallet_verifier");
        let is_workspace_member = metadata.as_ref().is_ok_and(|metadata| {
            if metadata.workspace_root == current_dir {
                pkg_arg.as_ref().is_some_and(|pkg_name| {
                    metadata
                        .workspace_packages()
                        .iter()
                        .any(|package| &package.name == pkg_name)
                })
            } else {
                current_dir.starts_with(&metadata.workspace_root)
            }
        });
        if is_workspace_member {
            if let Some(root_package) = root_package {
                target_dir.push(&root_package.name);
            }
        }
        cmd.arg(format!("--target-dir={}", target_dir.display()));
        target_dir
    };

    // Compiles `mirai-annotations` crate, and persists the path(s) to the compiled artifact(s).
    let compile_annotations_arg = format!("{ARG_COMPILE_ANNOTATIONS}=true");
    let annotations_out_dir = create_deps_out_dir(&target_dir);
    let annotation_args = vec![
        compile_annotations_arg.clone(),
        format!("--out-dir={}", annotations_out_dir.display()),
    ];
    call_pallet_verifier(annotation_args.into_iter(), std::iter::empty(), false);
    let annotations_rlib_path = annotations_out_dir.join(ANNOTATIONS_RLIB_FILENAME);
    env::set_var(ENV_ANNOTATIONS_RLIB_PATH_HOST, &annotations_rlib_path);
    let annotations_rlib_path_target = match target_platform {
        Some(target_platform) => {
            // Compiles and persists artifact for "target" platform.
            let annotations_out_dir_target = create_deps_out_dir(&target_dir.join(target_platform));
            let annotation_args_target = vec![
                compile_annotations_arg,
                format!("--out-dir={}", annotations_out_dir_target.display()),
                format!("--target={target_platform}"),
            ];
            call_pallet_verifier(
                annotation_args_target.into_iter(),
                std::iter::empty(),
                false,
            );
            annotations_out_dir_target.join(ANNOTATIONS_RLIB_FILENAME)
        }
        None => annotations_rlib_path,
    };
    env::set_var(
        ENV_ANNOTATIONS_RLIB_PATH_TARGET,
        annotations_rlib_path_target,
    );

    // Allows compilation of `parity-scale-codec >= 3.7.0` which requires `rustc >= 1.79`
    // Ref: <https://github.com/paritytech/parity-scale-codec/blob/master/Cargo.toml#L73C1-L73C13>
    // TODO: Remove when compiler is updated to >= 1.79
    cmd.arg("--ignore-rust-version");

    // Forwards relevant CLI args (skips cargo, subcommand and pallet-verifier specific args).
    let mut skip_next = false;
    cmd.args(env::args().skip(2).filter(|arg| {
        let can_skip = (skip_next && !arg.starts_with('-'))
            || arg == ARG_POINTER_WIDTH
            || arg.starts_with(ARG_POINTER_WIDTH)
            || arg == ARG_ALLOW_HOOK_PANICS
            || arg.starts_with(ARG_ALLOW_HOOK_PANICS);
        skip_next = arg == ARG_POINTER_WIDTH || arg == ARG_ALLOW_HOOK_PANICS;
        !can_skip
    }));

    // Track `--allow-hook-panics` arg.
    if cli_utils::has_arg(ARG_ALLOW_HOOK_PANICS) {
        if let Some(arg_value) = cli_utils::arg_value(ARG_ALLOW_HOOK_PANICS) {
            env::set_var(ENV_ALLOW_HOOK_PANICS, arg_value);
        } else {
            eprintln!(
                "{}: Missing value(s) for `{ARG_ALLOW_HOOK_PANICS}` arg.\
                \n  Accepts a comma separated list from: {}",
                "error".red().bold(),
                HOOKS.map(|name| format!("`{name}`")).join(", "),
            );
            exit(1);
        }
    }

    // Executes command (exits on failure).
    cli_utils::exec_cmd(&mut cmd);
}

/// Calls `pallet-verifier`.
fn call_pallet_verifier(
    args: impl Iterator<Item = String>,
    vars: impl Iterator<Item = (String, String)>,
    include_annotations: bool,
) {
    // Builds `pallet-verifier` command (specifically for the standalone executable).
    let mut path = env::current_exe()
        .expect("Expected valid executable path")
        .with_file_name("pallet-verifier");
    if cfg!(target_os = "windows") {
        path.set_extension("exe");
    }
    let mut cmd = Command::new(path);
    cmd.args(args);
    cmd.envs(vars);

    // Add `mirai-annotations` crate as a dependency (if necessary).
    // Ref: <https://doc.rust-lang.org/rustc/command-line-arguments.html#--extern-specify-where-an-external-library-is-located>
    if include_annotations && !cli_utils::has_mirai_annotations_dep() {
        let annotations_env_name = match cli_utils::arg_value("--target") {
            Some(_) => ENV_ANNOTATIONS_RLIB_PATH_TARGET,
            None => ENV_ANNOTATIONS_RLIB_PATH_HOST,
        };
        let annotations_rlib_path = env::var(annotations_env_name)
            .expect("Expected a path to `mirai-annotations` compiled artifact");
        cmd.args([
            "--extern".to_owned(),
            format!("mirai_annotations={annotations_rlib_path}"),
            format!("{ARG_AUTO_ANNOTATIONS_DEP}=true"),
        ]);
    }

    // Explicitly sets dynamic/shared library path to match the compile time value.
    let mut add_dy_lib_path = |dylib_path: &str| {
        cmd.env("LD_LIBRARY_PATH", dylib_path);
        if cfg!(target_os = "macos") {
            // Ref: <https://developer.apple.com/library/archive/documentation/DeveloperTools/Conceptual/DynamicLibraries/100-Articles/DynamicLibraryUsageGuidelines.html>
            cmd.env("DYLD_LIBRARY_PATH", dylib_path);
        }
    };
    if let Some(dl_path) =
        option_env!("LD_LIBRARY_PATH").or_else(|| option_env!("DYLD_LIBRARY_PATH"))
    {
        add_dy_lib_path(dl_path);
    } else {
        // Composes path from sysroot.
        let rustc_path = env::args()
            .nth(1)
            .filter(|arg| cli_utils::is_rustc_path(arg));
        let mut sys_root_cmd = cli_utils::rustc(rustc_path, ["--print", "sysroot"]);
        if let Some(toolchain) = option_env!("RUSTUP_TOOLCHAIN") {
            sys_root_cmd.env("RUSTUP_TOOLCHAIN", toolchain);
        }
        if let Some(out) = sys_root_cmd
            .output()
            .ok()
            .filter(|out| out.status.success())
        {
            let sys_root_path = Path::new(String::from_utf8_lossy(&out.stdout).trim()).join("lib");
            add_dy_lib_path(&sys_root_path.to_string_lossy());
        }
    }

    // Adds `--allow-hook-panics` arg from env (if any).
    if let Ok(arg_value) = env::var(ENV_ALLOW_HOOK_PANICS) {
        cmd.arg(ARG_ALLOW_HOOK_PANICS);
        cmd.arg(arg_value);
    }

    // Executes command (exits on failure).
    cli_utils::exec_cmd(&mut cmd);
}

/// Compiles dependencies.
fn compile_dependency(rustc_path: String, args: impl Iterator<Item = String>) {
    let is_wasm = is_wasm_target();
    let crate_name = cli_utils::arg_value("--crate-name");
    if is_wasm && is_wasmtime_package() {
        // Don't compile `wasmtime` (and related `wasmtime-*` packages) for `wasm` targets.
        exit(0);
    } else if is_wasm
        && crate_name
            .as_ref()
            .is_some_and(|crate_name| crate_name.starts_with("sp_wasm_interface"))
    {
        // Removes `wasmtime` dependency and feature from `sp-wasm-interface` package.
        let mut skip_next = false;
        let args = args.enumerate().filter_map(|(idx, arg)| {
            if skip_next {
                skip_next = false;
                return None;
            }

            // +3 because `args` iterator skipped 2 args and we're using the original `env::args`.
            let next_arg = || env::args().nth(idx + 3);

            // Removes `wasmtime` feature flag.
            if arg == "--cfg" || arg.starts_with("--cfg=") {
                let is_wasmtime_feature_flag =
                    |val: &str| val.contains("feature=") && val.contains("wasmtime");
                if arg
                    .strip_prefix("--cfg=")
                    .is_some_and(is_wasmtime_feature_flag)
                {
                    return None;
                }
                if next_arg().as_deref().is_some_and(is_wasmtime_feature_flag) {
                    skip_next = true;
                    return None;
                }
            }

            // Removes `wasmtime` dependency arg.
            if arg == "--extern" || arg.starts_with("--extern=") {
                let is_wasmtime_extern_flag = |val: &str| val.contains("wasmtime=");
                if arg
                    .strip_prefix("--extern=")
                    .is_some_and(is_wasmtime_extern_flag)
                {
                    return None;
                }
                if next_arg().as_deref().is_some_and(is_wasmtime_extern_flag) {
                    skip_next = true;
                    return None;
                }
            }

            Some(arg)
        });
        cli_utils::call_rustc(Some(rustc_path), args);
    } else if crate_name
        .as_ref()
        .is_some_and(|crate_name| crate_name.starts_with("serde"))
    {
        // TODO: Remove `--cfg no_diagnostic_namespace` when compiler is updated to >= nightly-2024-05-03
        // Ref: <https://blog.rust-lang.org/2024/05/02/Rust-1.78.0.html#diagnostic-attributes>
        // Ref: <https://github.com/serde-rs/serde/commit/694fe0595358aa0857120a99041d99975b1a8a70#diff-be34659e38d3b07b2dad53cae7b6a6a00860685171d703b524deb72c10d3f4e7R92>
        cli_utils::call_rustc(
            Some(rustc_path),
            args.chain(["--cfg=no_diagnostic_namespace".to_string()]),
        );
    } else if crate_name.as_ref().is_some_and(|crate_name| {
        crate_name.starts_with("pallet") && !is_unsupported_annotation_target()
    }) {
        // Compiles and annotates `pallet` dependencies with `pallet-verifier`.
        call_pallet_verifier(
            args.chain([ARG_DEP_ANNOTATE, "true"].map(ToString::to_string)),
            std::iter::empty(),
            true,
        );
    } else if crate_name
        .as_ref()
        .is_some_and(|crate_name| cli_utils::requires_unstable_features(crate_name))
    {
        // Compiles dependencies that require unstable features with `pallet-verifier`.
        call_pallet_verifier(
            args.chain([ARG_DEP_FEATURES, "true"].map(ToString::to_string)),
            std::iter::empty(),
            false,
        );
    } else {
        // Compiles dependencies with `rustc`.
        cli_utils::call_rustc(Some(rustc_path), args);
    }
}

/// Compiles build scripts.
fn compile_build_script(rustc_path: String, args: impl Iterator<Item = String>) {
    if is_wasm_target() && is_wasmtime_package() {
        // Compiles `wasmtime` build scripts (and those of related `wasmtime-*` packages) as no-op binaries.
        let out_dir = cli_utils::arg_value("--out-dir").expect("Expected an output directory arg");
        let dummy_build_file = Path::new(&out_dir).join("build.rs");
        fs::write(&dummy_build_file, "fn main() {}").expect("Failed to create dummy build file");
        cli_utils::call_rustc(
            Some(rustc_path),
            args.map(|arg| {
                if arg.ends_with("/build.rs") {
                    dummy_build_file.to_string_lossy().to_string()
                } else {
                    arg
                }
            }),
        );
    } else {
        // Compiles build scripts with `rustc`.
        cli_utils::call_rustc(Some(rustc_path), args);
    }
}

/// Checks if current compilation target is a build script.
fn is_build_script() -> bool {
    // First `*.rs` CLI argument should be a `build.rs` file
    // and `--crate-name` arg should be `build_script_build`.
    env::args().any(|arg| {
        Path::new(&arg)
            .file_name()
            .is_some_and(|name| name == "build.rs")
    }) && cli_utils::arg_value("--crate-name")
        .is_some_and(|crate_name| crate_name == "build_script_build")
}

/// Checks if the `rustc` target (if any) is wasm.
fn is_wasm_target() -> bool {
    cli_utils::arg_value("--target")
        .or(env::var(ENV_TARGET).ok())
        .is_some_and(|target| target.starts_with("wasm"))
}

/// Checks if the current `cargo` package is the `wastime`.
fn is_wasmtime_package() -> bool {
    env::var("CARGO_PKG_NAME").is_ok_and(|name| name.starts_with("wasmtime"))
}

/// Creates an output directory for dependencies inside the given target directory.
fn create_deps_out_dir(target_dir: &Path) -> PathBuf {
    let out_dir = target_dir.join("debug/deps");
    if !out_dir.exists() {
        fs::create_dir_all(&out_dir).expect("Failed to create output directory for annotations");
    }
    out_dir
}

/// Checks if the `rustc` target (if set) is a target that is NOT supported for annotations.
///
/// This typically happens when a build script manually compiles an artifact and explicitly
/// sets a `rustc` target that doesn't match the compilation target set by `pallet-verifier`
/// (e.g. see build script for `pallet-contracts-fixtures`).
fn is_unsupported_annotation_target() -> bool {
    cli_utils::arg_value("--target").is_some_and(|target| {
        let pallet_verifier_target = env::var(ENV_TARGET);
        pallet_verifier_target.is_err()
            || pallet_verifier_target.is_ok_and(|pv_target| pv_target != target)
    })
}
