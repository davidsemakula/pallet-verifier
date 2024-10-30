//! Implementation of `cargo verify-pallet` subcommand for `pallet-verifier`.

mod cli_utils;

use std::{
    env,
    path::{Path, PathBuf},
    process::{self, Command},
};

use cli_utils::{ENV_DEP_CRATE, ENV_DEP_RENAMES};

const COMMAND: &str = "cargo verify-pallet";
const ARG_POINTER_WIDTH: &str = "--pointer-width";

/// Env var set to the name of the top-level package being analyzed
/// (i.e. the package name in the `Cargo.toml` in the directory where `cargo verify-pallet`) is invoked.
const ENV_PKG_NAME: &str = "PALLET_VERIFIER_PKG_NAME";
/// Env var set to the name current `rustc` target (if set).
/// Ref: <https://doc.rust-lang.org/rustc/targets/index.html>
const ENV_TARGET: &str = "PALLET_VERIFIER_TARGET";

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
            let args = env::args().skip(2);
            if is_primary_package && is_analysis_target() && !is_build_script() {
                // Analyzes "primary" package with `pallet-verifier`.
                call_pallet_verifier(args, std::iter::empty());
            } else if is_build_script() {
                // Compiles build scripts.
                compile_build_script(sub_command, args);
            } else {
                // Compiles dependencies.
                compile_dependency(sub_command, args);
            }
        }
        _ => {
            eprintln!("Expected a valid cargo subcommand as the first argument.");
            process::exit(1);
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
            eprintln!("Expected a valid `--pointer-width=32|64`");
            process::exit(1);
        }
    };
    if pointer_width == 32 && cfg!(not(target_pointer_width = "32")) {
        cmd.arg("--target=wasm32-wasi");
        cmd.env(ENV_TARGET, "wasm32-wasi");
    } else if pointer_width == 64 && cfg!(not(target_pointer_width = "64")) {
        eprintln!("Unsupported host for 64-bit analysis");
        process::exit(1);
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

    // Sets cargo `--target-dir` arg if it's not already set.
    if cli_utils::arg_value("--target-dir").is_none()
        && env::var("CARGO_TARGET_DIR").is_err()
        && env::var("CARGO_BUILD_TARGET_DIR").is_err()
    {
        let target_dir = metadata
            .as_ref()
            .map(|metadata| metadata.target_directory.as_str())
            .unwrap_or("target");
        cmd.arg(format!("--target-dir={target_dir}/pallet_verifier"));
    }

    // Persists some package metadata.
    let root_package = metadata
        .as_ref()
        .ok()
        .and_then(|metadata| metadata.root_package());
    if let Some(root_package) = root_package {
        cmd.args(["-p", &root_package.name]);
        cmd.env(ENV_PKG_NAME, &root_package.name);

        let dep_renames: std::collections::HashMap<_, _> = root_package
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
    }

    // Forwards relevant CLI args (skips cargo, subcommand and pallet-verifier specific args).
    let mut skip_next = false;
    cmd.args(env::args().skip(2).filter(|arg| {
        let can_skip = skip_next || arg == ARG_POINTER_WIDTH || arg.starts_with(ARG_POINTER_WIDTH);
        skip_next = arg == ARG_POINTER_WIDTH;
        !can_skip
    }));

    // Executes command (exits on failure).
    cli_utils::exec_cmd(&mut cmd);
}

/// Calls `pallet-verifier`.
fn call_pallet_verifier(
    args: impl Iterator<Item = String>,
    vars: impl Iterator<Item = (String, String)>,
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

    // Explicitly sets dynamic/shared library path to match `pallet-verifier`.
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
        let mut sys_root_cmd = cli_utils::rustc(env::args().nth(1), ["--print", "sysroot"]);
        if let Some(out) = sys_root_cmd
            .output()
            .ok()
            .filter(|out| out.status.success())
        {
            let mut sys_root_path = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
            sys_root_path.push("lib");
            add_dy_lib_path(&sys_root_path.to_string_lossy());
        }
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
        process::exit(0);
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
    } else if let Some(dep_name) = crate_name
        .as_ref()
        .filter(|crate_name| crate_name.starts_with("pallet"))
    {
        // Compiles `pallet` dependencies with `pallet-verifier`.
        // The `PALLET_VERIFIER_DEP_CRATE` env var tells `pallet-verifier` that this a dependency.
        if env::var("PALLET_VERIFIER_UI_TESTS").is_err() {
            let vars = [(ENV_DEP_CRATE.to_string(), dep_name.to_owned())];
            call_pallet_verifier(args, vars.into_iter());
        } else {
            // TODO: Disable this option when UI tests play nicely with this config.
            cli_utils::call_rustc(Some(rustc_path), args);
        }
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
        std::fs::write(&dummy_build_file, "fn main() {}")
            .expect("Failed to create dummy build file");
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
