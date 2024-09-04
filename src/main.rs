//! Implementation of `cargo verify-pallet` subcommand for `pallet-verifier`.

mod cli_utils;

use std::{
    env,
    path::Path,
    process::{self, Command},
};

use cli_utils::ENV_DEP_RENAMES;

const COMMAND: &str = "cargo verify-pallet";
const ENV_PKG_NAME: &str = "PALLET_VERIFIER_PKG_NAME";

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
            // Checks whether the current target is a build script.
            let is_build_script = || {
                // First `*.rs` CLI argument should be a `build.rs` file
                // and `--crate-name` arg should be `build_script_build`.
                env::args().any(|arg| {
                    Path::new(&arg)
                        .file_name()
                        .is_some_and(|ext| ext == "build.rs")
                }) && cli_utils::arg_value("--crate-name")
                    .is_some_and(|crate_name| crate_name == "build_script_build")
            };
            if is_primary_package && is_analysis_target() && !is_build_script() {
                // Analyzes "primary" package with `pallet-verifier`.
                call_pallet_verifier();
            } else {
                // Compiles dependencies and build scripts with `rustc`.
                let args = env::args().skip(2);
                if cli_utils::arg_value("--crate-name")
                    .is_some_and(|crate_name| crate_name.starts_with("serde"))
                {
                    // TODO: Remove `--cfg no_diagnostic_namespace` when compiler is updated to >= nightly-2024-05-03
                    // Ref: <https://blog.rust-lang.org/2024/05/02/Rust-1.78.0.html#diagnostic-attributes>
                    // Ref: <https://github.com/serde-rs/serde/commit/694fe0595358aa0857120a99041d99975b1a8a70#diff-be34659e38d3b07b2dad53cae7b6a6a00860685171d703b524deb72c10d3f4e7R92>
                    cli_utils::call_rustc(
                        args.chain(["--cfg", "no_diagnostic_namespace"].map(ToString::to_string)),
                    );
                } else {
                    cli_utils::call_rustc(args);
                }
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
    let mut cmd = Command::new(env::var("CARGO").unwrap_or_else(|_| "cargo".into()));
    cmd.arg("test");
    cmd.arg("--lib");
    cmd.arg("--no-run");

    // Persists some crate metadata.
    let mut metadata_cmd = cargo_metadata::MetadataCommand::new();
    if let Some(manifest_path) = cli_utils::arg_value("--manifest-path") {
        metadata_cmd.manifest_path(manifest_path);
    }
    if let Ok(metadata) = metadata_cmd.exec() {
        if let Some(root_package) = metadata.root_package() {
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
    }

    // Sets `RUSTC_WRAPPER` to `pallet-verifier` (specifically this cargo subcommand).
    // Ref: <https://doc.rust-lang.org/cargo/reference/config.html#buildrustc-wrapper>
    let path = env::current_exe().expect("Expected valid executable path");
    cmd.env("RUSTC_WRAPPER", path);

    // Enables dumping MIR for all functions, and disables debug assertions, and enables overflow checks.
    // Ref: <https://doc.rust-lang.org/cargo/reference/config.html#buildrustflags>
    // Ref: <https://doc.rust-lang.org/rustc/command-line-arguments.html>
    // Ref: <https://github.com/rust-lang/rust/blob/master/compiler/rustc_session/src/options.rs#L1632>
    // Ref: <https://hackmd.io/@rust-compiler-team/r1JECK_76#metadata-and-depinfo>
    // Ref: <https://doc.rust-lang.org/rustc/codegen-options/index.html#debug-assertions>
    // Ref: <https://doc.rust-lang.org/rustc/codegen-options/index.html#overflow-checks>
    let flags = "-Zalways-encode-mir=yes -Cdebug-assertions=no -Coverflow-checks=yes";
    cmd.env(
        "RUSTFLAGS",
        env::var("RUSTFLAGS")
            .map(|var| format!("{var} {flags}"))
            .as_deref()
            .unwrap_or(flags),
    );

    // Explicitly set toolchain to match `pallet-verifier`.
    if let Some(toolchain) = option_env!("RUSTUP_TOOLCHAIN") {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain);
    }

    // Forwards relevant CLI args (skips cargo and subcommand args).
    cmd.args(env::args().skip(2));

    // Executes command (exits on failure).
    cli_utils::exec_cmd(&mut cmd);
}

/// Calls `pallet-verifier`.
fn call_pallet_verifier() {
    // Builds `pallet-verifier` command (specifically for the standalone executable).
    let mut path = env::current_exe()
        .expect("Expected valid executable path")
        .with_file_name("pallet-verifier");
    if cfg!(target_os = "windows") {
        path.set_extension("exe");
    }
    let mut cmd = Command::new(path);
    cmd.args(env::args().skip(2));

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
        let mut sys_root_cmd = cli_utils::rustc(["--print", "sysroot"]);
        if let Some(out) = sys_root_cmd
            .output()
            .ok()
            .filter(|out| out.status.success())
        {
            let mut sys_root_path =
                Path::new(String::from_utf8_lossy(&out.stdout).trim()).to_path_buf();
            sys_root_path.push("lib");
            add_dy_lib_path(&sys_root_path.to_string_lossy());
        }
    }

    // Executes command (exits on failure).
    cli_utils::exec_cmd(&mut cmd);
}
