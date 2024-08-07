//! Implementation of `cargo verify-pallet` subcommand for `pallet-verifier`.

mod cli_utils;

use std::{
    env,
    path::Path,
    process::{self, Command},
};

const COMMAND: &str = "cargo verify-pallet";

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
            // Checks whether the current target is a build script.
            let is_build_script = || {
                // First `*.rs` CLI argument should be a `build.rs` file.
                env::args().any(|arg| {
                    Path::new(&arg)
                        .file_name()
                        .is_some_and(|ext| ext == "build.rs")
                }) &&
                // `--crate-name` arg should be `build_script_build`.
                env::args().enumerate().any(|(idx, arg)| {
                    arg == "build_script_build"
                        && idx > 0
                        && env::args()
                            .nth(idx - 1)
                            .is_some_and(|arg| arg.ends_with("crate-name"))
                })
            };
            if is_primary_package && !is_build_script() {
                // Analyzes "primary" package with `pallet-verifier`.
                call_pallet_verifier();
            } else {
                // Compiles dependencies and build scripts with `rustc`.
                cli_utils::call_rustc(env::args().skip(2));
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
    cmd.env(
        "RUSTFLAGS",
        "-Zalways-encode-mir=yes -Cdebug-assertions=no -Coverflow-checks=yes",
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
