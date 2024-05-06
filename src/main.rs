//! Implementation of `cargo verify-pallet` subcommand for `pallet-verifier`.

mod cli_utils;

use std::{
    env,
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
        // Calls `pallet-verifier` for the "primary" package, and `rustc` for dependencies.
        // NOTE: Handles `cargo rustc` since `pallet-verifier` (specifically this cargo subcommand) is set as `RUSTC_WRAPPER`.
        // Ref: <https://doc.rust-lang.org/cargo/reference/environment-variables.html#environment-variables-cargo-reads>
        command if cli_utils::is_rustc_path(command) => {
            let is_primary_package = env::var("CARGO_PRIMARY_PACKAGE").is_ok();
            if is_primary_package {
                // Analyzes "primary" package with `pallet-verifier`.
                call_pallet_verifier();
            } else {
                // Compiles dependencies with `rustc`.
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
    let mut cmd = Command::new(env::var("CARGO").unwrap_or_else(|_| "cargo".into()));
    cmd.arg("check");

    // Sets `RUSTC_WRAPPER` to `pallet-verifier` (specifically this cargo subcommand).
    let path = env::current_exe().expect("Expected valid executable path");
    cmd.env("RUSTC_WRAPPER", path);

    // Enables compilation of MIRAI-only code, and dumping MIR for all functions (for dependencies).
    cmd.env("RUSTFLAGS", "--cfg=mirai -Zalways_encode_mir");

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
    if cfg!(windows) {
        path.set_extension("exe");
    }
    let mut cmd = Command::new(path);
    cmd.args(env::args().skip(2));

    // Executes command (exits on failure).
    cli_utils::exec_cmd(&mut cmd);
}
