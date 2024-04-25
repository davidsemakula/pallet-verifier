//! Implementation of `cargo verify-pallet` subcommand for `pallet-verifier`.

mod cli_utils;

use std::{
    env,
    path::PathBuf,
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
        // Calls `cargo` with `pallet-verifier` set as `RUSTC_WRAPPER`.
        "verify-pallet" => call_cargo(),
        // Calls `pallet-verifier` for the "primary" package, and `rustc` for dependencies.
        "rustc" => {
            let is_primary_package = env::var("CARGO_PRIMARY_PACKAGE").is_ok();
            if is_primary_package {
                // Analyzes "primary" package with `pallet-verifier`.
                call_pallet_verifier();
            } else {
                // Compiles dependencies with `rustc`.
                call_rustc();
            }
        }
        _ => {
            eprintln!("Expected a valid cargo subcommand as the first argument.");
            process::exit(1);
        }
    }
}

/// Calls `cargo` with `pallet-verifier` set as `RUSTC_WRAPPER`.
fn call_cargo() {
    // Builds cargo command.
    let mut cmd = Command::new(env::var("CARGO").unwrap_or_else(|_| "cargo".into()));
    cmd.arg("check");

    // Sets `RUSTC_WRAPPER` to pallet-verifier.
    let path = pallet_verifier_path().expect("Expected valid executable path");
    cmd.env("RUSTC_WRAPPER", path);

    // Enables compilation of MIRAI-only code, and dumping MIR for all functions (for dependencies).
    cmd.env("RUSTFLAGS", "--cfg=mirai -Zalways_encode_mir");

    // Forwards relevant CLI args (skips cargo and subcommand args).
    cmd.args(env::args().skip(2));

    // Executes command (exits on failure).
    exec_cmd(&mut cmd);
}

/// Calls `rustc`.
fn call_rustc() {
    // Builds `rustc` command.
    let mut cmd = Command::new(std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into()));
    cmd.args(env::args().skip(2));

    // Executes command (exits on failure).
    exec_cmd(&mut cmd);
}

/// Calls `pallet-verifier`.
fn call_pallet_verifier() {
    // Builds `pallet-verifier` command.
    let path = pallet_verifier_path().expect("Expected valid executable path");
    let mut cmd = Command::new(path);
    cmd.args(env::args().skip(2));

    // Executes command (exits on failure).
    exec_cmd(&mut cmd);
}

// Returns the path for the `pallet-verifier` executable.
fn pallet_verifier_path() -> Result<PathBuf, std::io::Error> {
    let mut path = env::current_exe()?.with_file_name("pallet-verifier");
    if cfg!(windows) {
        path.set_extension("exe");
    }
    Ok(path)
}

// Executes command (exits on failure).
fn exec_cmd(cmd: &mut Command) {
    let exit_status = cmd
        .spawn()
        .expect("Failed to run cmd")
        .wait()
        .expect("Failed to wait for cmd");
    if !exit_status.success() {
        process::exit(exit_status.code().unwrap_or(-1));
    }
}
