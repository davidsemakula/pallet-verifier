//! Implementation of `rustc` driver for `pallet-verifier`.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hash;
extern crate rustc_session;

mod cli_utils;

use std::{env, path::Path, process};

use pallet_verifier::{EntryPointsCallbacks, VerifierCallbacks, VirtualFileLoader};

const COMMAND: &str = "pallet-verifier";

fn main() {
    // Initialize loggers.
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

    // Retrieve command line arguments.
    let mut cli_args: Vec<_> = env::args().collect();
    // Setting `RUSTC_WRAPPER` causes Cargo to pass 'rustc' as the first argument.
    // We're invoking the compiler programmatically, so we remove it (if present).
    // Ref: <https://doc.rust-lang.org/cargo/reference/environment-variables.html#environment-variables-cargo-reads>
    // Ref: <https://github.com/rust-lang/rust-clippy/blob/caad063933e5012b152d883a6c03f1d0ad5ec6a8/src/driver.rs#L244-L251>
    let is_rustc_wrapper_mode = cli_args
        .get(1)
        .is_some_and(|arg| cli_utils::is_rustc_path(arg));
    if is_rustc_wrapper_mode {
        cli_args.remove(1);
    }
    if env::var("CARGO_PKG_NAME").is_err() || env::var("CARGO_PRIMARY_PACKAGE").is_err() {
        // Presumably, this is some kind of direct call to the `pallet-verifier` binary,
        // instead of via `cargo verify-pallet`, so we need to set some extra flags.
        cli_args.extend([
            // Enables compilation of unit tests and test harness generation.
            "--test".to_owned(),
            // Enables dumping MIR for all functions.
            "-Zalways-encode-mir".to_owned(),
        ]);
    }

    // Generates tractable entry points for FRAME pallet.
    let mut entry_point_callbacks = EntryPointsCallbacks::default();
    let entry_point_compiler =
        rustc_driver::RunCompiler::new(&cli_args, &mut entry_point_callbacks);
    let entry_point_result = entry_point_compiler.run();
    if entry_point_result.is_err() {
        process::exit(rustc_driver::EXIT_FAILURE);
    }
    let Some(entry_points_content) = entry_point_callbacks.entry_points_content() else {
        process::exit(rustc_driver::EXIT_FAILURE);
    };
    let contracts = entry_point_callbacks.contracts();

    // Initializes "virtual" `FileLoader` for entry point and "contracts" content.
    // Reads the analysis target path as the "normalized" first `*.rs` argument from CLI args.
    let target_path_str = cli_args
        .iter()
        .find(|arg| Path::new(arg).extension().is_some_and(|ext| ext == "rs"))
        .expect("Expected target path as the first `*.rs` argument");
    let target_path = Path::new(&target_path_str).to_path_buf();
    let virtual_file_loader = VirtualFileLoader::new(
        target_path,
        entry_points_content.to_owned(),
        contracts.map(ToString::to_string),
    );

    // Analyzes FRAME pallet with MIRAI.
    // Enables compilation of MIRAI only code.
    cli_args.push("--cfg=mirai".to_owned());
    let entry_point_names = entry_point_callbacks.entry_point_names();
    let mut verifier_callbacks = VerifierCallbacks::new(&entry_point_names);
    let mut verifier_compiler = rustc_driver::RunCompiler::new(&cli_args, &mut verifier_callbacks);
    verifier_compiler.set_file_loader(Some(Box::new(virtual_file_loader)));
    let verifier_result = verifier_compiler.run();

    let exit_code = match verifier_result {
        Ok(_) => rustc_driver::EXIT_SUCCESS,
        Err(_) => rustc_driver::EXIT_FAILURE,
    };
    process::exit(exit_code);
}
