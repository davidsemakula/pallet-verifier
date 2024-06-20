//! Implementation of `rustc` driver for `pallet-verifier`.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hash;
extern crate rustc_session;

mod cli_utils;

use std::{env, path::Path, process};

use pallet_verifier::{
    DefaultCallbacks, EntryPointsCallbacks, VerifierCallbacks, VirtualFileLoader,
    CONTRACTS_MOD_NAME, ENTRY_POINTS_MOD_NAME,
};

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

    // Compiles `mirai-annotations` crate and adds it as a dependency (if necessary).
    let has_mirai_annotations_dep = cli_args.iter().enumerate().any(|(idx, arg)| {
        arg.starts_with("mirai_annotations")
            && cli_args.get(idx - 1).is_some_and(|arg| arg == "--extern")
    });
    if !has_mirai_annotations_dep {
        let mut annotations_path = env::current_dir().expect("Expected valid current dir");
        annotations_path.push("__pallet_verifier_artifacts/mirai_annotations/src/lib.rs");
        let out_dir = cli_args
            .iter()
            .enumerate()
            .find_map(|(idx, arg)| {
                if arg == "--out-dir" {
                    cli_args
                        .get(idx + 1)
                        .map(|arg| Path::new(arg).to_path_buf())
                } else {
                    None
                }
            })
            .unwrap_or_else(|| {
                let mut target_dir = env::current_dir().expect("Expected valid current dir");
                target_dir.push("target/debug/deps");
                target_dir
            });
        let mut annotations_out_file = Path::new(&out_dir).to_path_buf();
        annotations_out_file.push("libmirai_annotations.rlib");
        let annotations_out_file_str = annotations_out_file.to_string_lossy();
        let annotations_args = [
            // NOTE: `rustc` ignores the first argument, so we set that to "pallet-verifier".
            "pallet-verifier".to_owned(),
            "--crate-name=mirai_annotations".to_owned(),
            "--edition=2021".to_owned(),
            annotations_path.to_string_lossy().to_string(),
            "--crate-type=lib".to_owned(),
            "--emit=link".to_owned(),
            "-o".to_owned(),
            annotations_out_file_str.to_string(),
            "--cfg=mirai".to_owned(),
            "-Zalways_encode_mir".to_owned(),
        ];
        let mut rustc_callbacks = DefaultCallbacks;
        let annotations_file_loader = VirtualFileLoader::new(
            annotations_path,
            Some(include_str!("../artifacts/mirai_annotations.rs").to_owned()),
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
            "--extern".to_owned(),
            format!("mirai_annotations={annotations_out_file_str}"),
        ]);
    }

    // Initializes "virtual" `FileLoader` for entry point and "contracts" content.
    // Reads the analysis target path as the "normalized" first `*.rs` argument from CLI args.
    let target_path_str = cli_args
        .iter()
        .find(|arg| Path::new(arg).extension().is_some_and(|ext| ext == "rs"))
        .expect("Expected target path as the first `*.rs` argument");
    let target_path = Path::new(&target_path_str).to_path_buf();
    let verifier_file_loader = VirtualFileLoader::new(
        target_path,
        None,
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
    let entry_point_names = entry_point_callbacks.entry_point_names();
    let mut verifier_callbacks = VerifierCallbacks::new(&entry_point_names);
    let mut verifier_compiler = rustc_driver::RunCompiler::new(&cli_args, &mut verifier_callbacks);
    verifier_compiler.set_file_loader(Some(Box::new(verifier_file_loader)));
    let verifier_result = verifier_compiler.run();

    let exit_code = match verifier_result {
        Ok(_) => rustc_driver::EXIT_SUCCESS,
        Err(_) => rustc_driver::EXIT_FAILURE,
    };
    process::exit(exit_code);
}
