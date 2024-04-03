//! # pallet-verifier
//!
//! pallet-verifier is a tool for detecting [common security vulnerabilities][vulnerabilities] and
//! [insecure patterns] in [FRAME pallets][FRAME] using [static program analysis][static-analysis]
//! techniques like [data-flow analysis][data-flow], [abstract interpretation][abs-int] and
//! [symbolic execution][symbex].
//!
//! [FRAME]: https://docs.substrate.io/learn/runtime-development/#frame
//! [Substrate]: https://docs.substrate.io/
//! [vulnerabilities]: https://secure-contracts.com/not-so-smart-contracts/substrate/
//! [insecure patterns]: https://docs.substrate.io/build/troubleshoot-your-code/#unsafe-or-insecure-patterns
//! [static-analysis]: https://en.wikipedia.org/wiki/Static_program_analysis
//! [data-flow]: https://en.wikipedia.org/wiki/Data-flow_analysis
//! [abs-int]: https://en.wikipedia.org/wiki/Abstract_interpretation
//! [symbex]: https://en.wikipedia.org/wiki/Symbolic_execution

#![feature(rustc_private)]
#![feature(new_uninit)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod callbacks;
mod file_loader;

use std::{env, path::Path, process};

use callbacks::{EntryPointCallbacks, VerifierCallbacks};
use file_loader::EntryPointFileLoader;

fn main() {
    // `rustc` ignores the first argument, so we set that to "pallet-verifier".
    let command = "pallet-verifier";

    // Reads the crate root from CLI args.
    let target_path_str = env::args()
        .nth(1)
        .expect("Expected target path as the first argument");
    let target_path = Path::new(&target_path_str).to_path_buf();

    // Generates tractable entry points for FRAME pallet.
    let entry_point_args = [
        command.to_owned(),
        target_path_str.clone(),
        // Enables dumping MIR for all functions.
        "-Zalways-encode-mir".to_owned(),
    ];
    let mut entry_point_callbacks = EntryPointCallbacks::new();
    let entry_point_compiler =
        rustc_driver::RunCompiler::new(&entry_point_args, &mut entry_point_callbacks);
    let entry_point_result = entry_point_compiler.run();
    if entry_point_result.is_err() {
        process::exit(rustc_driver::EXIT_FAILURE);
    }
    let Some(entry_point_content) = entry_point_callbacks.entry_point_content else {
        process::exit(rustc_driver::EXIT_FAILURE);
    };

    // Initializes `FileLoader`.
    let entry_point_file_loader =
        EntryPointFileLoader::new(target_path, entry_point_content.to_owned());

    // Analyzes FRAME pallet with MIRAI.
    let verifier_args = [
        command.to_owned(),
        target_path_str,
        // Enables compilation of MIRAI only code.
        "--cfg=mirai".to_owned(),
        // Enables dumping MIR for all functions.
        "-Zalways-encode-mir".to_owned(),
    ];
    let mut verifier_callbacks = VerifierCallbacks::new();
    let mut verifier_compiler =
        rustc_driver::RunCompiler::new(&verifier_args, &mut verifier_callbacks);
    verifier_compiler.set_file_loader(Some(Box::new(entry_point_file_loader)));
    let verifier_result = verifier_compiler.run();

    let exit_code = match verifier_result {
        Ok(_) => rustc_driver::EXIT_SUCCESS,
        Err(_) => rustc_driver::EXIT_FAILURE,
    };
    process::exit(exit_code);
}
