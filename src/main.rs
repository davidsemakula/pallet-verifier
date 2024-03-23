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

use std::{env, process};

use callbacks::EntryPointCallbacks;

fn main() {
    // `rustc` ignores the first argument, so we set that to "pallet-verifier".
    let command = "pallet-verifier";

    // Reads the crate root from CLI args.
    let target_path = env::args()
        .nth(1)
        .expect("Expected target path as the first argument");

    // Generates tractable entry points for FRAME pallet.
    let args = [
        command.to_owned(),
        target_path,
        // Enables dumping MIR for all functions.
        "-Zalways-encode-mir".to_owned(),
    ];
    let mut callbacks = EntryPointCallbacks::new();
    let compiler = rustc_driver::RunCompiler::new(&args, &mut callbacks);
    let result = compiler.run();
    if result.is_err() || callbacks.entry_point_content.is_none() {
        process::exit(rustc_driver::EXIT_FAILURE);
    }
    process::exit(rustc_driver::EXIT_FAILURE);
}
