//! `rustc` callbacks for analyzing FRAME pallets.

mod entry_point;
mod utils;
mod verifier;

pub use {entry_point::EntryPointCallbacks, verifier::VerifierCallbacks};
