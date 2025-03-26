//! `rustc` callbacks for analyzing FRAME pallets.

mod entry_points;
mod summaries;
mod verifier;

pub use {
    entry_points::EntryPointsCallbacks, summaries::SummariesCallbacks, verifier::VerifierCallbacks,
};

use rustc_middle::query;

use crate::providers;

/// `rustc` Default callbacks.
pub struct DefaultCallbacks;

impl rustc_driver::Callbacks for DefaultCallbacks {}

/// `rustc` callbacks for annotating dependencies.
pub struct DependencyCallbacks;

impl rustc_driver::Callbacks for DependencyCallbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        // Overrides `optimized_mir` query.
        config.override_queries = Some(|_, providers| {
            providers.queries = query::Providers {
                optimized_mir: providers::optimized_mir,
                ..providers.queries
            };
        });
    }
}
