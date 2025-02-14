//! `rustc` `MirPass` for adding custom annotations.
//!
//! [MIRAI-annotations]: https://crates.io/crates/mirai-annotations

mod int_cast_overflow;
mod iterator_invariants;
mod slice_invariants;

use rustc_middle::{mir::Body, ty::TyCtxt};

pub use int_cast_overflow::IntCastOverflowChecks;
pub use iterator_invariants::IteratorInvariants;
pub use slice_invariants::SliceInvariants;

/// Minimal copy of `rustc_mir_transform::pass_manager::MirPass` for a uniform interface for running MIR passes.
///
/// Ref: <https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_transform/pass_manager/trait.MirPass.html>
pub(crate) trait MirPass<'tcx> {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>);
}
