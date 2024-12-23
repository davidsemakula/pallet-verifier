//! `rustc` `MirPass` for adding custom annotations.
//!
//! [MIRAI-annotations]: https://crates.io/crates/mirai-annotations

mod int_cast_overflow;
mod iterator_invariants;
mod slice_invariants;

pub use int_cast_overflow::IntCastOverflowChecks;
pub use iterator_invariants::IteratorInvariants;
pub use slice_invariants::SliceInvariants;
