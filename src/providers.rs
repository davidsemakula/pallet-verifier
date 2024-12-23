//! `rustc` providers for overriding queries.

mod annotate;
mod passes;
mod traverse;

use rustc_middle::{
    mir::{Body, MirPass},
    query,
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;

use passes::{IntCastOverflowChecks, IteratorInvariants, SliceInvariants};

/// Overrides the `optimized_mir` query.
pub fn optimized_mir(tcx: TyCtxt<'_>, did: LocalDefId) -> &Body<'_> {
    let mut providers = query::Providers::default();
    rustc_mir_transform::provide(&mut providers);
    let mut body = (providers.optimized_mir)(tcx, did).clone();

    let passes: [&dyn MirPass; 3] = [
        &IntCastOverflowChecks,
        &IteratorInvariants,
        &SliceInvariants,
    ];
    for pass in passes {
        pass.run_pass(tcx, &mut body);
    }

    tcx.arena.alloc(body)
}
