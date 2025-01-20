//! `rustc` providers for overriding queries.

mod analyze;
mod annotate;
mod passes;
mod storage;

use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{Body, MirPass},
    query,
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;

use passes::{IntCastOverflowChecks, IteratorInvariants, SliceInvariants};

/// Overrides the `optimized_mir` query.
pub fn optimized_mir(tcx: TyCtxt<'_>, did: LocalDefId) -> &Body<'_> {
    // Runs default optimized MIR query.
    let mut providers = query::Providers::default();
    rustc_mir_transform::provide(&mut providers);
    let mut body = (providers.optimized_mir)(tcx, did).clone();

    // Runs custom MIR passes.
    let passes: [&dyn MirPass; 3] = [
        &IntCastOverflowChecks,
        &IteratorInvariants,
        &SliceInvariants,
    ];
    for pass in passes {
        pass.run_pass(tcx, &mut body);
    }

    // Applies propagated storage invariants (if any) for closure.
    if let DefKind::Closure = tcx.def_kind(did) {
        if let Some(closure_invariant_env) =
            storage::find_closure_invariant_env(did.to_def_id(), tcx)
        {
            storage::apply_propagated_closure_invariants(
                did.to_def_id(),
                closure_invariant_env,
                &mut body,
                tcx,
            );
        }
    }

    tcx.arena.alloc(body)
}
