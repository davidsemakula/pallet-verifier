//! `rustc` providers for overriding queries.

mod int_cast_overflow;
mod iterator_annotations;

use rustc_middle::{
    mir::{Body, MirPass},
    query,
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;

use self::int_cast_overflow::IntCastOverflowChecks;
use self::iterator_annotations::IteratorAnnotations;

/// Overrides the `optimized_mir` query.
pub fn optimized_mir(tcx: TyCtxt<'_>, did: LocalDefId) -> &Body<'_> {
    let mut providers = query::Providers::default();
    rustc_mir_transform::provide(&mut providers);
    let mut body = (providers.optimized_mir)(tcx, did).clone();

    let passes: [&dyn MirPass; 2] = [&IntCastOverflowChecks, &IteratorAnnotations];
    for pass in passes {
        pass.run_pass(tcx, &mut body);
    }

    tcx.arena.alloc(body)
}
