//! Common analysis utilities.

use rustc_hir::definitions::{DefPathData, DisambiguatedDefPathData};
use rustc_middle::ty::TyCtxt;
use rustc_span::{def_id::LocalDefId, Symbol};

/// Returns the name of the `LocalDefId` as a `Symbol` (if any).
pub fn def_name(local_def_id: LocalDefId, tcx: TyCtxt<'_>) -> Option<Symbol> {
    let def_path = tcx.hir().def_path(local_def_id);
    let def_path_data = def_path.data.last()?;
    match def_path_data {
        DisambiguatedDefPathData {
            data:
                DefPathData::MacroNs(name)
                | DefPathData::LifetimeNs(name)
                | DefPathData::TypeNs(name)
                | DefPathData::ValueNs(name),
            ..
        } => Some(*name),
        _ => None,
    }
}
