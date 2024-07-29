//! Common analysis utilities.

use rustc_ast::NestedMetaItem;
use rustc_hir::{
    definitions::{DefPathData, DisambiguatedDefPathData},
    HirId,
};
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

/// Checks if an item (given it's `HirId`) "effectively" has a `#[cfg(test)]` attribute.
pub fn has_cfg_test_attr(hir_id: HirId, tcx: TyCtxt<'_>) -> bool {
    let attrs = tcx.hir().attrs(hir_id);
    attrs.iter().any(|attr| {
        let is_cfg_path = attr.has_name(Symbol::intern("cfg"));
        is_cfg_path
            && attr.meta_item_list().is_some_and(|meta_items| {
                let test_symbol = Symbol::intern("test");
                let is_test_path = |meta_items: &[NestedMetaItem]| {
                    meta_items
                        .iter()
                        .any(|meta_item| meta_item.has_name(test_symbol))
                };
                is_test_path(&meta_items)
                    || meta_items.iter().any(|meta_item| {
                        (meta_item.has_name(Symbol::intern("any"))
                            || meta_item.has_name(Symbol::intern("all")))
                            && meta_item.meta_item_list().is_some_and(is_test_path)
                    })
            })
    })
}
