//! Common analysis utilities.

use rustc_ast::NestedMetaItem;
use rustc_hir::{
    definitions::{DefPathData, DisambiguatedDefPathData},
    HirId,
};
use rustc_middle::{query::IntoQueryParam, ty::TyCtxt};
use rustc_span::{def_id::DefId, Symbol};

/// Returns the name of the definition as a `Symbol` (if any).
pub fn def_name(def_id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> Option<Symbol> {
    let def_key = tcx.def_key(def_id);
    match def_key.disambiguated_data {
        DisambiguatedDefPathData {
            data:
                DefPathData::MacroNs(name)
                | DefPathData::LifetimeNs(name)
                | DefPathData::TypeNs(name)
                | DefPathData::ValueNs(name),
            ..
        } => Some(name),
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
