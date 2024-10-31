//! Common analysis utilities.

use rustc_ast::NestedMetaItem;
use rustc_hir::{def::DefKind, HirId};
use rustc_middle::{middle::exported_symbols::ExportedSymbol, ty::TyCtxt};
use rustc_span::{def_id::DefId, Symbol};

use std::env;

use crate::ENV_TARGET_POINTER_WIDTH;

pub const HOST_POINTER_WIDTH: usize = std::mem::size_of::<usize>() * 8;

/// Returns the target pointer size in bits.
pub fn target_pointer_width() -> usize {
    match env::var(ENV_TARGET_POINTER_WIDTH).as_deref() {
        Ok("16") => 16,
        Ok("32") => 32,
        Ok("64") => 64,
        _ => HOST_POINTER_WIDTH,
    }
}

/// Checks if an item (given it's `HirId`) "effectively" has a `#[cfg(test)]` attribute.
pub fn has_cfg_test_attr(hir_id: HirId, tcx: TyCtxt) -> bool {
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

/// Returns `DefId` (if known) of a mirai annotation function.
pub fn mirai_annotation_fn(name: &str, tcx: TyCtxt) -> Option<DefId> {
    let annotations_crate = tcx
        .crates(())
        .iter()
        .find(|crate_num| tcx.crate_name(**crate_num).as_str() == "mirai_annotations")
        .expect("Expected `mirai_annotations` crate as a dependency");
    tcx.exported_symbols(*annotations_crate)
        .iter()
        .find_map(|(exported_sym, _)| {
            if let ExportedSymbol::NonGeneric(def_id) = exported_sym {
                if tcx.def_kind(def_id) == DefKind::Fn && tcx.item_name(*def_id).as_str() == name {
                    return Some(*def_id);
                }
            }
            None
        })
}
