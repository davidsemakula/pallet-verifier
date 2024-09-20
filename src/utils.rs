//! Common analysis utilities.

use rustc_ast::NestedMetaItem;
use rustc_hir::HirId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

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
