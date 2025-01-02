//! Common analysis utilities.

use rustc_ast::NestedMetaItem;
use rustc_hir::{def_id::CrateNum, HirId};
use rustc_middle::ty::TyCtxt;
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

/// Returns `CrateNum` given a crate name.
pub fn find_crate(name: &str, tcx: TyCtxt) -> Option<CrateNum> {
    tcx.crates(())
        .iter()
        .find(|crate_num| tcx.crate_name(**crate_num).as_str() == name)
        .cloned()
}

/// Returns the `DefId` of the parent/subject trait (if any) for the associated item
/// with the given `DefId`.
pub fn assoc_item_parent_trait(def_id: DefId, tcx: TyCtxt) -> Option<DefId> {
    tcx.opt_associated_item(def_id).and_then(|assoc_item| {
        assoc_item.trait_container(tcx).or_else(|| {
            assoc_item
                .impl_container(tcx)
                .and_then(|impl_def_id| tcx.impl_trait_ref(impl_def_id))
                .map(|trait_ref| trait_ref.skip_binder().def_id)
        })
    })
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

/// Returns the highlight style for console text.
pub fn highlight_style() -> owo_colors::Style {
    let is_color_disabled = env::var("PALLET_VERIFIER_NO_COLOR")
        .is_ok_and(|val| matches!(val.as_str(), "true" | "yes" | "y" | "1"));
    if is_color_disabled {
        owo_colors::style()
    } else {
        owo_colors::Style::new().green().bold()
    }
}
