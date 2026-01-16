//! Common analysis utilities.

use rustc_ast::MetaItemInner;
use rustc_errors::DiagCtxtHandle;
use rustc_hir::{HirId, def_id::CrateNum};
use rustc_middle::ty::{GenericArg, List, TyCtxt, TyKind};
use rustc_span::{Symbol, def_id::DefId};
use rustc_type_ir::{IntTy, UintTy};

use std::{env, process};

use itertools::Itertools;

use crate::{
    ENTRY_POINT_FN_PREFIX, ENV_TARGET_POINTER_WIDTH, EntryPointInfo, EntryPointsInfo,
    ResolvedEntryPoint,
};

pub const HOST_POINTER_WIDTH: usize = std::mem::size_of::<usize>() * 8;

/// Resolves generated entry points.
///
/// # Panics
///
/// Panics with a compiler diagostic message when failing to resolve an entry point.
pub fn resolve_entry_points(
    entry_points: &EntryPointsInfo,
    tcx: TyCtxt,
    dcx: DiagCtxtHandle,
) -> Vec<ResolvedEntryPoint> {
    try_resolve_entry_points(entry_points, tcx)
        .process_results(|processor| processor.collect())
        .unwrap_or_else(|entry_point_info| {
            let mut error = dcx.struct_err(format!(
                "Couldn't find definition for {}: `{}`",
                entry_point_info.call_kind,
                entry_point_info.name.replace(ENTRY_POINT_FN_PREFIX, "")
            ));
            error.note("This is most likely a bug in pallet-verifier.");
            error.help(
                "Please consider filling a bug report at \
            https://github.com/davidsemakula/pallet-verifier/issues",
            );
            error.emit();
            process::exit(rustc_driver::EXIT_FAILURE)
        })
}

/// Resolves generated entry points.
pub fn try_resolve_entry_points<'compilation, 'tcx>(
    entry_points: &'compilation EntryPointsInfo,
    tcx: TyCtxt<'tcx>,
) -> impl Iterator<Item = Result<ResolvedEntryPoint, EntryPointInfo<'compilation>>>
+ use<'tcx, 'compilation> {
    tcx.hir_body_owners().filter_map(move |local_def_id| {
        tcx.opt_item_name(local_def_id.to_def_id())
            .and_then(|def_name| {
                entry_points
                    .iter()
                    .find_map(|(name, (target_hash, call_kind))| {
                        if name != def_name.as_str() {
                            return None;
                        }
                        let callee_def_id = tcx.def_path_hash_to_def_id(*target_hash);
                        match callee_def_id {
                            Some(callee_def_id) => callee_def_id.as_local().map(|callee_def_id| {
                                Ok(ResolvedEntryPoint {
                                    def_id: local_def_id,
                                    callee_def_id,
                                    call_kind: *call_kind,
                                })
                            }),
                            None => Some(Err(EntryPointInfo {
                                name: name.as_str(),
                                callee_def_hash: target_hash,
                                call_kind: *call_kind,
                            })),
                        }
                    })
            })
    })
}

/// Returns the target pointer size in bits.
pub fn target_pointer_width() -> usize {
    match env::var(ENV_TARGET_POINTER_WIDTH).as_deref() {
        Ok("16") => 16,
        Ok("32") => 32,
        Ok("64") => 64,
        _ => HOST_POINTER_WIDTH,
    }
}

// Returns `isize::MAX` value for target platform.
pub fn target_isize_max() -> u128 {
    let pointer_width = target_pointer_width();
    match pointer_width {
        16 => i16::MAX as u128,
        32 => i32::MAX as u128,
        64 => i64::MAX as u128,
        _ => unreachable!("Unsupported pointer width"),
    }
}

// Returns `usize::MAX` value for target platform.
pub fn target_usize_max() -> u128 {
    let pointer_width = target_pointer_width();
    match pointer_width {
        16 => u16::MAX as u128,
        32 => u32::MAX as u128,
        64 => u64::MAX as u128,
        _ => unreachable!("Unsupported pointer width"),
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
    let attrs = tcx.hir_attrs(hir_id);
    attrs.iter().any(|attr| {
        let is_cfg_path = attr.has_any_name(&[Symbol::intern("cfg"), Symbol::intern("<cfg>")]);
        is_cfg_path
            && attr.meta_item_list().is_some_and(|meta_items| {
                let test_symbol = Symbol::intern("test");
                let is_test_path = |meta_items: &[MetaItemInner]| {
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

/// Returns true if the item with the given `DefId` is named like a generated storage prefix.
pub fn is_storage_prefix(def_id: DefId, tcx: TyCtxt) -> bool {
    tcx.item_name(def_id)
        .as_str()
        .starts_with("_GeneratedPrefixForStorage")
}

/// Returns true if the given generic args include a storage query type.
///
/// (i.e. `frame_support::storage::types::ValueQuery`, `frame_support::storage::types::OptionQuery`
/// or `frame_support::storage::types::ResultQuery`).
pub fn includes_query_type(gen_args: &List<GenericArg>, tcx: TyCtxt) -> bool {
    gen_args.iter().any(|arg| {
        arg.as_type()
            .and_then(|ty| ty.ty_adt_def())
            .map(|adt_def| adt_def.did())
            .is_some_and(|adt_def_id| {
                let crate_name = tcx.crate_name(adt_def_id.krate);
                let item_name = tcx.item_name(adt_def_id);
                crate_name.as_str() == "frame_support"
                    && matches!(
                        item_name.as_str(),
                        "ValueQuery" | "OptionQuery" | "ResultQuery"
                    )
            })
    })
}

/// Returns a string representation of the `DefPathHash` of the given `DefId`.
pub fn def_hash_str(def_id: DefId, tcx: TyCtxt) -> String {
    format!("{:?}", tcx.def_path_hash(def_id))
}

/// Returns the maximum value for the given integer type kind.
pub fn int_max(kind: &TyKind) -> Option<u128> {
    let val = match kind {
        TyKind::Int(IntTy::I8) => i8::MAX as u128,
        TyKind::Int(IntTy::I16) => i16::MAX as u128,
        TyKind::Int(IntTy::I32) => i32::MAX as u128,
        TyKind::Int(IntTy::I64) => i64::MAX as u128,
        TyKind::Int(IntTy::I128) => i128::MAX as u128,
        TyKind::Int(IntTy::Isize) => target_isize_max(),
        TyKind::Uint(UintTy::U8) => u8::MAX as u128,
        TyKind::Uint(UintTy::U16) => u16::MAX as u128,
        TyKind::Uint(UintTy::U32) => u32::MAX as u128,
        TyKind::Uint(UintTy::U64) => u64::MAX as u128,
        TyKind::Uint(UintTy::U128) => u128::MAX,
        TyKind::Uint(UintTy::Usize) => target_usize_max(),
        _ => return None,
    };
    Some(val)
}

/// Returns the bit width for the given integer type kind.
pub fn int_bit_width(kind: &TyKind) -> Option<usize> {
    let val = match kind {
        TyKind::Int(IntTy::I8) | TyKind::Uint(UintTy::U8) => 8,
        TyKind::Int(IntTy::I16) | TyKind::Uint(UintTy::U16) => 16,
        TyKind::Int(IntTy::I32) | TyKind::Uint(UintTy::U32) => 32,
        TyKind::Int(IntTy::I64) | TyKind::Uint(UintTy::U64) => 64,
        TyKind::Int(IntTy::I128) | TyKind::Uint(UintTy::U128) => 128,
        TyKind::Int(IntTy::Isize) | TyKind::Uint(UintTy::Usize) => target_pointer_width(),
        _ => return None,
    };
    Some(val)
}
