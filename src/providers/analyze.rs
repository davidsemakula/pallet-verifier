//! Common utilities and helpers for traversing and analyzing MIR.

use rustc_abi::VariantIdx;
use rustc_data_structures::graph::{StartNode, Successors, dominators::Dominators};
use rustc_hash::FxHashSet;
use rustc_hir::LangItem;
use rustc_middle::{
    mir::{
        BasicBlock, BasicBlockData, BasicBlocks, LocalDecls, Operand, Place, PlaceElem,
        RETURN_PLACE, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::{AssocTag, GenericArg, ImplSubject, List, Region, Ty, TyCtxt, TyKind},
};
use rustc_span::{def_id::DefId, symbol::Ident};

use itertools::Itertools;
use serde::{Deserialize, Serialize};

/// Finds the innermost place if the given place is a single deref of a local,
/// otherwise returns the given place.
fn direct_place(place: Place) -> Place {
    match place.local_or_deref_local() {
        Some(local) => Place::from(local),
        None => place,
    }
}

/// Returns the derefed place and region (if the current place is a reference).
fn deref_place<'tcx>(
    place: Place<'tcx>,
    block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
) -> Option<(Place<'tcx>, Region<'tcx>)> {
    let target_place = direct_place(place);
    basic_blocks[block].statements.iter().find_map(|stmt| {
        let StatementKind::Assign(assign) = &stmt.kind else {
            return None;
        };
        if target_place != assign.0 {
            return None;
        }
        let Rvalue::Ref(region, _, op_place) = &assign.1 else {
            return None;
        };
        let direct_op_place = direct_place(*op_place);
        direct_op_place
            .projection
            .is_empty()
            .then_some((direct_op_place, *region))
    })
}

// Returns the innermost derefed place and region (if the current place is a reference).
pub fn deref_place_recursive<'tcx>(
    place: Place<'tcx>,
    block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
) -> Option<(Place<'tcx>, Region<'tcx>)> {
    let mut result = None;
    let mut deref_target_place = place;
    while let Some((derefed_place, region)) = deref_place(deref_target_place, block, basic_blocks) {
        result = Some((derefed_place, region));
        deref_target_place = derefed_place;
    }
    result
}

/// Returns terminator (if any) whose destination is the given place,
/// and whose basic block is a predecessor of the given anchor block.
pub fn pre_anchor_assign_terminator<'tcx>(
    place: Place<'tcx>,
    parent_block: BasicBlock,
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    dominators: &Dominators<BasicBlock>,
) -> Option<(Terminator<'tcx>, BasicBlock)> {
    let mut places = FxHashSet::default();
    let mut already_visited = FxHashSet::default();

    places.insert(place);
    let mut deref_target_place = place;
    while let Some((derefed_place, _)) = deref_place(deref_target_place, parent_block, basic_blocks)
    {
        places.insert(derefed_place);
        deref_target_place = derefed_place;
    }

    return pre_anchor_assign_terminator_inner(
        &mut places,
        anchor_block,
        anchor_block,
        basic_blocks,
        dominators,
        &mut already_visited,
    );

    fn pre_anchor_assign_terminator_inner<'tcx>(
        places: &mut FxHashSet<Place<'tcx>>,
        current_block: BasicBlock,
        anchor_block: BasicBlock,
        basic_blocks: &BasicBlocks<'tcx>,
        dominators: &Dominators<BasicBlock>,
        already_visited: &mut FxHashSet<BasicBlock>,
    ) -> Option<(Terminator<'tcx>, BasicBlock)> {
        for pred_bb in &basic_blocks.predecessors()[current_block] {
            if already_visited.contains(pred_bb) {
                continue;
            }
            already_visited.insert(*pred_bb);

            if pred_bb.index() != anchor_block.index()
                && !dominators.dominates(anchor_block, *pred_bb)
            {
                let bb_data = &basic_blocks[*pred_bb];
                for stmt in &bb_data.statements {
                    add_place_aliases(places, stmt);
                }
                if let Some(terminator) = &bb_data.terminator {
                    if let TerminatorKind::Call { destination, .. } = &terminator.kind {
                        if places.contains(destination) {
                            return Some((terminator.clone(), *pred_bb));
                        }
                    }
                }
                let assign = pre_anchor_assign_terminator_inner(
                    places,
                    *pred_bb,
                    anchor_block,
                    basic_blocks,
                    dominators,
                    already_visited,
                );
                if assign.is_some() {
                    return assign;
                }
            }
        }

        None
    }

    fn add_place_aliases<'tcx>(places: &mut FxHashSet<Place<'tcx>>, stmt: &Statement<'tcx>) {
        if let StatementKind::Assign(assign) = &stmt.kind {
            if places.contains(&assign.0) {
                if let Rvalue::Use(Operand::Copy(op_place) | Operand::Move(op_place)) = &assign.1 {
                    places.insert(*op_place);
                }
            }
        }
    }
}

/// Returns true if the given `DefId` is an associated item of the slice type `[T]`.
pub fn is_slice_assoc_item(def_id: DefId, tcx: TyCtxt) -> bool {
    tcx.opt_associated_item(def_id)
        .and_then(|assoc_item| assoc_item.impl_container(tcx))
        .is_some_and(|impl_def_id| {
            let impl_subject = tcx.impl_subject(impl_def_id).skip_binder();
            if let ImplSubject::Inherent(ty) = impl_subject {
                if let TyKind::Slice(slice_ty) = ty.kind() {
                    if let TyKind::Param(param_ty) = slice_ty.kind() {
                        return param_ty.name.as_str() == "T";
                    }
                }
            }
            false
        })
}

/// Finds place for operand/arg and basic block of a `Deref` call (if any) that assigns to the given place.
pub fn deref_subject<'tcx>(
    place: Place<'tcx>,
    parent_block: BasicBlock,
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    dominators: &Dominators<BasicBlock>,
    tcx: TyCtxt<'tcx>,
) -> Option<(Place<'tcx>, BasicBlock)> {
    let deref_call =
        pre_anchor_assign_terminator(place, parent_block, anchor_block, basic_blocks, dominators);
    deref_call
        .and_then(|(terminator, block)| deref_operand(&terminator, tcx).map(|place| (place, block)))
}

/// Recursively finds places for operand/arg and basic blocks of a `Deref` calls (if any) that assign to the given place.
pub fn deref_subjects_recursive<'tcx>(
    place: Place<'tcx>,
    parent_block: BasicBlock,
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    dominators: &Dominators<BasicBlock>,
    tcx: TyCtxt<'tcx>,
) -> FxHashSet<(Place<'tcx>, BasicBlock)> {
    let mut deref_subjects = FxHashSet::default();
    let mut current_place = place;
    let mut current_block = parent_block;

    while let Some((deref_arg_place, deref_block)) = deref_subject(
        current_place,
        current_block,
        anchor_block,
        basic_blocks,
        dominators,
        tcx,
    ) {
        deref_subjects.insert((deref_arg_place, deref_block));
        current_place = deref_arg_place;
        current_block = deref_block;
    }

    deref_subjects
}

/// Returns place (if any) for the arg/operand of `std::ops::Deref` or `std::ops::DerefMut`.
fn deref_operand<'tcx>(terminator: &Terminator<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Place<'tcx>> {
    let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
        return None;
    };
    let (def_id, ..) = func.const_fn_def()?;
    let deref_trait_def_id = tcx
        .lang_items()
        .get(LangItem::Deref)
        .expect("Expected `std::ops::Deref` lang item");
    let deref_mut_trait_def_id = tcx
        .lang_items()
        .get(LangItem::DerefMut)
        .expect("Expected `std::ops::DerefMut` lang item");
    let is_deref_call = matches!(tcx.item_name(def_id).as_str(), "deref" | "deref_mut")
        && tcx
            .opt_associated_item(def_id)
            .and_then(|assoc_item| assoc_item.trait_container(tcx))
            .is_some_and(|trait_def_id| {
                trait_def_id == deref_trait_def_id || trait_def_id == deref_mut_trait_def_id
            });
    if !is_deref_call {
        return None;
    }
    args.first()?.node.place()
}

/// Returns true if the type is a known collection whose length/size maxima is `isize::MAX`.
pub fn is_isize_bound_collection(ty: Ty, tcx: TyCtxt) -> bool {
    ty.peel_refs().ty_adt_def().is_some_and(|adt_def| {
        let adt_def_id = adt_def.did();
        matches!(
            (
                tcx.crate_name(adt_def_id.krate).as_str(),
                tcx.item_name(adt_def_id).as_str(),
            ),
            ("alloc" | "std", "Vec" | "VecDeque")
                | ("std" | "hashbrown", "HashSet" | "HashMap")
                | ("hashbrown", "HashTable")
                | (
                    "bounded_collections" | "frame_support",
                    "BoundedVec" | "WeakBoundedVec"
                )
                | ("frame_support", "PrefixIterator" | "KeyPrefixIterator")
        )
    })
}

/// Convenience type alias for tracking info necessary to build a length/size call for a collection
/// (i.e. a list of tuples of length/size call `DefId`, call generic args, and the return type).
pub type LenCallBuilderInfo<'tcx> = Vec<(DefId, &'tcx List<GenericArg<'tcx>>, Ty<'tcx>)>;

/// Returns info necessary for constructing a length/size call for the given collection type
/// (if possible).
///
/// See [`LenCallBuilderInfo`] for additional details.
pub fn collection_len_call<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<LenCallBuilderInfo<'tcx>> {
    let base_ty = ty.peel_refs();
    let TyKind::Adt(adt_def, gen_args) = base_ty.kind() else {
        return None;
    };
    let adt_def_id = adt_def.did();

    // Finds associated function by name.
    let assoc_fn_def = |name: &str| {
        tcx.inherent_impls(adt_def_id)
            .iter()
            .find_map(|impl_def_id| {
                tcx.associated_items(impl_def_id)
                    .find_by_ident_and_kind(tcx, Ident::from_str(name), AssocTag::Fn, *impl_def_id)
                    .map(|assoc_item| assoc_item.def_id)
            })
    };

    // Finds associated function on `Deref` target.
    let deref_target_assoc_fn = || {
        let deref_trait_def_id = tcx
            .lang_items()
            .get(LangItem::Deref)
            .expect("Expected `std::ops::Deref` lang item");
        let deref_impl = tcx
            .non_blanket_impls_for_ty(deref_trait_def_id, base_ty)
            .next()?;
        let deref_assoc_items = tcx.associated_items(deref_impl);
        let deref_fn_assoc_item = deref_assoc_items.find_by_ident_and_kind(
            tcx,
            Ident::from_str("deref"),
            AssocTag::Fn,
            deref_impl,
        )?;
        let deref_target_assoc_item = deref_assoc_items.find_by_ident_and_kind(
            tcx,
            Ident::from_str("Target"),
            AssocTag::Type,
            deref_impl,
        )?;
        let deref_target_ty = tcx
            .type_of(deref_target_assoc_item.def_id)
            .instantiate(tcx, gen_args);

        let deref_len_call_info = collection_len_call(deref_target_ty, tcx);
        deref_len_call_info.map(|mut deref_len_call_info| {
            deref_len_call_info.splice(
                ..0,
                [(deref_fn_assoc_item.def_id, *gen_args, deref_target_ty)],
            );
            deref_len_call_info
        })
    };

    match (
        tcx.crate_name(adt_def_id.krate).as_str(),
        tcx.item_name(adt_def_id).as_str(),
    ) {
        (
            "std" | "alloc",
            "Vec" | "VecDeque" | "LinkedList" | "BTreeSet" | "BTreeMap" | "BinaryHeap",
        )
        | ("std" | "hashbrown", "HashSet" | "HashMap")
        | ("hashbrown", "HashTable")
        | (
            "bounded_collections" | "frame_support",
            "BoundedVec" | "BoundedSlice" | "WeakBoundedVec" | "BoundedBTreeSet"
            | "BoundedBTreeMap",
        ) => assoc_fn_def("len")
            .filter(|def_id| tcx.is_mir_available(def_id))
            .map(|def_id| vec![(def_id, *gen_args, tcx.types.usize)])
            .or_else(deref_target_assoc_fn),
        _ => None,
    }
}

/// Given a collection place, returns info necessary to construct a collection length/size call
/// only if the collection place is borrowed (i.e. a reference).
///
/// Return info (if any) includes the derefed collection place, the `region`,
/// along with [`LenCallBuilderInfo`].
pub fn borrowed_collection_len_call_info<'tcx>(
    place: Place<'tcx>,
    block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<(Place<'tcx>, Region<'tcx>, LenCallBuilderInfo<'tcx>)> {
    let place_ty = place.ty(local_decls, tcx).ty;
    let (collection_place, region) =
        deref_place_recursive(place, block, basic_blocks).or_else(|| {
            if let TyKind::Ref(region, _, _) = place_ty.kind() {
                Some((place, *region))
            } else {
                None
            }
        })?;
    collection_len_call(place_ty, tcx)
        .map(|len_call_info| (collection_place, region, len_call_info))
}

/// Returns info necessary for constructing a length/size call for the given slice place (if possible).
///
/// See [`LenCallBuilderInfo`] for additional details.
pub fn slice_len_call_info<'tcx>(
    place: Place<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<(Region<'tcx>, LenCallBuilderInfo<'tcx>)> {
    let TyKind::Ref(region, slice_ty, _) = place.ty(local_decls, tcx).ty.kind() else {
        return None;
    };
    if !slice_ty.is_slice() {
        return None;
    }
    let slice_len_def_id = tcx
        .lang_items()
        .get(LangItem::SliceLen)
        .expect("Expected `[T]::len` lang item");
    let gen_ty = slice_ty
        .walk()
        .nth(1)
        .expect("Expected a generic arg for `[T]`");
    let gen_args = tcx.mk_args(&[gen_ty]);
    Some((*region, vec![(slice_len_def_id, gen_args, tcx.types.usize)]))
}

/// An `Option`, `Result` or `ControlFlow` variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SwitchVariant {
    /// `Option::Some`
    OptionSome,
    /// `Option::None`
    #[allow(dead_code)]
    OptionNone,
    /// `Result::Ok`
    ResultOk,
    /// `Result::Err`
    ResultErr,
    /// `ControlFlow::Continue`
    ControlFlowContinue,
    /// `ControlFlow::Break`
    #[allow(dead_code)]
    ControlFlowBreak,
}

impl SwitchVariant {
    /// Returns `VariantIdx` for equivalent `LangItem`.
    ///
    /// # Panics
    ///
    /// Panics if the `LangItem` is not a Variant.
    pub fn idx(&self, tcx: TyCtxt) -> VariantIdx {
        let lang_item = self.lang_item();
        let variant_def_id = tcx
            .lang_items()
            .get(lang_item)
            .unwrap_or_else(|| panic!("Expected `DefId` for lang item for {lang_item:?}"));
        let adt_def_id = tcx.parent(variant_def_id);
        let adt_def = tcx.adt_def(adt_def_id);
        adt_def.variant_index_with_id(variant_def_id)
    }

    /// Returns name of the variant.
    pub fn name(&self) -> &str {
        match self {
            SwitchVariant::OptionSome => "Some",
            SwitchVariant::OptionNone => "None",
            SwitchVariant::ResultOk => "Ok",
            SwitchVariant::ResultErr => "Err",
            SwitchVariant::ControlFlowContinue => "Continue",
            SwitchVariant::ControlFlowBreak => "Break",
        }
    }

    /// Returns `LangItem` for the variant.
    fn lang_item(&self) -> LangItem {
        match self {
            SwitchVariant::OptionSome => LangItem::OptionSome,
            SwitchVariant::OptionNone => LangItem::OptionNone,
            SwitchVariant::ResultOk => LangItem::ResultOk,
            SwitchVariant::ResultErr => LangItem::ResultErr,
            SwitchVariant::ControlFlowContinue => LangItem::ControlFlowContinue,
            SwitchVariant::ControlFlowBreak => LangItem::ControlFlowBreak,
        }
    }
}

impl std::fmt::Display for SwitchVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// Tracks switch target info through "safe" transformations
/// (i.e. ones that don't change the `Result::Ok` nor `Result::Err` variant values) between
/// `Option::Some`, `Result::Ok` and `ControlFlow::Continue`
/// (e.g. via `Result::inspect`, `Result::inspect_err` calls e.t.c).
pub fn track_safe_result_transformations<'tcx>(
    switch_target_place: &mut Place<'tcx>,
    switch_target_block: &mut BasicBlock,
    target_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt,
) {
    let mut next_target_block = Some(target_block);
    while let Some(current_target_block) = next_target_block {
        let target_bb_data = &basic_blocks[current_target_block];
        if let Some((transformer_destination, transformer_target_block)) =
            safe_result_transform_destination(*switch_target_place, target_bb_data, tcx)
        {
            *switch_target_place = transformer_destination;
            *switch_target_block = current_target_block;
            next_target_block = transformer_target_block;
        } else {
            next_target_block = None;
        }
    }
}

// Tracks switch target info through "safe" transformations
// (i.e. ones that don't change the target variant's value) between
// `Option::Some`, `Result::Ok` and `ControlFlow::Continue`
// (e.g. via `std::ops::Try::branch` calls, `Option::ok_or`, `Result::ok`, `Result::map_err`
// and `Option::inspect` calls e.t.c).
pub fn track_safe_primary_opt_result_variant_transformations<'tcx>(
    switch_target_place: &mut Place<'tcx>,
    switch_target_block: &mut BasicBlock,
    switch_target_variant: &mut SwitchVariant,
    target_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt,
    strict: bool,
) {
    let mut next_target_block = Some(target_block);
    while let Some(current_target_block) = next_target_block {
        let block_data = &basic_blocks[current_target_block];
        if let Some((try_branch_destination, try_branch_target_bb)) =
            try_branch_destination(*switch_target_place, block_data, tcx)
        {
            *switch_target_place = try_branch_destination;
            *switch_target_block = current_target_block;
            *switch_target_variant = SwitchVariant::ControlFlowContinue;
            next_target_block = try_branch_target_bb;
        } else if let Some((transformer_destination, transformer_target_block)) =
            safe_option_some_transform_destination(*switch_target_place, block_data, tcx, strict)
        {
            *switch_target_place = transformer_destination;
            *switch_target_block = current_target_block;
            *switch_target_variant = SwitchVariant::OptionSome;
            next_target_block = transformer_target_block;
        } else if let Some((transformer_destination, transformer_target_block)) =
            safe_result_ok_transform_destination(*switch_target_place, block_data, tcx)
        {
            *switch_target_place = transformer_destination;
            *switch_target_block = current_target_block;
            *switch_target_variant = SwitchVariant::ResultOk;
            next_target_block = transformer_target_block;
        } else {
            next_target_block = None;
        }
    }
}

// Tracks switch target info through "safe" transformations
// (i.e. ones that don't change the target variant's value) from
// `Result::Err` to `Option::Some`, `Result::Ok` and `ControlFlow::Continue`
// (e.g. via `Result::err`, and then optionally through
// `std::ops::Try::branch` calls, `Option::ok_or`, `Result::map_err`
// and `Option::inspect` calls e.t.c).
pub fn track_safe_result_err_transformations<'tcx>(
    switch_target_place: &mut Place<'tcx>,
    switch_target_block: &mut BasicBlock,
    switch_target_variant: &mut SwitchVariant,
    target_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt,
    strict: bool,
) {
    let mut next_target_block = Some(target_block);
    let mut opt_some_target_block = None;
    fn result_err_crate_adt_and_fn_name_check(
        crate_name: &str,
        adt_name: &str,
        fn_name: &str,
    ) -> bool {
        matches!(crate_name, "std" | "core") && (adt_name == "Result" && fn_name == "err")
    }
    while let Some(current_target_block) = next_target_block {
        let block_data = &basic_blocks[current_target_block];
        if let Some((transformer_destination, transformer_target_block)) =
            safe_transform_destination(
                *switch_target_place,
                block_data,
                result_err_crate_adt_and_fn_name_check,
                tcx,
            )
        {
            *switch_target_place = transformer_destination;
            *switch_target_block = current_target_block;
            *switch_target_variant = SwitchVariant::OptionSome;
            next_target_block = None;
            opt_some_target_block = transformer_target_block;
        } else if let Some((transformer_destination, transformer_target_block)) =
            safe_result_err_transform_destination(*switch_target_place, block_data, tcx)
        {
            *switch_target_place = transformer_destination;
            *switch_target_block = current_target_block;
            *switch_target_variant = SwitchVariant::ResultErr;
            next_target_block = transformer_target_block;
        } else {
            next_target_block = None;
        }
    }

    if let Some(opt_some_target_block) = opt_some_target_block {
        track_safe_primary_opt_result_variant_transformations(
            switch_target_place,
            switch_target_block,
            switch_target_variant,
            opt_some_target_block,
            basic_blocks,
            tcx,
            strict,
        );
    }
}

/// Returns the target block for the given basic block's terminator call (if any).
pub fn call_target(block_data: &BasicBlockData) -> Option<BasicBlock> {
    let terminator = block_data.terminator.as_ref()?;
    match &terminator.kind {
        TerminatorKind::Call { target, .. } => *target,
        _ => None,
    }
}

/// Returns destination place and target block (if any) of an `std::ops::Try::branch` call
/// (i.e. `?` operator) where the given place is the first argument.
fn try_branch_destination<'tcx>(
    place: Place<'tcx>,
    block_data: &BasicBlockData<'tcx>,
    tcx: TyCtxt,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    let terminator = block_data.terminator.as_ref()?;
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &terminator.kind
    else {
        return None;
    };
    let (def_id, ..) = func.const_fn_def()?;
    let try_branch_def_id = tcx
        .lang_items()
        .get(LangItem::TryTraitBranch)
        .expect("Expected `std::ops::Try::branch` lang item");
    if def_id != try_branch_def_id {
        return None;
    }
    let first_arg_place = args.first().and_then(|arg| arg.node.place())?;
    if first_arg_place != place {
        return None;
    }

    Some((*destination, *target))
}

/// Returns destination place and target block (if any) of a transformation into `Option`
/// that doesn't change the `Option::Some` variant value, where the given place is the first argument.
///
/// (e.g. via `Option::inspect`, `Result::ok` calls e.t.c).
fn safe_option_some_transform_destination<'tcx>(
    place: Place<'tcx>,
    block_data: &BasicBlockData<'tcx>,
    tcx: TyCtxt,
    strict: bool,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    let crate_adt_and_fn_name_check = |crate_name: &str, adt_name: &str, fn_name: &str| -> bool {
        matches!(crate_name, "std" | "core")
            && ((adt_name == "Option"
                && (matches!(
                    fn_name,
                    "copied" | "cloned" | "inspect" | "as_ref" | "as_deref"
                ) || (!strict && fn_name == "filter")))
                || (adt_name == "Result" && fn_name == "ok"))
    };
    safe_transform_destination(place, block_data, crate_adt_and_fn_name_check, tcx)
}

/// Returns destination place and target block (if any) of a transformation into `Result`
/// that doesn't change the `Result::Ok` nor `Result::Err` variant values,
/// where the given place is the first argument.
///
/// (e.g. via `Result::inspect`, `Result::inspect_err` calls e.t.c).
fn safe_result_transform_destination<'tcx>(
    place: Place<'tcx>,
    block_data: &BasicBlockData<'tcx>,
    tcx: TyCtxt,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    fn crate_adt_and_fn_name_check(crate_name: &str, adt_name: &str, fn_name: &str) -> bool {
        matches!(crate_name, "std" | "core")
            && adt_name == "Result"
            && matches!(
                fn_name,
                "copied" | "cloned" | "inspect" | "inspect_err" | "as_ref" | "as_deref"
            )
    }
    safe_transform_destination(place, block_data, crate_adt_and_fn_name_check, tcx)
}

/// Returns destination place and target block (if any) of a transformation into `Result`
/// that doesn't change the `Result::Ok` variant value, where the given place is the first argument.
///
/// (e.g. via `Result::map_err`, `Option::ok_or` calls e.t.c).
fn safe_result_ok_transform_destination<'tcx>(
    place: Place<'tcx>,
    block_data: &BasicBlockData<'tcx>,
    tcx: TyCtxt,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    fn crate_adt_and_fn_name_check(crate_name: &str, adt_name: &str, fn_name: &str) -> bool {
        matches!(crate_name, "std" | "core")
            && ((adt_name == "Result"
                && matches!(
                    fn_name,
                    "map_err"
                        | "copied"
                        | "cloned"
                        | "inspect"
                        | "inspect_err"
                        | "as_ref"
                        | "as_deref"
                ))
                || (adt_name == "Option" && matches!(fn_name, "ok_or" | "ok_or_else")))
    }
    safe_transform_destination(place, block_data, crate_adt_and_fn_name_check, tcx)
}

/// Returns destination place and target block (if any) of a transformation into `Result`
/// that doesn't change the `Result::Err` variant value, where the given place is the first argument.
///
/// (e.g. via `Result::map`, `Result::inspect` calls e.t.c).
fn safe_result_err_transform_destination<'tcx>(
    place: Place<'tcx>,
    block_data: &BasicBlockData<'tcx>,
    tcx: TyCtxt,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    fn crate_adt_and_fn_name_check(crate_name: &str, adt_name: &str, fn_name: &str) -> bool {
        matches!(crate_name, "std" | "core")
            && (adt_name == "Result"
                && matches!(
                    fn_name,
                    "map" | "copied" | "cloned" | "inspect" | "inspect_err" | "as_ref" | "as_deref"
                ))
    }
    safe_transform_destination(place, block_data, crate_adt_and_fn_name_check, tcx)
}

/// Returns destination place and target block (if any) of a "safe" transformation
/// where the given place is the first argument of the "transformer" call.
///
/// See [`safe_option_some_transform_destination`] and [`safe_result_transform_destination`] docs
/// for details about the target "safe" transformations.
pub fn safe_transform_destination<'tcx>(
    place: Place<'tcx>,
    block_data: &BasicBlockData<'tcx>,
    transform_check: impl Fn(&str, &str, &str) -> bool,
    tcx: TyCtxt,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    let terminator = block_data.terminator.as_ref()?;
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &terminator.kind
    else {
        return None;
    };
    let first_arg = args.first()?;
    let first_arg_place = first_arg.node.place()?;
    if first_arg_place != place {
        return None;
    }

    let (def_id, ..) = func.const_fn_def()?;
    let fn_name = tcx.item_name(def_id);
    let crate_name = tcx.crate_name(def_id.krate);

    let assoc_item = tcx.opt_associated_item(def_id)?;
    let impl_def_id = assoc_item.impl_container(tcx)?;
    let impl_subject = tcx.impl_subject(impl_def_id).skip_binder();
    let ImplSubject::Inherent(ty) = impl_subject else {
        return None;
    };
    let adt_def = ty.ty_adt_def()?;
    let adt_name = tcx.item_name(adt_def.did());

    let is_safe_transform =
        transform_check(crate_name.as_str(), adt_name.as_str(), fn_name.as_str());
    is_safe_transform.then_some((*destination, *target))
}

/// Returns true if the operand is the const identity function (i.e. `std::convert::identity`).
///
/// Ref: <https://doc.rust-lang.org/std/convert/fn.identity.html>
pub fn is_identity_fn(operand: &Operand, tcx: TyCtxt) -> bool {
    let Some((def_id, ..)) = operand.const_fn_def() else {
        return false;
    };
    let fn_name = tcx.item_name(def_id);
    let crate_name = tcx.crate_name(def_id.krate);
    fn_name.as_str() == "identity" && matches!(crate_name.as_str(), "std" | "core")
}

/// Returns true if the operand is an identity closure (i.e. `|x| x`).
pub fn is_identity_closure(operand: &Operand, tcx: TyCtxt) -> bool {
    let Some(const_op) = operand.constant() else {
        return false;
    };
    let const_op_ty = const_op.const_.ty();
    let TyKind::Closure(def_id, _) = const_op_ty.kind() else {
        return false;
    };
    let body = tcx.optimized_mir(def_id);
    let blocks = &body.basic_blocks;
    if blocks.len() != 1 {
        return false;
    }
    let bb_data = &blocks[blocks.start_node()];
    let Some(terminator) = &bb_data.terminator else {
        return false;
    };
    if terminator.kind != TerminatorKind::Return {
        return false;
    }
    let stmts = &bb_data.statements;
    if stmts.len() != 1 {
        return false;
    }
    let stmt = stmts.first().expect("Expected a stmt");
    let StatementKind::Assign(assign) = &stmt.kind else {
        return false;
    };
    let assign_place = assign.0;
    let assign_rvalue = &assign.1;
    if assign_place.local != RETURN_PLACE {
        return false;
    }
    let Rvalue::Use(Operand::Copy(assign_rvalue_place) | Operand::Move(assign_rvalue_place)) =
        assign_rvalue
    else {
        return false;
    };
    assign_rvalue_place.local.as_usize() <= body.arg_count
}

/// Collects target basic blocks (if any) for the given value of a switch on discriminant of given place.
pub fn collect_switch_targets_for_discr_value<'tcx>(
    place: Place<'tcx>,
    value: u128,
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
) -> FxHashSet<BasicBlock> {
    let mut target_blocks = FxHashSet::default();
    let mut already_visited = FxHashSet::default();
    collect_switch_targets_for_discr_value_inner(
        place,
        value,
        anchor_block,
        basic_blocks,
        &mut target_blocks,
        &mut already_visited,
    );
    return target_blocks;

    fn collect_switch_targets_for_discr_value_inner<'tcx>(
        destination: Place<'tcx>,
        value: u128,
        anchor_block: BasicBlock,
        basic_blocks: &BasicBlocks<'tcx>,
        target_blocks: &mut FxHashSet<BasicBlock>,
        already_visited: &mut FxHashSet<BasicBlock>,
    ) {
        for successor_block in basic_blocks.successors(anchor_block) {
            if already_visited.contains(&successor_block) {
                continue;
            }
            already_visited.insert(successor_block);

            // Finds switch target (if any) for the discriminant with the given value.
            if let Some(target_block) =
                switch_target_for_discr_value(destination, value, &basic_blocks[successor_block])
            {
                target_blocks.insert(target_block);
            }

            collect_switch_targets_for_discr_value_inner(
                destination,
                value,
                successor_block,
                basic_blocks,
                target_blocks,
                already_visited,
            );
        }
    }
}

/// Returns target basic block (if any) for the given value of a switch on discriminant of given place.
fn switch_target_for_discr_value<'tcx>(
    place: Place<'tcx>,
    value: u128,
    block_data: &BasicBlockData<'tcx>,
) -> Option<BasicBlock> {
    block_data.statements.iter().find_map(|stmt| {
        let StatementKind::Assign(assign) = &stmt.kind else {
            return None;
        };
        let Rvalue::Discriminant(op_place) = assign.1 else {
            return None;
        };
        if op_place != place {
            return None;
        }

        let terminator = block_data.terminator.as_ref()?;
        let TerminatorKind::SwitchInt { discr, targets } = &terminator.kind else {
            return None;
        };
        let discr_place = match discr {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => {
                return None;
            }
        };
        if *discr_place != assign.0 {
            return None;
        }

        Some(targets.target_for_value(value))
    })
}

/// Returns place (if any) for the variant downcast to `ty` of given place.
pub fn variant_downcast_to_ty_place<'tcx>(
    place: Place<'tcx>,
    variant_name: &str,
    variant_idx: VariantIdx,
    ty: Ty<'tcx>,
    stmt: &Statement<'tcx>,
) -> Option<Place<'tcx>> {
    let StatementKind::Assign(assign) = &stmt.kind else {
        return None;
    };
    let op_place = match &assign.1 {
        Rvalue::Use(Operand::Copy(op_place) | Operand::Move(op_place))
        | Rvalue::Ref(_, _, op_place) => Some(op_place),
        _ => None,
    }?;
    is_variant_downcast_to_ty_place(*op_place, place, variant_name, variant_idx, ty)
        .then_some(assign.0)
}

/// Returns true if the given `op_place` is a variant downcast to `ty` of `place`.
pub fn is_variant_downcast_to_ty_place<'tcx>(
    op_place: Place<'tcx>,
    place: Place<'tcx>,
    variant_name: &str,
    variant_idx: VariantIdx,
    ty: Ty<'tcx>,
) -> bool {
    if op_place.local == place.local
        && let Some((
            (_, PlaceElem::Downcast(op_variant_name, op_variant_idx)),
            (_, PlaceElem::Field(field_idx, field_ty)),
        )) = op_place.iter_projections().collect_tuple()
        && ((op_variant_name.is_none()
            || op_variant_name.is_some_and(|name| name.as_str() == variant_name))
            && op_variant_idx == variant_idx
            && field_idx.as_u32() == 0
            && field_ty == ty)
    {
        true
    } else {
        false
    }
}
