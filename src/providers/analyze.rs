//! Common utilities and helpers for traversing and analyzing MIR.

use rustc_abi::{FieldIdx, VariantIdx};
use rustc_data_structures::graph::{StartNode, Successors, dominators::Dominators};
use rustc_hash::FxHashSet;
use rustc_hir::LangItem;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, BasicBlockData, BasicBlocks, Local, LocalDecls, Location,
        Operand, Place, PlaceElem, RETURN_PLACE, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind, UnOp,
    },
    ty::{AssocTag, ClosureArgs, GenericArg, ImplSubject, List, Region, Ty, TyCtxt, TyKind},
};
use rustc_span::{def_id::DefId, symbol::Ident};

use itertools::Itertools;
use serde::{Deserialize, Serialize};

use crate::providers::annotate::CondOp;

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
        if let StatementKind::Assign(assign) = &stmt.kind
            && target_place == assign.0
            && let Rvalue::Ref(region, _, op_place) = &assign.1
        {
            let direct_op_place = direct_place(*op_place);
            direct_op_place
                .projection
                .is_empty()
                .then_some((direct_op_place, *region))
        } else {
            None
        }
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
        for pred_block in &basic_blocks.predecessors()[current_block] {
            if already_visited.contains(pred_block) {
                continue;
            }
            already_visited.insert(*pred_block);

            if pred_block.index() != anchor_block.index()
                && !dominators.dominates(anchor_block, *pred_block)
            {
                let block_data = &basic_blocks[*pred_block];
                add_place_aliases(places, block_data);
                if let Some(terminator) = &block_data.terminator {
                    if let TerminatorKind::Call { destination, .. } = &terminator.kind
                        && places.contains(destination)
                    {
                        return Some((terminator.clone(), *pred_block));
                    }
                }
                let assign = pre_anchor_assign_terminator_inner(
                    places,
                    *pred_block,
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

    fn add_place_aliases<'tcx>(
        places: &mut FxHashSet<Place<'tcx>>,
        block_data: &BasicBlockData<'tcx>,
    ) {
        for stmt in block_data.statements.iter().rev() {
            if let StatementKind::Assign(assign) = &stmt.kind
                && places.contains(&assign.0)
                && let Some(op_place) = rvalue_alias_place(&assign.1)
            {
                places.insert(direct_place(op_place));
            }
        }
    }
}

/// Collects places which are either copies/moves or references to the given place.
pub fn collect_place_aliases<'tcx>(
    place: Place<'tcx>,
    block_data: &BasicBlockData<'tcx>,
) -> FxHashSet<Place<'tcx>> {
    let mut aliases = FxHashSet::default();
    for stmt in block_data.statements.iter().rev() {
        if let StatementKind::Assign(assign) = &stmt.kind
            && (assign.0 == place || aliases.contains(&assign.0))
            && let Some(op_place) = rvalue_alias_place(&assign.1)
        {
            aliases.insert(direct_place(op_place));
        }
    }
    aliases
}

/// Returns `Rvalue` place only if it represents either a copy/move or a reference.
fn rvalue_alias_place<'tcx>(value: &Rvalue<'tcx>) -> Option<Place<'tcx>> {
    if let Rvalue::Use(Operand::Copy(op_place) | Operand::Move(op_place))
    | Rvalue::Ref(_, _, op_place)
    | Rvalue::CopyForDeref(op_place) = value
    {
        Some(*op_place)
    } else {
        None
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
    if let TyKind::Ref(region, slice_ty, _) = place.ty(local_decls, tcx).ty.kind()
        && slice_ty.is_slice()
    {
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
    } else {
        None
    }
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
/// (e.g. via `Option::inspect`, `Option::as_ref` calls e.t.c).
pub fn track_safe_option_transformations<'tcx>(
    switch_target_place: &mut Place<'tcx>,
    switch_target_block: &mut BasicBlock,
    target_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt,
) {
    let mut next_target_block = Some(target_block);
    while let Some(current_target_block) = next_target_block {
        let block_data = &basic_blocks[current_target_block];
        let Some(terminator) = &block_data.terminator else {
            continue;
        };
        if let Some((transformer_destination, transformer_target_block)) =
            safe_option_some_transform_destination(*switch_target_place, terminator, tcx, true)
        {
            *switch_target_place = transformer_destination;
            *switch_target_block = current_target_block;
            next_target_block = transformer_target_block;
        } else {
            next_target_block = None;
        }
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
        let block_data = &basic_blocks[current_target_block];
        let Some(terminator) = &block_data.terminator else {
            continue;
        };
        if let Some((transformer_destination, transformer_target_block)) =
            safe_result_transform_destination(*switch_target_place, terminator, tcx)
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
pub fn track_safe_primary_option_result_variant_transformations<'tcx>(
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
        let Some(terminator) = &block_data.terminator else {
            continue;
        };
        if let Some((try_branch_destination, try_branch_target_block)) =
            try_branch_destination(*switch_target_place, terminator, tcx)
        {
            *switch_target_place = try_branch_destination;
            *switch_target_block = current_target_block;
            *switch_target_variant = SwitchVariant::ControlFlowContinue;
            next_target_block = try_branch_target_block;
        } else if let Some((transformer_destination, transformer_target_block)) =
            safe_option_some_transform_destination(*switch_target_place, terminator, tcx, strict)
        {
            *switch_target_place = transformer_destination;
            *switch_target_block = current_target_block;
            *switch_target_variant = SwitchVariant::OptionSome;
            next_target_block = transformer_target_block;
        } else if let Some((transformer_destination, transformer_target_block)) =
            safe_result_ok_transform_destination(*switch_target_place, terminator, tcx)
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
        let Some(terminator) = &block_data.terminator else {
            continue;
        };
        if let Some((transformer_destination, transformer_target_block)) =
            first_arg_transformer_call_destination(
                *switch_target_place,
                terminator,
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
            safe_result_err_transform_destination(*switch_target_place, terminator, tcx)
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
        track_safe_primary_option_result_variant_transformations(
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
    terminator: &Terminator<'tcx>,
    tcx: TyCtxt,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    if let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &terminator.kind
        && let Some((def_id, ..)) = func.const_fn_def()
        && def_id
            == tcx
                .lang_items()
                .get(LangItem::TryTraitBranch)
                .expect("Expected `std::ops::Try::branch` lang item")
        && let Some(first_arg_place) = args.first().and_then(|arg| arg.node.place())
        && first_arg_place == place
    {
        Some((*destination, *target))
    } else {
        None
    }
}

/// Returns destination place and target block (if any) of a transformation into `Option`
/// that doesn't change the `Option::Some` variant value, where the given place is the first argument.
///
/// (e.g. via `Option::inspect`, `Result::ok` calls e.t.c).
fn safe_option_some_transform_destination<'tcx>(
    place: Place<'tcx>,
    terminator: &Terminator<'tcx>,
    tcx: TyCtxt,
    strict: bool,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    first_arg_transformer_call_destination(
        place,
        terminator,
        |crate_name, adt_name, fn_name| {
            matches!(crate_name, "std" | "core")
                && ((adt_name == "Option"
                    && (matches!(
                        fn_name,
                        "copied" | "cloned" | "inspect" | "as_ref" | "as_deref"
                    ) || (!strict && fn_name == "filter")))
                    || (adt_name == "Result" && fn_name == "ok"))
        },
        tcx,
    )
}

/// Returns destination place and target block (if any) of a transformation into `Result`
/// that doesn't change the `Result::Ok` nor `Result::Err` variant values,
/// where the given place is the first argument.
///
/// (e.g. via `Result::inspect`, `Result::inspect_err` calls e.t.c).
fn safe_result_transform_destination<'tcx>(
    place: Place<'tcx>,
    terminator: &Terminator<'tcx>,
    tcx: TyCtxt,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    first_arg_transformer_call_destination(
        place,
        terminator,
        |crate_name, adt_name, fn_name| {
            matches!(crate_name, "std" | "core")
                && adt_name == "Result"
                && matches!(
                    fn_name,
                    "copied" | "cloned" | "inspect" | "inspect_err" | "as_ref" | "as_deref"
                )
        },
        tcx,
    )
}

/// Returns destination place and target block (if any) of a transformation into `Result`
/// that doesn't change the `Result::Ok` variant value, where the given place is the first argument.
///
/// (e.g. via `Result::map_err`, `Option::ok_or` calls e.t.c).
fn safe_result_ok_transform_destination<'tcx>(
    place: Place<'tcx>,
    terminator: &Terminator<'tcx>,
    tcx: TyCtxt,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    first_arg_transformer_call_destination(
        place,
        terminator,
        |crate_name, adt_name, fn_name| {
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
        },
        tcx,
    )
}

/// Returns destination place and target block (if any) of a transformation into `Result`
/// that doesn't change the `Result::Err` variant value, where the given place is the first argument.
///
/// (e.g. via `Result::map`, `Result::inspect` calls e.t.c).
fn safe_result_err_transform_destination<'tcx>(
    place: Place<'tcx>,
    terminator: &Terminator<'tcx>,
    tcx: TyCtxt,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    first_arg_transformer_call_destination(
        place,
        terminator,
        |crate_name, adt_name, fn_name| {
            matches!(crate_name, "std" | "core")
                && (adt_name == "Result"
                    && matches!(
                        fn_name,
                        "map"
                            | "copied"
                            | "cloned"
                            | "inspect"
                            | "inspect_err"
                            | "as_ref"
                            | "as_deref"
                    ))
        },
        tcx,
    )
}

/// Returns destination place and target block (if any) if the given terminator matches
/// the given `call_matcher`, and the given place is the first argument of the terminator call.
pub fn first_arg_transformer_call_destination<'tcx>(
    place: Place<'tcx>,
    terminator: &Terminator<'tcx>,
    call_matcher: impl Fn(&str, &str, &str) -> bool,
    tcx: TyCtxt,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    if is_first_arg_transformer(place, terminator, call_matcher, tcx)
        && let TerminatorKind::Call {
            destination,
            target,
            ..
        } = &terminator.kind
    {
        Some((*destination, *target))
    } else {
        None
    }
}

/// Returns true if the given terminator matches the given `call_matcher`,
/// and the given place is the first argument of the terminator call.
pub fn is_first_arg_transformer<'tcx>(
    place: Place<'tcx>,
    terminator: &Terminator<'tcx>,
    call_matcher: impl Fn(&str, &str, &str) -> bool,
    tcx: TyCtxt,
) -> bool {
    if let TerminatorKind::Call { func, args, .. } = &terminator.kind
        && let Some(first_arg) = args.first()
        && let Some(first_arg_place) = first_arg.node.place()
        && first_arg_place == place
        && let Some((def_id, ..)) = func.const_fn_def()
        && let Some(assoc_item) = tcx.opt_associated_item(def_id)
        && let Some(impl_def_id) = assoc_item.impl_container(tcx)
        && let ImplSubject::Inherent(ty) = tcx.impl_subject(impl_def_id).skip_binder()
        && let Some(adt_def) = ty.ty_adt_def()
    {
        let fn_name = tcx.item_name(def_id);
        let crate_name = tcx.crate_name(def_id.krate);
        let adt_name = tcx.item_name(adt_def.did());
        call_matcher(crate_name.as_str(), adt_name.as_str(), fn_name.as_str())
    } else {
        false
    }
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
        if let StatementKind::Assign(assign) = &stmt.kind
            && let Rvalue::Discriminant(op_place) = assign.1
            && op_place == place
            && let Some(terminator) = block_data.terminator.as_ref()
            && let TerminatorKind::SwitchInt { discr, targets } = &terminator.kind
            && let Operand::Copy(discr_place) | Operand::Move(discr_place) = discr
            && *discr_place == assign.0
        {
            Some(targets.target_for_value(value))
        } else {
            None
        }
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
    if let StatementKind::Assign(assign) = &stmt.kind
        && let Rvalue::Use(Operand::Copy(op_place) | Operand::Move(op_place))
        | Rvalue::Ref(_, _, op_place)
        | Rvalue::CopyForDeref(op_place) = &assign.1
    {
        is_variant_downcast_to_ty_place(*op_place, place, variant_name, variant_idx, ty)
            .then_some(assign.0)
    } else {
        None
    }
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

/// Returns closure info if the given an arg operand represents a closure that captures some variables.
pub fn capturing_closure_info<'tcx, 'analysis>(
    arg: &Operand<'tcx>,
    basic_block: &'analysis BasicBlockData<'tcx>,
) -> Option<(
    DefId,
    &'analysis IndexVec<FieldIdx, Operand<'tcx>>,
    ClosureArgs<TyCtxt<'tcx>>,
)> {
    // A direct const operand indicates a non-capturing closure which requires no annotation.
    let arg_place = arg.place()?;
    basic_block.statements.iter().find_map(|stmt| {
        if let StatementKind::Assign(assign) = &stmt.kind {
            if assign.0 == arg_place {
                if let Rvalue::Aggregate(aggregate_kind, captured_locals) = &assign.1 {
                    if let AggregateKind::Closure(def_id, args) = **aggregate_kind {
                        return Some((def_id, captured_locals, ClosureArgs { args }));
                    }
                }
            }
        }
        None
    })
}

/// Returns `Place` for captured index given a closure args.
///
/// # Note
///
/// For closures captured locals are represented as projections (i.e. struct fields)
/// of the local with index 1.
pub fn captured_idx_to_place<'tcx>(
    idx: u32,
    args: ClosureArgs<TyCtxt<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> Place<'tcx> {
    let captured_local_ty = args.upvar_tys()[idx as usize];
    let captured_locals = Local::from_u32(1);
    let captured_locals_place = Place::from(captured_locals);
    let field_idx = FieldIdx::from_u32(idx);
    let projection = PlaceElem::Field(field_idx, captured_local_ty);
    tcx.mk_place_elem(captured_locals_place, projection)
}

/// Convenience alias for tracking invariant info.
pub type Invariant<'tcx> = (Location, CondOp, Place<'tcx>);

/// Collects collection length/size bound invariants and returned
/// `Option` or `Result` `unwrap`, `unwrap_or` or `unwrap_or_else` target info.
///
/// # Note
///
/// - For `unwrap_or`, the second arg must be a slice or collection length call for the subject place
///   or its `Deref` subject.
/// - For `unwrap_or_else`, the second arg must either be a closure that returns
///   a slice or collection length call for the subject place (or its `Deref` subject),
///   or for the case a `Result` type, an identity closure or function.
pub fn option_result_unwrap_analysis<'tcx>(
    unwrap_arg_place: Place<'tcx>,
    next_block: BasicBlock,
    subject_place: Place<'tcx>,
    subject_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<(FxHashSet<Invariant<'tcx>>, (Place<'tcx>, BasicBlock))> {
    // Tracks collection length/size bound invariants.
    let mut invariants = FxHashSet::default();
    let mut next_target_block = Some(next_block);
    let mut unwrap_place_info = None;
    let mut already_visited = FxHashSet::default();
    while let Some(block) = next_target_block
        && !already_visited.contains(&block)
    {
        let block_data = &basic_blocks[block];
        already_visited.insert(block);
        let terminator = block_data.terminator.as_ref()?;
        if let Some((unwrap_dest_place, post_unwrap_target)) =
            first_arg_transformer_call_destination(
                unwrap_arg_place,
                terminator,
                |crate_name, adt_name, fn_name| {
                    matches!(crate_name, "std" | "core")
                        && matches!(adt_name, "Option" | "Result")
                        && fn_name == "unwrap"
                },
                tcx,
            )
        {
            unwrap_place_info = Some((unwrap_dest_place, post_unwrap_target, CondOp::Lt));
            next_target_block = None;
        } else if let Some((unwrap_dest_place, post_unwrap_target)) =
            first_arg_transformer_call_destination(
                unwrap_arg_place,
                terminator,
                |crate_name, adt_name, fn_name| {
                    matches!(crate_name, "std" | "core")
                        && matches!(adt_name, "Option" | "Result")
                        && fn_name == "unwrap_or"
                },
                tcx,
            )
        {
            // Checks if the second `unwrap_or` arg is a slice or collection length call
            // for the subject place or its `Deref` subject.
            if let TerminatorKind::Call {
                args: unwrap_args, ..
            } = &terminator.kind
                && let Some(unwrap_second_arg) = unwrap_args.get(1)
                && let Some(unwrap_second_arg_place) = unwrap_second_arg.node.place()
                && (block_data.statements.iter().any(|stmt| {
                    is_subject_slice_len_metadata_assign(
                        unwrap_second_arg_place,
                        stmt,
                        block,
                        subject_place,
                        subject_block,
                        local_decls,
                        basic_blocks,
                        tcx,
                    )
                }) || pre_anchor_assign_terminator(
                    unwrap_second_arg_place,
                    block,
                    block,
                    basic_blocks,
                    basic_blocks.dominators(),
                )
                .is_some_and(|(assign_terminator, assign_block)| {
                    is_subject_collection_len_assign(
                        unwrap_second_arg_place,
                        &assign_terminator,
                        assign_block,
                        subject_place,
                        subject_block,
                        basic_blocks,
                        tcx,
                    )
                }))
            {
                unwrap_place_info = Some((unwrap_dest_place, post_unwrap_target, CondOp::Le));
            }
            next_target_block = None;
        } else if let Some((unwrap_dest_place, post_unwrap_target)) =
            first_arg_transformer_call_destination(
                unwrap_arg_place,
                terminator,
                |crate_name, adt_name, fn_name| {
                    matches!(crate_name, "std" | "core")
                        && matches!(adt_name, "Option" | "Result")
                        && fn_name == "unwrap_or_else"
                },
                tcx,
            )
        {
            // Checks that second arg is an identity function or closure and, if true,
            // returns unwrap destination place and next target.
            // See [`analyze::is_identity_fn`] and [`analyze::is_identity_closure`] for details.
            let is_result_and_identity = |operand: &Operand| {
                if let TyKind::Adt(adt_def, _) = unwrap_arg_place.ty(local_decls, tcx).ty.kind()
                    && let adt_def_id = adt_def.did()
                    && tcx.item_name(adt_def_id).as_str() == "Result"
                    && matches!(tcx.crate_name(adt_def_id.krate).as_str(), "std" | "core")
                {
                    is_identity_fn(operand, tcx) || is_identity_closure(operand, tcx)
                } else {
                    false
                }
            };
            if let TerminatorKind::Call {
                args: unwrap_args, ..
            } = &terminator.kind
                && let Some(unwrap_second_arg) = unwrap_args.get(1)
                && (is_result_and_identity(&unwrap_second_arg.node)
                    || is_subject_len_closure(
                        &unwrap_second_arg.node,
                        block,
                        subject_place,
                        subject_block,
                        basic_blocks,
                        tcx,
                    ))
            {
                unwrap_place_info = Some((unwrap_dest_place, post_unwrap_target, CondOp::Le));
            }
            next_target_block = None;
        } else {
            next_target_block = match &terminator.kind {
                TerminatorKind::Call {
                    args,
                    destination,
                    target,
                    ..
                } if *destination != unwrap_arg_place
                    && args.iter().all(|arg| {
                        arg.node
                            .place()
                            .is_none_or(|place| place != unwrap_arg_place)
                    }) =>
                {
                    *target
                }
                TerminatorKind::Drop { place, target, .. } if *place != unwrap_arg_place => {
                    Some(*target)
                }
                TerminatorKind::Goto { target }
                | TerminatorKind::Assert { target, .. }
                | TerminatorKind::FalseEdge {
                    real_target: target,
                    ..
                }
                | TerminatorKind::FalseUnwind {
                    real_target: target,
                    ..
                } => Some(*target),
                TerminatorKind::Yield {
                    value,
                    resume: target,
                    ..
                } if value.place().is_none_or(|place| place != unwrap_arg_place) => Some(*target),
                _ => None,
            };
        }
    }

    let (unwrap_dest_place, post_unwrap_target, cond_op) = unwrap_place_info?;
    let post_unwrap_target = post_unwrap_target?;

    // Declares collection length/size invariant for unwrap place.
    let annotation_location = Location {
        block: post_unwrap_target,
        statement_index: 0,
    };
    invariants.insert((annotation_location, cond_op, unwrap_dest_place));

    // Returns analysis results.
    Some((invariants, (unwrap_dest_place, post_unwrap_target)))
}

// Returns true if the given `place` is an alias of `subject` possibly via a shared deref subject.
fn is_subject_or_deref_alias<'tcx>(
    place: Place<'tcx>,
    block: BasicBlock,
    subject: Place<'tcx>,
    subject_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    if place == subject {
        return true;
    }

    let place_aliases = collect_place_aliases(place, &basic_blocks[block]);
    if place_aliases.contains(&subject) {
        return true;
    }

    let subject_aliases = collect_place_aliases(subject, &basic_blocks[subject_block]);
    if subject_aliases.contains(&place)
        || subject_aliases
            .iter()
            .any(|subject_alias| *subject_alias == place || place_aliases.contains(subject_alias))
    {
        return true;
    }

    // Collects all subject aliases (including `Deref` subjects and their aliases).
    let subject_deref_subjects = deref_subjects_recursive(
        subject,
        subject_block,
        subject_block,
        basic_blocks,
        basic_blocks.dominators(),
        tcx,
    );
    let all_subject_aliases: FxHashSet<_> = std::iter::once(subject)
        .chain(subject_aliases)
        .chain(
            subject_deref_subjects
                .iter()
                .map(|(deref_subject_place, _)| *deref_subject_place),
        )
        .chain(subject_deref_subjects.iter().flat_map(
            |(deref_subject_place, deref_subject_block)| {
                collect_place_aliases(*deref_subject_place, &basic_blocks[*deref_subject_block])
            },
        ))
        .collect();

    // Returns true if any place alias (including `Deref` subjects and their aliases) matches any subject alias.
    let place_deref_subjects = deref_subjects_recursive(
        place,
        block,
        block,
        basic_blocks,
        basic_blocks.dominators(),
        tcx,
    );
    let mut all_place_aliases = std::iter::once(place)
        .chain(place_aliases)
        .chain(
            place_deref_subjects
                .iter()
                .map(|(deref_subject_place, _)| *deref_subject_place),
        )
        .chain(place_deref_subjects.iter().flat_map(
            |(deref_subject_place, deref_subject_block)| {
                collect_place_aliases(*deref_subject_place, &basic_blocks[*deref_subject_block])
            },
        ));
    all_place_aliases.any(|place_alias| all_subject_aliases.contains(&place_alias))
}

/// Returns true if the operand is the const identity function (i.e. `std::convert::identity`).
///
/// Ref: <https://doc.rust-lang.org/std/convert/fn.identity.html>
fn is_identity_fn(operand: &Operand, tcx: TyCtxt) -> bool {
    operand.const_fn_def().is_some_and(|(def_id, ..)| {
        let fn_name = tcx.item_name(def_id);
        let crate_name = tcx.crate_name(def_id.krate);
        fn_name.as_str() == "identity" && matches!(crate_name.as_str(), "std" | "core")
    })
}

/// Returns true if the operand is an identity closure (i.e. `|x| x`).
fn is_identity_closure(operand: &Operand, tcx: TyCtxt) -> bool {
    if let Some(const_op) = operand.constant()
        && let TyKind::Closure(def_id, _) = const_op.const_.ty().kind()
        && let body = tcx.optimized_mir(def_id)
        && let blocks = &body.basic_blocks
        && blocks.len() == 1
        && let block_data = &blocks[blocks.start_node()]
        && let Some(terminator) = &block_data.terminator
        && terminator.kind == TerminatorKind::Return
        && let stmts = &block_data.statements
        && stmts.len() == 1
        && let Some(stmt) = stmts.first()
        && let StatementKind::Assign(assign) = &stmt.kind
        && assign.0.local == RETURN_PLACE
        && let Rvalue::Use(Operand::Copy(assign_rvalue_place) | Operand::Move(assign_rvalue_place)) =
            &assign.1
    {
        assign_rvalue_place.local.as_usize() <= body.arg_count
    } else {
        false
    }
}

/// Returns true if the operand is an len call for the given captured subject place (e.g. `|x| x.len()`).
fn is_subject_len_closure<'tcx>(
    operand: &Operand<'tcx>,
    block: BasicBlock,
    subject_place: Place<'tcx>,
    subject_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    let closure_info = capturing_closure_info(operand, &basic_blocks[block]);
    let Some((closure_def_id, captured_locals, closure_args)) = closure_info else {
        return false;
    };

    // Finds captured subject place.
    let captured_subject_idx = captured_locals
        .iter_enumerated()
        .find_map(|(idx, operand)| {
            let op_place = operand.place()?;
            is_subject_or_deref_alias(
                op_place,
                block,
                subject_place,
                subject_block,
                basic_blocks,
                tcx,
            )
            .then_some(idx)
        });
    let Some(captured_subject_idx) = captured_subject_idx else {
        return false;
    };
    let captured_subject_place =
        captured_idx_to_place(captured_subject_idx.as_u32(), closure_args, tcx);

    // Returns true if all return place assigns are subject len calls.
    let body = tcx.optimized_mir(closure_def_id);
    body.basic_blocks
        .iter_enumerated()
        .all(|(closure_block, closure_block_data)| {
            let terminator_is_valid =
                closure_block_data
                    .terminator
                    .as_ref()
                    .is_none_or(|terminator| {
                        if let TerminatorKind::Call { destination, .. } = &terminator.kind {
                            if destination.local == RETURN_PLACE {
                                is_subject_collection_len_assign(
                                    *destination,
                                    terminator,
                                    closure_block,
                                    captured_subject_place,
                                    closure_block,
                                    &body.basic_blocks,
                                    tcx,
                                )
                            } else {
                                // Call terminators that don't assign to the return are fine.
                                true
                            }
                        } else {
                            // All other terminators are fine.
                            true
                        }
                    });
            let all_stmts_are_valid = || {
                closure_block_data.statements.iter().all(|stmt| {
                    if let StatementKind::Assign(assign) = &stmt.kind {
                        if assign.0.local == RETURN_PLACE {
                            is_subject_slice_len_metadata_assign(
                                assign.0,
                                stmt,
                                closure_block,
                                captured_subject_place,
                                closure_block,
                                &body.local_decls,
                                &body.basic_blocks,
                                tcx,
                            )
                        } else {
                            // Statements that don't assign to the return are fine.
                            true
                        }
                    } else {
                        // All other statements are fine.
                        true
                    }
                })
            };
            terminator_is_valid && all_stmts_are_valid()
        })
}

/// Returns true if the statement assigns slice metadata of `subject_place`
/// (possibly via a shared deref subject) to the given `place`.
///
/// # Note
///
/// This accounts for multiple derefs (e.g. `BoundedVec` -> `Vec` -> `slice`).
#[allow(clippy::too_many_arguments)]
fn is_subject_slice_len_metadata_assign<'tcx>(
    place: Place<'tcx>,
    stmt: &Statement<'tcx>,
    block: BasicBlock,
    subject_place: Place<'tcx>,
    subject_block: BasicBlock,
    local_decls: &LocalDecls<'tcx>,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    if let StatementKind::Assign(assign) = &stmt.kind
        && assign.0 == place
        && let Rvalue::UnaryOp(UnOp::PtrMetadata, op) = &assign.1
        && op.ty(local_decls, tcx).peel_refs().is_slice()
        && let Some(op_place) = op.place()
    {
        is_subject_or_deref_alias(
            op_place,
            block,
            subject_place,
            subject_block,
            basic_blocks,
            tcx,
        )
    } else {
        false
    }
}

/// Returns true if the terminator assigns a collection len result of `subject_place`
/// (possibly via a shared deref subject) to the given `place`.
///
/// # Note
///
/// This accounts for multiple derefs (e.g. `BoundedVec` -> `Vec` -> `slice`).
fn is_subject_collection_len_assign<'tcx>(
    place: Place<'tcx>,
    terminator: &Terminator<'tcx>,
    block: BasicBlock,
    subject_place: Place<'tcx>,
    subject_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    if let TerminatorKind::Call {
        func,
        args,
        destination,
        ..
    } = &terminator.kind
        && *destination == place
        && args.len() == 1
        && let Some((def_id, _)) = func.const_fn_def()
        && let Some(fn_name) = tcx.opt_item_name(def_id)
        && fn_name.as_str() == "len"
        && let Some(len_arg) = args.first()
        && let Some(len_arg_place) = len_arg.node.place()
    {
        is_subject_or_deref_alias(
            len_arg_place,
            block,
            subject_place,
            subject_block,
            basic_blocks,
            tcx,
        )
    } else {
        false
    }
}
