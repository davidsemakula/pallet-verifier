//! Common utilities and helpers for analyses related to FRAME storage items.

use rustc_ast::Mutability;
use rustc_data_structures::graph::{dominators::Dominators, iterate::post_order_from};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::LangItem;
use rustc_middle::{
    mir::{
        visit::Visitor, BasicBlock, BasicBlockData, BasicBlocks, Body, HasLocalDecls, LocalDecls,
        Location, Operand, Place, Rvalue, StatementKind, Terminator, TerminatorKind,
    },
    ty::{
        AssocItemContainer, GenericArg, ImplSubject, List, Region, RegionKind, Ty, TyCtxt, TyKind,
    },
};
use rustc_mir_dataflow::{
    impls::{MaybeBorrowedLocals, MaybeLiveLocals},
    Analysis,
};
use rustc_span::def_id::DefId;
use rustc_target::abi::FieldIdx;

use itertools::Itertools;
use serde::{Deserialize, Serialize};

use crate::{
    providers::{
        analyze::{self, SwitchVariant},
        annotate::{Annotation, CondOp},
        closure::{self, ClosureInvariantEnv, ClosureInvariantInfo, ClosurePlaceIdx},
    },
    utils,
};

/// FRAME storage item info.
#[derive(Debug, Clone, Copy)]
pub struct StorageItem<'tcx> {
    /// Storage item type (i.e. the `#[pallet::storage]` annotated type alias).
    pub ty: Ty<'tcx>,
    /// `DefId` of storage prefix
    /// (i.e. the generated `_GeneratedPrefixForStorage<Name>` named struct,
    /// where `<Name>` is the name of the `#[pallet::storage]` annotated type alias).
    pub prefix: DefId,
    /// Underlying storage value type (e.g. `Vec<u8>` in `StorageValue<_, Vec<u8>, ValueQuery>`).
    pub value_ty: Ty<'tcx>,
    /// Generic args of the storage item type.
    pub args: &'tcx List<GenericArg<'tcx>>,
}

/// FRAME storage related invariants.
pub type StorageInvariant<'tcx> = (
    StorageId,
    BasicBlock,
    FxHashSet<(Location, CondOp, Place<'tcx>)>,
);

/// Identifier for storage item.
pub enum StorageId {
    /// `DefId` of generated storage item.
    ///
    /// (i.e. [`StorageItem::prefix`])
    DefId(DefId),
    /// String representation of the `DefPathHash` for the above `DefId`.
    ///
    /// See [`utils::def_hash_str`].
    DefHash(String),
}

impl StorageId {
    /// Returns a string representation of the `DefPathHash` of the storage id.
    ///
    /// See [`utils::def_hash_str`] for details.
    pub fn as_hash(&self, tcx: TyCtxt) -> String {
        match self {
            StorageId::DefId(def_id) => utils::def_hash_str(*def_id, tcx),
            StorageId::DefHash(hash) => hash.to_string(),
        }
    }
}

/// Returns info about the FRAME storage item from which the given place is derived (if any).
///
/// See [`StorageItem`].
pub fn storage_subject<'tcx>(
    place: Place<'tcx>,
    parent_block: BasicBlock,
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    dominators: &Dominators<BasicBlock>,
    tcx: TyCtxt<'tcx>,
) -> Option<(StorageItem<'tcx>, BasicBlock)> {
    // Finds innermost (un-derefed) place and it's parent block.
    let mut derefed_target_place = place;
    let mut derefed_target_block = parent_block;
    while let Some((derefed_place, bb)) = analyze::deref_subject(
        derefed_target_place,
        parent_block,
        anchor_block,
        basic_blocks,
        dominators,
        tcx,
    ) {
        derefed_target_place = derefed_place;
        derefed_target_block = bb;
    }

    // Finds FRAME storage subject (if any).
    let (terminator, call_bb) = analyze::pre_anchor_assign_terminator(
        derefed_target_place,
        derefed_target_block,
        anchor_block,
        basic_blocks,
        dominators,
    )?;
    storage_item(&terminator, tcx).map(|storage_item| (storage_item, call_bb))
}

/// Returns info about the FRAME storage item (if any) for which the given `Terminator` call is
/// an associated fn.
///
/// See [`StorageItem`].
fn storage_item<'tcx>(
    terminator: &Terminator<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<StorageItem<'tcx>> {
    let TerminatorKind::Call { func, .. } = &terminator.kind else {
        return None;
    };
    let (fn_def_id, fn_gen_args) = func.const_fn_def()?;
    if tcx.crate_name(fn_def_id.krate).as_str() != "frame_support" {
        return None;
    }

    let assoc_item = tcx.opt_associated_item(fn_def_id)?;
    let (call_gen_args, self_ty) = match assoc_item.container {
        AssocItemContainer::ImplContainer => {
            let impl_def_id = tcx.impl_of_method(fn_def_id)?;
            let impl_subject = tcx.impl_subject(impl_def_id).instantiate(tcx, fn_gen_args);
            let ImplSubject::Inherent(self_ty) = impl_subject else {
                return None;
            };
            (fn_gen_args, self_ty)
        }
        AssocItemContainer::TraitContainer => {
            let trait_def_id = assoc_item.container_id(tcx);
            let is_frame_storage_trait = tcx.crate_name(trait_def_id.krate).as_str()
                == "frame_support"
                && tcx.item_name(trait_def_id).as_str().contains("Storage");
            if !is_frame_storage_trait {
                return None;
            }
            let arg_ty = first_ty_arg(fn_gen_args)?;
            let TyKind::Adt(_, adt_gen_args) = arg_ty.kind() else {
                return None;
            };
            (*adt_gen_args, arg_ty)
        }
    };

    let prefix_ty_def_id = first_ty_arg(call_gen_args)?.ty_adt_def()?.did();
    if !utils::is_storage_prefix(prefix_ty_def_id, tcx)
        || !utils::includes_query_type(call_gen_args, tcx)
    {
        return None;
    }
    let self_def_id = self_ty.ty_adt_def()?.did();
    let is_frame_storage_type = tcx.crate_name(self_def_id.krate).as_str() == "frame_support"
        && tcx.item_name(self_def_id).as_str().starts_with("Storage");
    if !is_frame_storage_type {
        return None;
    }
    let self_ty_generics = tcx.generics_of(self_def_id);
    let value_param_def = self_ty_generics
        .params
        .iter()
        .find(|param| param.name.as_str() == "Value")?;
    let value_ty = call_gen_args
        .iter()
        .nth(value_param_def.index as usize)?
        .as_type()?;
    Some(StorageItem {
        ty: self_ty,
        prefix: prefix_ty_def_id,
        value_ty,
        args: call_gen_args,
    })
}

/// Propagates storage related invariants.
pub fn propagate_invariants<'tcx>(
    storage_invariants: Vec<StorageInvariant<'tcx>>,
    annotations: &mut Vec<Annotation<'tcx>>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) {
    // Tracks propagated storage related invariants for closures.
    let mut closure_invariants_map: FxHashMap<DefId, FxHashSet<ClosureInvariantInfo>> =
        FxHashMap::default();

    // Collects storage type associated function calls.
    let mut storage_visitor = StorageCallVisitor::new(tcx);
    storage_visitor.visit_body(body);

    // Performs live-variable and borrowed-variable dataflow analyses.
    // Ref: <https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_dataflow/impls/struct.MaybeLiveLocals.html>
    // Ref: <https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_dataflow/impls/struct.MaybeBorrowedLocals.html>
    let mut live_locals = MaybeLiveLocals
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);
    let mut borrowed_locals = MaybeBorrowedLocals
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

    // Propagates storage invariants (if necessary).
    let basic_blocks = &body.basic_blocks;
    let dominators = basic_blocks.dominators();
    for (storage_id, use_location, invariants) in storage_invariants {
        // Retreives calls for storage type.
        let Some((storage_item, storage_calls)) =
            storage_visitor.calls.get(&storage_id.as_hash(tcx))
        else {
            continue;
        };

        // Filters out only storage calls dominated by the invariant block and sorts them by block/location.
        let dominated_storage_calls = storage_calls
            .iter()
            .filter(|(_, block)| {
                *block != use_location && dominators.dominates(use_location, *block)
            })
            .sorted_by(|(_, a), (_, b)| a.cmp(b));

        // Tracks calls that can mutate the storage value
        // (used to disable propagation of invariants for successors).
        let mut mutable_call_locations: FxHashMap<BasicBlock, Vec<BasicBlock>> =
            FxHashMap::default();

        for (terminator, block) in dominated_storage_calls {
            // Don't propagate invariant if the current call is downstream from a
            // intermediate storage call than can (possibly) mutate the storage value.
            let is_possibly_mutated_by_predecessor = mutable_call_locations
                .iter()
                .any(|(_, successors)| successors.contains(block));
            if is_possibly_mutated_by_predecessor {
                continue;
            }

            // Update mutable call locations if current call can mutate the storage value.
            if !is_idempotent_call(terminator, storage_item, tcx) {
                // We eagerly compute successors as it's cheaper than the worst case of computing
                // them in a loop when evaluating successor calls.
                let successors = post_order_from(basic_blocks, *block);
                mutable_call_locations.insert(*block, successors);
            }

            // Retrieves dataflow states at entry of storage call block.
            live_locals.seek_to_block_start(*block);
            borrowed_locals.seek_to_block_start(*block);
            let live_domain = live_locals.get();
            let borrowed_domain = borrowed_locals.get();

            // Progagates each storage invariant if the target invariant place
            // is either live or borrowed and the target call uses the storage value type.
            for (annotation_location, cond_op, invariant_place) in &invariants {
                // Finds the live or borrowed invariant propagation place.
                let is_live_or_borrowed = live_domain.contains(invariant_place.local)
                    || borrowed_domain.contains(invariant_place.local);
                let invariant_prop_place =
                    is_live_or_borrowed.then_some(*invariant_place).or_else(|| {
                        // TODO: Remove this aliasing logic when SSA optimizations are enabled
                        // (e.g. unification of locals that copy each other - i.e copy prop).
                        body.basic_blocks[annotation_location.block]
                            .statements
                            .iter()
                            .find_map(|stmt| {
                                if let StatementKind::Assign(assign) = &stmt.kind {
                                    if let Rvalue::Use(
                                        Operand::Copy(op_place) | Operand::Move(op_place),
                                    ) = assign.1
                                    {
                                        let assign_place = assign.0;
                                        if op_place == *invariant_place {
                                            let is_live_or_borrowed = live_domain
                                                .contains(assign_place.local)
                                                || borrowed_domain.contains(assign_place.local);
                                            return is_live_or_borrowed.then_some(assign_place);
                                        }
                                    }
                                }
                                None
                            })
                    });
                let Some(invariant_prop_place) = invariant_prop_place else {
                    continue;
                };

                // Finds propagated invariants for closure arguments (if appropriate).
                let closure_invariant_info = propagate_closure_arg_invariant(
                    invariant_prop_place,
                    storage_item.value_ty,
                    terminator,
                    &body.basic_blocks[*block],
                    tcx,
                );
                if let Some((closure_def_id, storage_value_arg_index, captured_invariant_idx)) =
                    closure_invariant_info
                {
                    let invariant_info = (
                        *cond_op,
                        ClosurePlaceIdx::new_capture(captured_invariant_idx.as_u32()),
                        ClosurePlaceIdx::new_arg(storage_value_arg_index),
                    );
                    match closure_invariants_map.get_mut(&closure_def_id) {
                        Some(closure_invariants) => {
                            closure_invariants.insert(invariant_info);
                        }
                        None => {
                            let mut closure_invariants = FxHashSet::default();
                            closure_invariants.insert(invariant_info);
                            closure_invariants_map.insert(closure_def_id, closure_invariants);
                        }
                    };
                }

                // Finds propagated invariants for storage value type return place (if any).
                if closure_invariant_info.is_none() {
                    propagate_return_place_invariant(
                        invariant_prop_place,
                        *cond_op,
                        storage_item.value_ty,
                        terminator,
                        *block,
                        &body.basic_blocks,
                        body.local_decls(),
                        tcx,
                        annotations,
                    );
                }
            }
        }
    }

    // Applies propagated storage related invariants for closures.
    for (closure_def_id, invariants) in closure_invariants_map {
        // Sets propagated invariant environment for closure.
        let closure_invariant_env = ClosureInvariantEnv::new(closure_def_id, invariants, tcx);
        closure::set_invariant_env(&closure_invariant_env);

        // Composes closure MIR (with propagated invariant environment set).
        let _ = tcx.optimized_mir(closure_def_id);
    }
}

/// Returns info needed to propagate a storage related invariant to a closure that's an argument of
/// a storage call.
///
/// i.e. returns a tuple of the closure's `DefId`, the index of the storage value type arg
/// and the `FieldIdx` of the captured place for the invariant (which may be a reference or copy).
fn propagate_closure_arg_invariant<'tcx>(
    invariant_place: Place<'tcx>,
    // Storage value type.
    value_ty: Ty<'tcx>,
    // Storage call.
    terminator: &Terminator<'tcx>,
    basic_block: &BasicBlockData<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<(DefId, usize, FieldIdx)> {
    // Finds a closure arg (if any) which has a storage value type arg and also captures some locals.
    let TerminatorKind::Call { args, .. } = &terminator.kind else {
        return None;
    };
    let (closure_def_id, captured_locals, storage_value_arg_idx) = args.iter().find_map(|arg| {
        // Find capturing closure info (if any).
        let (closure_def_id, captured_locals, closure_args) =
            closure::capturing_closure_info(&arg.node, basic_block)?;

        // Extracts the "real" (i.e. user-supplied) closure args.
        // Ref: <https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.ClosureArgs.html>
        // Ref: <https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.ClosureArgsParts.html#structfield.closure_sig_as_fn_ptr_ty>
        let closure_args_tuple = closure_args.sig().inputs().skip_binder().first()?;
        let TyKind::Tuple(closure_arg_tys) = closure_args_tuple.kind() else {
            return None;
        };

        // Finds storage value type arg (including refs and `Option<T>` and `Result<T>` wrappers).
        let storage_value_arg_idx = closure_arg_tys.iter().enumerate().find_map(|(idx, ty)| {
            // NOTE: This assumes that closure args are already normalized.
            let is_storage_value_type = ty == value_ty
                || ty.peel_refs() == value_ty
                || is_option_or_result_ty(ty, value_ty, tcx);
            is_storage_value_type.then_some(idx)
        })?;

        // Returns closure info.
        Some((closure_def_id, captured_locals, storage_value_arg_idx))
    })?;

    // Finds captured invariant place (if any).
    let captured_invariant_idx = captured_locals
        .iter_enumerated()
        .find_map(|(idx, operand)| {
            operand.place().and_then(|op_place| {
                (op_place == invariant_place).then_some(idx).or_else(|| {
                    // Handles aliased captures.
                    basic_block
                        .statements
                        .iter()
                        .find_map(|stmt| match &stmt.kind {
                            StatementKind::Assign(assign) if op_place == assign.0 => {
                                let src_place = match assign.1 {
                                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
                                        Some(place)
                                    }
                                    Rvalue::Ref(_, _, place) => Some(place),
                                    _ => None,
                                }?;
                                (src_place == invariant_place).then_some(idx)
                            }
                            _ => None,
                        })
                })
            })
        })?;

    // Returns closure propagation info.
    Some((
        closure_def_id,
        storage_value_arg_idx,
        captured_invariant_idx,
    ))
}

/// Adds return place annotations (if appropriate) for propagated storage related invariants.
#[allow(clippy::too_many_arguments)]
fn propagate_return_place_invariant<'tcx>(
    invariant_place: Place<'tcx>,
    cond_op: CondOp,
    // Storage value type.
    value_ty: Ty<'tcx>,
    // Storage call.
    terminator: &Terminator<'tcx>,
    // Storage call block.
    block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    tcx: TyCtxt<'tcx>,
    annotations: &mut Vec<Annotation<'tcx>>,
) {
    // Only propapages invariant to return place if the storage value type is not used in any params.
    let TerminatorKind::Call {
        func,
        destination,
        target,
        ..
    } = &terminator.kind
    else {
        return;
    };
    let Some((def_id, gen_args)) = func.const_fn_def() else {
        return;
    };
    let fn_sig = tcx.fn_sig(def_id).instantiate(tcx, gen_args).skip_binder();
    // NOTE: This also walks closure args, see `is_ty_or_ty_arg` for details.
    let is_storage_type_in_params = fn_sig
        .inputs()
        .iter()
        .any(|ty| is_ty_or_ty_arg(*ty, value_ty));
    if is_storage_type_in_params {
        return;
    }

    // Handles T and &T return places where T is the storage value type.
    // NOTE: We use the place type instead of the output type from the function signature because
    // the former is already normalized while the latter isn't.
    let return_ty = destination.ty(local_decls, tcx).ty;
    let region = match return_ty.kind() {
        TyKind::Ref(region, _, _) => *region,
        _ => Region::new_from_kind(tcx, RegionKind::ReErased),
    };
    let Some(target) = *target else {
        return;
    };
    if return_ty == value_ty || return_ty.peel_refs() == value_ty {
        let annotation_location = Location {
            block: target,
            statement_index: 0,
        };
        let Some(len_call_info) = analyze::collection_len_call(return_ty, tcx) else {
            return;
        };
        annotations.push(Annotation::Len(
            annotation_location,
            cond_op,
            invariant_place,
            *destination,
            region,
            len_call_info.clone(),
        ));
        return;
    }

    // Handles `Option<T>` and `Result<T>` return places where T is the storage value type.
    // NOTE: `is_option_ty` and `is_result_ty` also match references.
    let mut switch_target_variant = if is_option_ty(return_ty, value_ty, tcx) {
        SwitchVariant::OptionSome
    } else if is_result_ty(return_ty, value_ty, tcx) {
        SwitchVariant::ResultOk
    } else {
        return;
    };
    // Finds wrapped storage value like type (e.g. the type or a reference to the type).
    let TyKind::Adt(_, gen_args) = return_ty.peel_refs().kind() else {
        unreachable!("Expected `Option` or `Result` struct");
    };
    let Some(downcast_ty) = first_ty_arg(gen_args) else {
        unreachable!("Expected `Option` or `Result` struct generic type param");
    };

    // Collects `Option::Some` or `Result::Ok` (or equivalent safe transformation) target blocks
    // for switches based on the discriminant of destination of in successor blocks.
    let mut switch_target_place = *destination;
    let mut switch_target_block = block;
    analyze::track_safe_primary_opt_result_variant_transformations(
        &mut switch_target_place,
        &mut switch_target_block,
        &mut switch_target_variant,
        target,
        basic_blocks,
        tcx,
    );
    let switch_targets = analyze::collect_switch_targets_for_discr_value(
        switch_target_place,
        switch_target_variant.idx(tcx).as_u32() as u128,
        block,
        basic_blocks,
    );

    // Adds annotations for propagated invariants for variant downcast to `downcast_ty` places (if any)
    // for the switch targets.
    let mut invariants = Vec::new();
    let Some(len_call_info) = analyze::collection_len_call(downcast_ty, tcx) else {
        return;
    };
    for target_bb in switch_targets {
        for (stmt_idx, stmt) in basic_blocks[target_bb].statements.iter().enumerate() {
            // Finds variant downcast to `downcast_ty` places (if any) for the switch target variant.
            let Some(downcast_place) = analyze::variant_downcast_to_ty_place(
                switch_target_place,
                switch_target_variant.name(),
                switch_target_variant.idx(tcx),
                downcast_ty,
                stmt,
            ) else {
                continue;
            };

            // Declares propagated invariant.
            let annotation_location = Location {
                block: target_bb,
                statement_index: stmt_idx + 1,
            };
            invariants.push((annotation_location, downcast_place));
            annotations.push(Annotation::Len(
                annotation_location,
                cond_op,
                invariant_place,
                downcast_place,
                region,
                len_call_info.clone(),
            ));
        }
    }
}

/// Env var for tracking propagated return place storage invariant.
pub const ENV_STORAGE_INVARIANT_PREFIX: &str = "PALLET_VERIFIER_STORAGE_INVARIANT";

/// Info needed to apply propagated return place storage invariants.
#[derive(Debug, Serialize, Deserialize)]
pub struct StorageInvariantEnv {
    pub call_def_hash: String,
    pub storage_def_hash: String,
    pub source: InvariantSource,
    pub propagated_variant: PropagatedVariant,
}

impl StorageInvariantEnv {
    /// Create new storage invariant environment.
    pub fn new(
        call_def_id: DefId,
        storage_def_hash: String,
        source: InvariantSource,
        propagated_variant: PropagatedVariant,
        tcx: TyCtxt,
    ) -> Self {
        Self {
            call_def_hash: utils::def_hash_str(call_def_id, tcx),
            storage_def_hash,
            propagated_variant,
            source,
        }
    }

    /// Create new storage invariant environment.
    pub fn new_with_id(
        call_def_id: DefId,
        storage_id: StorageId,
        source: InvariantSource,
        propagated_variant: PropagatedVariant,
        tcx: TyCtxt,
    ) -> Self {
        Self::new(
            call_def_id,
            storage_id.as_hash(tcx),
            source,
            propagated_variant,
            tcx,
        )
    }
}

/// A propagated return place variant of `Result` or `Option` type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PropagatedVariant {
    /// `Option::Some` or `Result::Ok` (or a "safe" transformation from either).
    Primary(SwitchVariant),
    /// `Option::None` or `Result::Err` (or a "safe" transformation from either).
    Alt(SwitchVariant),
    /// An undetermined variant for a `Result` or `Option` type (or a "safe" transformation from either).
    ///
    /// NOTE: This is equivalent to the `TOP` abstract value.
    Unknown(SwitchVariant, SwitchVariant),
    /// A unification of variants (e.g. with `Result::unwrap_or_else`).
    ///
    /// **NOTE:** This is NOT equivalent to the `TOP` abstract value because it's an "unwrapped" value.
    Union,
}

impl PropagatedVariant {
    pub fn as_switch_variant(&self) -> Option<SwitchVariant> {
        match self {
            PropagatedVariant::Primary(switch_variant) | PropagatedVariant::Alt(switch_variant) => {
                Some(*switch_variant)
            }
            PropagatedVariant::Unknown(_, _) | PropagatedVariant::Union => None,
        }
    }
}

/// Source operation for the propagated invariant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum InvariantSource {
    /// `[T]::binary_search*` methods.
    SliceBinarySearch,
    /// `Iterator::position` and `Iterator::position` methods.
    IteratorPosition,
}

// Sets propagated storage invariant environment.
pub fn set_invariant_env(invariant_env: &StorageInvariantEnv) {
    let invariant_env_json =
        serde_json::to_string(invariant_env).expect("Expected serialized `StorageInvariantEnv`");
    // SAFETY: `pallet-verifier` is single-threaded.
    let env_key = call_propagation_env_key(&invariant_env.call_def_hash);
    std::env::set_var(env_key, invariant_env_json);
}

/// Retrieves the propagated storage invariant environment (if any).
pub fn find_invariant_env(def_id: DefId, tcx: TyCtxt) -> Option<StorageInvariantEnv> {
    // SAFETY: `pallet-verifier` is single-threaded.
    let hash = utils::def_hash_str(def_id, tcx);
    let env_key = call_propagation_env_key(&hash);
    let invariant_env_json = std::env::var(env_key).ok()?;
    let invariant_env: StorageInvariantEnv = serde_json::from_str(&invariant_env_json).ok()?;
    (invariant_env.call_def_hash == hash).then_some(invariant_env)
}

/// Returns a env key for the given def hash.
fn call_propagation_env_key(def_hash: &str) -> String {
    format!("{ENV_STORAGE_INVARIANT_PREFIX}_{def_hash}")
}

/// Composes a boolean condition for checking if any of the `$needle` word stems is present
/// in the `$haystack` expression.
macro_rules! contains_word_stem {
    ($haystack: expr, $first_needle: literal $(, $other_needle: literal)+) => {
        (
            contains_word_stem!($haystack, $first_needle)
            $(|| contains_word_stem!($haystack, $other_needle))+
        )
    };
    ($haystack: expr, $needle: literal) => {
        (
            $haystack == $needle ||
            $haystack.starts_with(concat!($needle, "_")) ||
            $haystack.ends_with(concat!("_", $needle)) ||
            $haystack.contains(concat!("_", $needle, "_"))
        )
    };
}

/// Returns true if the call is (likely) idempotent with regards to the storage value.
///
/// (i.e. storage invariants are preserved before and after the call).
///
/// **NOTE:** This is implemented as a heuristic analyzing the storage call signature
/// for light coupling with current storage type implementations
/// and possible use with custom storage types.
///
/// **NOTE:** This function assumes the given `Terminator` represents a FRAME storage call
/// but doesn't verify it.
fn is_idempotent_call<'tcx>(
    terminator: &Terminator<'tcx>,
    storage_item: &StorageItem<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    let TerminatorKind::Call { func, .. } = &terminator.kind else {
        return false;
    };
    let Some((def_id, gen_args)) = func.const_fn_def() else {
        return false;
    };
    let fn_sig = tcx.fn_sig(def_id).instantiate(tcx, gen_args).skip_binder();
    let param_tys = fn_sig.inputs();
    let ret_ty = fn_sig.output();

    // No params and a unit or never return type is typically a signature of a destructive operation
    // (e.g. `kill`, `clear` e.t.c).
    if param_tys.is_empty() && (ret_ty.is_unit() || ret_ty.is_never()) {
        return false;
    }

    // Some notable traits are known to have only idempotent assoc fns
    // (e.g. `StorageInfoTrait`, `PartialStorageInfoTrait` and `StorageEntryMetadataBuilder`).
    // Ref: <https://docs.rs/frame-support/latest/frame_support/traits/trait.StorageInfoTrait.html>
    // Ref: <https://docs.rs/frame-support/latest/frame_support/traits/trait.PartialStorageInfoTrait.html>
    // Ref: <https://docs.rs/frame-support/latest/frame_support/storage/types/trait.StorageEntryMetadataBuilder.html>
    let assoc_item = tcx.opt_associated_item(def_id);
    let is_notable_idempotent_trait_fn = assoc_item
        .and_then(|assoc_item| assoc_item.trait_container(tcx))
        .is_some_and(|trait_def_id| {
            let crate_name = tcx.crate_name(trait_def_id.krate);
            let trait_name = tcx.item_name(trait_def_id);
            crate_name.as_str() == "frame_support"
                && matches!(
                    trait_name.as_str(),
                    "StorageInfoTrait" | "PartialStorageInfoTrait" | "StorageEntryMetadataBuilder"
                )
        });
    if is_notable_idempotent_trait_fn {
        return true;
    }

    // A return type including the storage value type for a function whose name includes
    // a "reading related" word stem (e.g. `get`, `read`) is typically a read-only operation.
    //
    // NOTE: We don't include FRAME storage iterators (e.g. `PrefixIterator`, `KeyPrefixIterator`)
    // because:
    // - They can be converted to mutating/draining iterators with using a `drain` method.
    // - The underlying storage values can be altered during iteration (even if this is discouraged
    //   and considered undefined behaviour).
    // Ref: <https://docs.rs/frame-support/latest/frame_support/storage/struct.PrefixIterator.html#method.drain>
    // Ref: <https://docs.rs/frame-support/latest/frame_support/storage/struct.KeyPrefixIterator.html#method.drain>
    // Ref: <https://docs.rs/frame-support/latest/frame_support/storage/types/struct.StorageMap.html#method.iter>
    let fn_name = tcx.item_name(def_id);
    if contains_word_stem!(fn_name.as_str(), "get", "read")
        && is_ty_or_ty_arg(ret_ty, storage_item.value_ty)
    {
        return true;
    }

    // A `bool` return type with either no params or no storage value type in its params,
    // is typically an existence check (e.g. `exists`, `contains` e.t.c).
    // However, we also look for "existential check" related words
    // (e.g. `exists`, `contains`, `find` e.t.c) for robustness in case of a non-empty param set.
    // NOTE: `is_storage_type_in_params` is eagerly evaluated as it likely to be reused by
    // subsequent branch conditions (i.e. is a hot path).
    let is_storage_type_in_params = param_tys
        .iter()
        .any(|ty| is_ty_or_ty_arg(*ty, storage_item.value_ty));
    if ret_ty.is_bool()
        && (param_tys.is_empty()
            || (!is_storage_type_in_params
                && contains_word_stem!(fn_name.as_str(), "exists", "contains", "find", "any")))
    {
        return true;
    }

    // A `usize`, `Option<usize>` or `Result<usize>` return type for a function whose name includes
    // a "length/size related" word stem (e.g. `len`, `size` e.t.c) is typically
    // a length/size read-only operation.
    // However, we also check that if any params are passed, then no storage value type
    // is included in the params.
    let is_usize_like_ret_ty =
        ret_ty == tcx.types.usize || is_option_or_result_ty(ret_ty, tcx.types.usize, tcx);
    if is_usize_like_ret_ty
        && contains_word_stem!(fn_name.as_str(), "len", "size", "length")
        && (param_tys.is_empty() || !is_storage_type_in_params)
    {
        return true;
    }

    // A byte array, vec or slice (i.e. `[u8: N]`, `Vec<u8>` or `&[u8]`) return type for a function
    // whose name includes both "key" and either "hashed" or "final" word stems (e.g. `hashed_key` e.t.c)
    // is typically a read-only storage key retrieval operation.
    // However, we also check that if any params are passed, then no storage value type
    // is included in the params.
    let is_byte_array_vec_or_slice_ret_ty = match ret_ty.kind() {
        TyKind::Array(ty, _) => *ty == tcx.types.u8,
        TyKind::Adt(adt_def, gen_args) => {
            let adt_def_id = adt_def.did();
            let crate_name = tcx.crate_name(adt_def_id.krate);
            let name = tcx.item_name(adt_def_id);
            if name.as_str() == "Vec" && matches!(crate_name.as_str(), "std" | "alloc") {
                let gen_ty = gen_args.iter().filter_map(|arg| arg.as_type()).next();
                gen_ty.is_some_and(|ty| ty == tcx.types.u8)
            } else {
                false
            }
        }
        TyKind::Ref(_, ty, Mutability::Not) => {
            if let TyKind::Slice(ty) = ty.kind() {
                *ty == tcx.types.u8
            } else {
                false
            }
        }
        _ => false,
    };
    if is_byte_array_vec_or_slice_ret_ty
        && contains_word_stem!(fn_name.as_str(), "key")
        && (contains_word_stem!(fn_name.as_str(), "hashed")
            || contains_word_stem!(fn_name.as_str(), "final"))
        && (param_tys.is_empty() || !is_storage_type_in_params)
    {
        return true;
    }

    // No params and a byte array, vec or slice (i.e. `[u8: N]`, `Vec<u8>` or `&[u8]`) return type
    // for a function whose name includes the word stem "prefix"
    // (e.g. `pallet_prefix`, `storage_prefix`, `final_prefix` e.t.c)
    // is typically a read-only "prefix" retrieval operation.
    if param_tys.is_empty()
        && is_byte_array_vec_or_slice_ret_ty
        && contains_word_stem!(fn_name.as_str(), "prefix")
    {
        return true;
    }

    // Default assumption is false.
    false
}

/// Returns true if `ty` is `inner_ty` or `inner_ty` as some kind of argument `ty`.
///
/// **NOTE:** This function simply "walks" `ty` and compares all the inner types to `inner_ty`,
/// so it also handles cases where `ty` is a closure or fn def type and `inner_ty` is an args.
fn is_ty_or_ty_arg<'tcx>(ty: Ty<'tcx>, inner_ty: Ty<'tcx>) -> bool {
    ty.walk()
        .any(|ty| ty.as_type().is_some_and(|ty| ty == inner_ty))
}

/// Returns true if the given `ty` is either `Option<T>` or `Result<T>`
/// where T is the given `inner_ty`.
fn is_option_or_result_ty<'tcx>(ty: Ty<'tcx>, inner_ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    is_option_ty(ty, inner_ty, tcx) || is_result_ty(ty, inner_ty, tcx)
}

/// Returns true if the given `ty` is `Option<T>` where T is the given `inner_ty`.
fn is_option_ty<'tcx>(ty: Ty<'tcx>, inner_ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let def_id = tcx
        .lang_items()
        .get(LangItem::Option)
        .expect("Expected `Option` lang item");
    is_adt_with_generic_type_param(ty, def_id, inner_ty)
}

/// Returns true if the given `ty` is `Result<T>` where T is the given `inner_ty`.
fn is_result_ty<'tcx>(ty: Ty<'tcx>, inner_ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let def_id = tcx
        .lang_items()
        .get(LangItem::Option)
        .expect("Expected `Result` lang item");
    is_adt_with_generic_type_param(ty, def_id, inner_ty)
}

/// Returns true if the given `ty` is an ADT with the given `DefId` and has an `inner_ty`
/// as a generic type param.
fn is_adt_with_generic_type_param<'tcx>(ty: Ty<'tcx>, def_id: DefId, inner_ty: Ty<'tcx>) -> bool {
    match ty.peel_refs().kind() {
        TyKind::Adt(adt_def, gen_args) => {
            if adt_def.did() == def_id {
                gen_args.iter().any(|arg| {
                    arg.as_type()
                        .is_some_and(|ty| ty == inner_ty || ty.peel_refs() == inner_ty)
                })
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Returns the type of the first type arg in the generic arg list.
fn first_ty_arg<'tcx>(gen_args: &List<GenericArg<'tcx>>) -> Option<Ty<'tcx>> {
    gen_args.iter().filter_map(GenericArg::as_type).next()
}

/// Collects storage type associated function calls.
pub struct StorageCallVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// A map of storage type `DefId` to associated function calls.
    pub calls: FxHashMap<String, (StorageItem<'tcx>, Vec<(Terminator<'tcx>, BasicBlock)>)>,
}

impl<'tcx> StorageCallVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            calls: FxHashMap::default(),
        }
    }

    /// Collects storage item associated function calls.
    fn process_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        let Some(storage_item) = storage_item(terminator, self.tcx) else {
            return;
        };
        let hash = utils::def_hash_str(storage_item.prefix, self.tcx);
        let call_info = (terminator.clone(), location.block);
        match self.calls.get_mut(&hash) {
            Some((_, calls)) => {
                calls.push(call_info);
            }
            None => {
                self.calls.insert(hash, (storage_item, vec![call_info]));
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for StorageCallVisitor<'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.process_terminator(terminator, location);
        self.super_terminator(terminator, location);
    }
}
