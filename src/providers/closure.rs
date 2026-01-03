//! Common utilities and helpers for analyzing and annotating closures.

use rustc_abi::FieldIdx;
use rustc_hash::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, BasicBlockData, BasicBlocks, Body, HasLocalDecls, Local,
        LocalDecl, Location, Operand, Place, PlaceElem, Rvalue, Statement, StatementKind,
        TerminatorKind,
    },
    ty::{ClosureArgs, ImplSubject, Region, RegionKind, TyCtxt, TyKind},
};

use serde::{Deserialize, Serialize};

use crate::{
    providers::{
        analyze,
        annotate::{Annotation, CondOp},
    },
    utils,
};

/// Env var for tracking propagated invariant environment for closure.
const ENV_CLOSURE_INVARIANT_PREFIX: &str = "PALLET_VERIFIER_CLOSURE_INVARIANT";

/// Info needed to apply propagated invariants to a closure's MIR.
#[derive(Debug, Serialize, Deserialize)]
pub struct ClosureInvariantEnv {
    pub def_hash: String,
    pub invariants: FxHashSet<ClosureInvariantInfo>,
}

impl ClosureInvariantEnv {
    /// Create new closure invariant environment.
    pub fn new(def_id: DefId, invariants: FxHashSet<ClosureInvariantInfo>, tcx: TyCtxt) -> Self {
        Self {
            def_hash: utils::def_hash_str(def_id, tcx),
            invariants,
        }
    }
}

/// Convenience type alias for closure invariant info tuple
/// (i.e. a tuple representing the conditional operation, operand place, collection place ).
pub type ClosureInvariantInfo = (CondOp, ClosurePlaceIdx, ClosurePlaceIdx);

/// A serializable closure place idx.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ClosurePlaceIdx {
    /// An index of a closure argument.
    Arg(usize),
    /// An index of a captured variable.
    Capture(u32),
}

impl ClosurePlaceIdx {
    /// Create an argument place index.
    pub fn new_arg(idx: usize) -> Self {
        Self::Arg(idx)
    }

    /// Create a captured local place index.
    pub fn new_capture(idx: u32) -> Self {
        Self::Capture(idx)
    }

    /// Returns `Place` for index given a closure `DefId`.
    pub fn into_place(self, def_id: DefId, tcx: TyCtxt) -> Place {
        match self {
            Self::Arg(idx) => {
                // NOTE: For closures the "real"/user-defined args start from index 2.
                let arg_local = Local::from_usize(idx + 2);
                Place::from(arg_local)
            }
            Self::Capture(idx) => {
                // Finds the type of the captured place.
                let closure_ty = tcx.type_of(def_id).skip_binder();
                let TyKind::Closure(_, closure_args) = closure_ty.kind() else {
                    panic!("Expected a closure, found {def_id:?}");
                };
                let closure_args = ClosureArgs::<TyCtxt> { args: closure_args };
                let captured_locals_ty = closure_args.upvar_tys()[idx as usize];

                // Finds the captured place.
                // NOTE: For closures captured locals are represented as projections (i.e. struct fields)
                // of the local with index 1.
                let captured_locals = Local::from_u32(1);
                let captured_locals_place = Place::from(captured_locals);
                let field_idx = FieldIdx::from_u32(idx);
                let projection = PlaceElem::Field(field_idx, captured_locals_ty);
                tcx.mk_place_elem(captured_locals_place, projection)
            }
        }
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

/// Propagate collection index/position invariant to `Result` or `Option` adapter input closures.
pub fn propagate_opt_result_idx_invariant<'tcx>(
    opt_res_place: Place<'tcx>,
    next_block: &BasicBlockData<'tcx>,
    collection_def_places: &[(Place<'tcx>, BasicBlock)],
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt<'tcx>,
) {
    let Some(terminator) = next_block.terminator.as_ref() else {
        return;
    };
    let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
        return;
    };
    let Some(first_arg_place) = args.first().and_then(|arg| arg.node.place()) else {
        return;
    };
    if first_arg_place != opt_res_place {
        return;
    }
    let Some((def_id, ..)) = func.const_fn_def() else {
        return;
    };
    let fn_name = tcx.item_name(def_id);
    let crate_name = tcx.crate_name(def_id.krate);
    let Some(impl_def_id) = tcx.impl_of_method(def_id) else {
        return;
    };
    let impl_subject = tcx.impl_subject(impl_def_id).skip_binder();
    let ImplSubject::Inherent(ty) = impl_subject else {
        return;
    };
    let Some(adt_def) = ty.ty_adt_def() else {
        return;
    };
    let adt_name = tcx.item_name(adt_def.did());
    let is_adapter_with_closure_input = matches!(crate_name.as_str(), "std" | "core")
        && (matches!(adt_name.as_str(), "Result" | "Option")
            && matches!(
                fn_name.as_str(),
                "map" | "map_or" | "map_or_else" | "inspect" | "and_then"
            )
            || (adt_name.as_str() == "Result" && fn_name.as_str() == "is_ok_and")
            || (adt_name.as_str() == "Option"
                && matches!(fn_name.as_str(), "filter" | "is_some_and" | "take_if")));
    if !is_adapter_with_closure_input {
        return;
    }

    // Find capturing closure info (if any).
    let Some((closure_def_id, captured_locals, _)) = args
        .iter()
        .find_map(|arg| capturing_closure_info(&arg.node, next_block))
    else {
        return;
    };
    let use_or_ref_place = |rvalue: &Rvalue<'tcx>| match rvalue {
        Rvalue::Use(Operand::Copy(op_place) | Operand::Move(op_place)) => Some(*op_place),
        Rvalue::Ref(_, _, op_place) => Some(*op_place),
        _ => None,
    };
    let assign_place = |place: Place<'tcx>, block_data: &BasicBlockData<'tcx>| {
        block_data
            .statements
            .iter()
            .find_map(|stmt| match &stmt.kind {
                StatementKind::Assign(assign) if assign.0 == place => use_or_ref_place(&assign.1),
                _ => None,
            })
    };
    let captured_collection_idx = captured_locals
        .iter_enumerated()
        .find_map(|(idx, operand)| {
            operand.place().and_then(|op_place| {
                let is_collection_place = collection_def_places
                    .iter()
                    .any(|(collection_place, _)| op_place == *collection_place);
                is_collection_place.then_some(idx).or_else(|| {
                    // Handles aliased and projection captures.
                    next_block
                        .statements
                        .iter()
                        .find_map(|stmt| match &stmt.kind {
                            StatementKind::Assign(assign) if op_place == assign.0 => {
                                let src_place = use_or_ref_place(&assign.1)?;
                                let is_use_or_ref_place = collection_def_places
                                    .iter()
                                    .any(|(collection_place, _)| src_place == *collection_place);
                                let is_projected_place = collection_def_places.iter().any(
                                    |(collection_place, collection_def_bb)| {
                                        assign_place(
                                            *collection_place,
                                            &basic_blocks[*collection_def_bb],
                                        )
                                        .is_some_and(|place| place == src_place)
                                    },
                                );
                                (is_use_or_ref_place || is_projected_place).then_some(idx)
                            }
                            _ => None,
                        })
                })
            })
        });
    let Some(captured_collection_idx) = captured_collection_idx else {
        return;
    };

    // Composes propagated invariant environment for closure.
    let invariants = FxHashSet::from_iter([(
        CondOp::Lt,
        // Position/index operand is the first arg of the input closure.
        ClosurePlaceIdx::new_arg(0),
        ClosurePlaceIdx::new_capture(captured_collection_idx.as_u32()),
    )]);
    let closure_invariant_env = ClosureInvariantEnv::new(closure_def_id, invariants, tcx);

    // Sets propagated invariant environment for closure.
    set_invariant_env(&closure_invariant_env);

    // Composes closure MIR (with propagated invariant environment set).
    let _ = tcx.optimized_mir(closure_def_id);
}

/// Returns a env key for the given def hash.
fn closure_invariant_env_key(def_hash: &str) -> String {
    format!("{ENV_CLOSURE_INVARIANT_PREFIX}_{def_hash}")
}

/// Sets propagated invariant environment for closure.
pub fn set_invariant_env(invariant_env: &ClosureInvariantEnv) {
    let invariant_env_json =
        serde_json::to_string(invariant_env).expect("Expected serialized `ClosureInvariantEnv`");
    // SAFETY: `pallet-verifier` is single-threaded.
    let env_key = closure_invariant_env_key(&invariant_env.def_hash);
    std::env::set_var(env_key, invariant_env_json);
}

/// Retrieves the propagated invariant environment for closure (if any).
pub fn find_invariant_env(def_id: DefId, tcx: TyCtxt) -> Option<ClosureInvariantEnv> {
    // SAFETY: `pallet-verifier` is single-threaded.
    let hash = utils::def_hash_str(def_id, tcx);
    let env_key = closure_invariant_env_key(&hash);
    let invariant_env_json = std::env::var(env_key).ok()?;
    let invariant_env: ClosureInvariantEnv = serde_json::from_str(&invariant_env_json).ok()?;
    (invariant_env.def_hash == hash).then_some(invariant_env)
}

/// Applies propagated invariants for closure.
pub fn apply_propagated_invariants<'tcx>(
    def_id: DefId,
    closure_invariant_env: ClosureInvariantEnv,
    body: &mut Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) {
    for (cond_op, op_place_idx, collection_place_idx) in closure_invariant_env.invariants {
        apply_propagated_invariant(
            def_id,
            cond_op,
            op_place_idx,
            collection_place_idx,
            body,
            tcx,
        );
    }
}

/// Applies propagated invariant for closure.
fn apply_propagated_invariant<'tcx>(
    def_id: DefId,
    cond_op: CondOp,
    op_place_idx: ClosurePlaceIdx,
    collection_place_idx: ClosurePlaceIdx,
    body: &mut Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) {
    // Finds operand place.
    let op_place = op_place_idx.into_place(def_id, tcx);

    // Finds collection place.
    let collection_place = collection_place_idx.into_place(def_id, tcx);

    // Declares a collection length/size bound annotation (if appropriate).
    let collection_place_ty = collection_place.ty(body.local_decls(), tcx).ty;
    let Some(len_call_info) = analyze::collection_len_call(collection_place_ty, tcx) else {
        return;
    };

    // Derefs places (if necessary), also sets the annotation location.
    let mut annotation_location = Location::START;
    let derefed_op_place = if matches!(op_place_idx, ClosurePlaceIdx::Capture(_)) {
        let Ok(derefed_place) = deref_captured_place(op_place, &mut annotation_location, body, tcx)
        else {
            // Bails if captured place needs derefing, but we couldn't deref it.
            return;
        };
        derefed_place
    } else {
        op_place
    };
    let derefed_collection_place = if matches!(collection_place_idx, ClosurePlaceIdx::Capture(_)) {
        let Ok(derefed_place) =
            deref_captured_place(collection_place, &mut annotation_location, body, tcx)
        else {
            // Bails if captured place needs derefing, but we couldn't deref it.
            return;
        };
        derefed_place
    } else {
        collection_place
    };

    // Adds propagated invariant annotation.
    let region = match collection_place_ty.kind() {
        TyKind::Ref(region, _, _) => *region,
        _ => Region::new_from_kind(tcx, RegionKind::ReErased),
    };
    let annotation = Annotation::Len(
        annotation_location,
        cond_op,
        derefed_op_place,
        derefed_collection_place,
        region,
        len_call_info,
    );
    annotation.insert(body, tcx);
}

// Derefs place and updates the annotation location (if necessary).
fn deref_captured_place<'tcx>(
    op_place: Place<'tcx>,
    annotation_location: &mut Location,
    body: &mut Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Result<Place<'tcx>, ()> {
    // Derefs place (if necessary), also sets the annotation location.
    let op_place_ty = op_place.ty(body.local_decls(), tcx).ty;
    let derefed_op_place = if op_place_ty.is_ref() {
        // Composes `CopyForDeref` statement for place ref.
        let basic_block = &body.basic_blocks[annotation_location.block];
        let Some(source_info) = basic_block
            .statements
            .first()
            .map(|stmt| stmt.source_info)
            .or_else(|| {
                basic_block
                    .terminator
                    .as_ref()
                    .map(|terminator| terminator.source_info)
            })
        else {
            // Bails if captured place needs derefing, but we have no source info.
            return Err(());
        };
        let copy_for_deref_rvalue = Rvalue::CopyForDeref(op_place);
        let copy_for_deref_local_decl = LocalDecl::with_source_info(op_place_ty, source_info);
        let copy_for_deref_local = body.local_decls.push(copy_for_deref_local_decl);
        let copy_for_deref_place = Place::from(copy_for_deref_local);
        let copy_for_deref_stmt = Statement {
            source_info,
            kind: StatementKind::Assign(Box::new((copy_for_deref_place, copy_for_deref_rvalue))),
        };

        // Composes `Deref` statements for place.
        let deref_place = tcx.mk_place_deref(copy_for_deref_place);
        let deref_operand = Operand::Copy(deref_place);
        let deref_rvalue = Rvalue::Use(deref_operand);
        let deref_local_decl = LocalDecl::with_source_info(tcx.types.usize, source_info);
        let deref_local = body.local_decls.push(deref_local_decl);
        let deref_place = Place::from(deref_local);
        let deref_stmt = Statement {
            source_info,
            kind: StatementKind::Assign(Box::new((deref_place, deref_rvalue))),
        };

        // Adds `Deref` statements for place to first block, and updates annotation location.
        body.basic_blocks_mut()[annotation_location.block]
            .statements
            .splice(..0, [copy_for_deref_stmt, deref_stmt]);
        annotation_location.statement_index = 2;

        // Sets derefed op place
        deref_place
    } else {
        op_place
    };

    Ok(derefed_op_place)
}
