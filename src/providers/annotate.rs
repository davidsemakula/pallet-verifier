//! Utilities and helpers for adding MIRAI annotations to MIR.
//!
//! [MIRAI-annotations]: https://crates.io/crates/mirai-annotations

use rustc_abi::{Align, Size};
use rustc_const_eval::interpret::{Allocation, Scalar};
use rustc_hir::{def::DefKind, LangItem};
use rustc_middle::{
    middle::exported_symbols::ExportedSymbol,
    mir::{
        BasicBlockData, BinOp, Body, BorrowKind, CallSource, Const, ConstOperand, ConstValue,
        HasLocalDecls, LocalDecl, LocalDecls, Location, Operand, Place, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind, UnwindAction,
    },
    ty::{GenericArg, List, Region, ScalarInt, Ty, TyCtxt, TyKind, TypeAndMut},
};
use rustc_span::{def_id::DefId, source_map::dummy_spanned, Span};

use crate::utils;

/// An annotation to add to MIR.
pub enum Annotation<'tcx> {
    /// An integer cast overflow check.
    CastOverflow(Location, BinOp, Operand<'tcx>, Operand<'tcx>),
    /// An `isize::MAX` bound annotation.
    Isize(Location, BinOp, Place<'tcx>),
    /// A collection length/size bound annotation.
    Len(
        Location,
        /// Binary operation for the annotation.
        BinOp,
        /// The operand place (e.g. a index place).
        Place<'tcx>,
        /// The collection place and region.
        Place<'tcx>,
        Region<'tcx>,
        /// A list of call info needed to build a collection length/size call.
        /// A list is necessary because some length/size calls require a `Deref` call before
        ///  the target length/size call (e.g. for `BoundedVec`).
        /// See also [`collection_len_call`].
        Vec<(DefId, &'tcx List<GenericArg<'tcx>>, Ty<'tcx>)>,
    ),
}

impl<'tcx> Annotation<'tcx> {
    /// Adds instructions for the annotation to the given MIR body.
    pub fn insert(self, body: &mut Body<'tcx>, tcx: TyCtxt<'tcx>) {
        let location = *self.location();
        let Some(basic_block) = body.basic_blocks.get(location.block) else {
            return;
        };
        let Some(source_info) = basic_block
            .statements
            .get(location.statement_index)
            .or_else(|| basic_block.statements.first())
            .map(|stmt| stmt.source_info)
            .or_else(|| {
                basic_block
                    .terminator
                    .as_ref()
                    .map(|terminator| terminator.source_info)
            })
        else {
            return;
        };

        // Extracts predecessors and successors.
        let (predecessors, successors) = basic_block.statements.split_at(location.statement_index);
        let mut predecessors = predecessors.to_vec();
        let successors = successors.to_vec();
        let terminator = basic_block.terminator.clone();

        // Adds successor block.
        let mut successor_block_data = BasicBlockData::new(terminator);
        successor_block_data.statements = successors;
        let successor_block = body.basic_blocks_mut().push(successor_block_data);

        // Adds annotation argument (and related) statements and/or blocks.
        let arg_local_decl = LocalDecl::with_source_info(tcx.types.bool, source_info);
        let arg_local = body.local_decls.push(arg_local_decl);
        let arg_place = Place::from(arg_local);
        let (annotation_handle, annotation_args, target_block, target_block_statements) = match self
        {
            Annotation::CastOverflow(_, assert_cond, val_operand, bound_operand) => {
                // Adds condition statement.
                let arg_rvalue =
                    Rvalue::BinaryOp(assert_cond, Box::new((val_operand, bound_operand)));
                let arg_stmt = Statement {
                    source_info,
                    kind: StatementKind::Assign(Box::new((arg_place, arg_rvalue))),
                };
                predecessors.push(arg_stmt);

                // Returns target block and statements.
                (
                    mirai_annotation_fn_handle(AnnotationFn::Verify, tcx),
                    vec![
                        dummy_spanned(Operand::Move(arg_place)),
                        dummy_spanned(cast_overflow_diag_message(tcx)),
                    ],
                    location.block,
                    predecessors,
                )
            }
            Annotation::Isize(_, cond_op, op_place) => {
                // Creates `isize::MAX` bound statement.
                let arg_rvalue = Rvalue::BinaryOp(
                    cond_op,
                    Box::new((Operand::Copy(op_place), isize_max_operand(tcx))),
                );
                let arg_stmt = Statement {
                    source_info,
                    kind: StatementKind::Assign(Box::new((arg_place, arg_rvalue))),
                };
                predecessors.push(arg_stmt);

                // Returns target block and statements.
                (
                    mirai_annotation_fn_handle(AnnotationFn::Assume, tcx),
                    vec![dummy_spanned(Operand::Move(arg_place))],
                    location.block,
                    predecessors,
                )
            }
            Annotation::Len(
                _,
                cond_op,
                op_place,
                collection_place,
                collection_region,
                collection_len_builder_calls,
            ) => {
                // Initializes variables for tracking state of collection length/size "builder" calls.
                let mut current_block = location.block;
                let mut current_statements = predecessors;
                let mut current_arg_place = collection_place;
                let mut final_len_bound_place = None;
                for (len_builder_def_id, len_builder_gen_args, len_builder_ty) in
                    collection_len_builder_calls
                {
                    // Sets arg ref place.
                    let current_arg_ty = current_arg_place.ty(body.local_decls(), tcx).ty;
                    let current_arg_ref_place = if current_arg_ty.is_ref() {
                        current_arg_place
                    } else {
                        // Creates arg ref statement.
                        let current_arg_ref_ty = Ty::new_ref(
                            tcx,
                            collection_region,
                            TypeAndMut {
                                ty: current_arg_ty,
                                mutbl: rustc_ast::Mutability::Not,
                            },
                        );
                        let current_arg_ref_local_decl =
                            LocalDecl::with_source_info(current_arg_ref_ty, source_info);
                        let current_arg_ref_local =
                            body.local_decls.push(current_arg_ref_local_decl);
                        let current_arg_ref_place = Place::from(current_arg_ref_local);
                        let current_arg_ref_rvalue =
                            Rvalue::Ref(collection_region, BorrowKind::Shared, current_arg_place);
                        let current_arg_ref_stmt = Statement {
                            source_info,
                            kind: StatementKind::Assign(Box::new((
                                current_arg_ref_place,
                                current_arg_ref_rvalue,
                            ))),
                        };
                        current_statements.push(current_arg_ref_stmt);
                        current_arg_ref_place
                    };

                    // Creates an empty next block.
                    let next_block_data = BasicBlockData::new(None);
                    let next_block = body.basic_blocks_mut().push(next_block_data);

                    // Creates collection length/size "builder" call.
                    let len_builder_local_decl =
                        LocalDecl::with_source_info(len_builder_ty, source_info);
                    let len_builder_local = body.local_decls.push(len_builder_local_decl);
                    let len_builder_destination_place = Place::from(len_builder_local);
                    let len_builder_handle = Operand::function_handle(
                        tcx,
                        len_builder_def_id,
                        len_builder_gen_args,
                        Span::default(),
                    );
                    let len_builder_call = Terminator {
                        source_info,
                        kind: TerminatorKind::Call {
                            func: len_builder_handle,
                            args: vec![dummy_spanned(Operand::Move(current_arg_ref_place))],
                            destination: len_builder_destination_place,
                            target: Some(next_block),
                            unwind: UnwindAction::Unreachable,
                            call_source: CallSource::Misc,
                            fn_span: Span::default(),
                        },
                    };

                    // Updates current block statements and terminator.
                    let basic_blocks = body.basic_blocks_mut();
                    basic_blocks[current_block].statements = current_statements;
                    basic_blocks[current_block].terminator = Some(len_builder_call);

                    // Next iteration.
                    current_block = next_block;
                    current_statements = Vec::new();
                    current_arg_place = len_builder_destination_place;
                    final_len_bound_place = Some(len_builder_destination_place);
                }

                // Creates collection length/size bound statement
                // (if a length/size call was successfully constructed).
                if let Some(final_len_bound_place) = final_len_bound_place {
                    let deref_op_place = if op_place.ty(body.local_decls(), tcx).ty.is_ref() {
                        tcx.mk_place_deref(op_place)
                    } else {
                        op_place
                    };
                    let arg_rvalue = Rvalue::BinaryOp(
                        cond_op,
                        Box::new((
                            Operand::Copy(deref_op_place),
                            Operand::Copy(final_len_bound_place),
                        )),
                    );
                    let arg_stmt = Statement {
                        source_info,
                        kind: StatementKind::Assign(Box::new((arg_place, arg_rvalue))),
                    };
                    current_statements.push(arg_stmt);
                }

                // Returns target block and statements.
                (
                    mirai_annotation_fn_handle(AnnotationFn::Assume, tcx),
                    vec![dummy_spanned(Operand::Move(arg_place))],
                    current_block,
                    current_statements,
                )
            }
        };

        // Creates annotation call (e.g. `mirai_assume!` or `mirai_verify!`).
        let annotation_local_decl = LocalDecl::with_source_info(tcx.types.never, source_info);
        let annotation_local = body.local_decls.push(annotation_local_decl);
        let annotation_place = Place::from(annotation_local);
        let annotation_call = Terminator {
            source_info,
            kind: TerminatorKind::Call {
                func: annotation_handle,
                args: annotation_args,
                destination: annotation_place,
                target: Some(successor_block),
                unwind: UnwindAction::Unreachable,
                call_source: CallSource::Misc,
                fn_span: Span::default(),
            },
        };

        // Updates target block statements and terminator.
        let basic_blocks = body.basic_blocks_mut();
        basic_blocks[target_block].statements = target_block_statements;
        basic_blocks[target_block].terminator = Some(annotation_call);
    }

    /// Returns the target location for adding the annotation.
    pub fn location(&self) -> &Location {
        match &self {
            Annotation::CastOverflow(location, ..)
            | Annotation::Isize(location, ..)
            | Annotation::Len(location, ..) => location,
        }
    }
}

/// Adds a list of annotations.
pub fn add_annotations<'tcx>(
    mut annotations: Vec<Annotation<'tcx>>,
    body: &mut Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) {
    // Bails if there are no annotations.
    if annotations.is_empty() {
        return;
    }

    // Reverse sorts annotation declarations by location.
    annotations.sort_by(|a, b| b.location().cmp(a.location()));

    // Adds iterator annotations.
    for annotation in annotations {
        annotation.insert(body, tcx);
    }
}

/// Composes a slice length/size bound annotation.
pub fn compose_slice_len_annotation<'tcx>(
    annotation_location: Location,
    cond_op: BinOp,
    invariant_place: Place<'tcx>,
    slice_place: Place<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<Annotation<'tcx>> {
    let TyKind::Ref(region, slice_ty, _) = slice_place.ty(local_decls, tcx).ty.kind() else {
        return None;
    };
    if !slice_ty.is_slice() {
        return None;
    }
    let slice_len_def_id = tcx
        .lang_items()
        .get(LangItem::SliceLen)
        .expect("Expected `[T]::len` lang item");
    let slice_len_generics = tcx.generics_of(slice_len_def_id);
    let slice_len_host_param_def = slice_len_generics
        .params
        .first()
        .expect("Expected `host` generic param");
    let slice_len_host_param_value = slice_len_host_param_def
        .default_value(tcx)
        .expect("Expected `host` generic param default value")
        .skip_binder();
    let gen_ty = slice_ty
        .walk()
        .nth(1)
        .expect("Expected a generic arg for `[T]`");
    let gen_args = tcx.mk_args(&[gen_ty, slice_len_host_param_value]);
    Some(Annotation::Len(
        annotation_location,
        cond_op,
        invariant_place,
        slice_place,
        *region,
        vec![(slice_len_def_id, gen_args, tcx.types.usize)],
    ))
}

/// An annotation function (equivalent to a MIRAI annotation macro).
///
/// Ref: <https://crates.io/crates/mirai-annotations>
enum AnnotationFn {
    Assume,
    Verify,
}

impl AnnotationFn {
    /// Returns the name of target MIRAI annotation function.
    ///
    /// (i.e. for `mirai_annotations::assume!`, the target function is `mirai_assume`).
    fn fn_name(&self) -> &str {
        match self {
            AnnotationFn::Assume => "mirai_assume",
            AnnotationFn::Verify => "mirai_verify",
        }
    }
}

impl std::fmt::Display for AnnotationFn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.fn_name())
    }
}

/// Creates MIRAI annotation function handle.
fn mirai_annotation_fn_handle(annotation_fn: AnnotationFn, tcx: TyCtxt) -> Operand {
    let annotations_crate = tcx
        .crates(())
        .iter()
        .find(|crate_num| tcx.crate_name(**crate_num).as_str() == "mirai_annotations")
        .expect("Expected `mirai_annotations` crate as a dependency");
    let fn_name = annotation_fn.fn_name();
    let fn_def_id = tcx
        .exported_symbols(*annotations_crate)
        .iter()
        .find_map(|(exported_sym, _)| {
            if let ExportedSymbol::NonGeneric(def_id) = exported_sym {
                if tcx.def_kind(def_id) == DefKind::Fn && tcx.item_name(*def_id).as_str() == fn_name
                {
                    return Some(*def_id);
                }
            }
            None
        })
        .expect("Expected a fn def");
    Operand::function_handle(tcx, fn_def_id, [], Span::default())
}

/// Creates cast overflow diagnostic message.
fn cast_overflow_diag_message(tcx: TyCtxt) -> Operand {
    let msg = "attempt to cast with overflow".as_bytes();
    let msg_const = ConstValue::Slice {
        data: tcx.mk_const_alloc(Allocation::from_bytes(
            msg,
            Align::ONE,
            rustc_ast::Mutability::Not,
        )),
        meta: msg.len() as u64,
    };
    Operand::Constant(Box::new(ConstOperand {
        span: Span::default(),
        user_ty: None,
        const_: Const::from_value(msg_const, Ty::new_static_str(tcx)),
    }))
}

// Creates `isize::MAX` operand.
fn isize_max_operand(tcx: TyCtxt) -> Operand {
    let pointer_width = utils::target_pointer_width();
    let isize_max_scalar = ScalarInt::try_from_uint(
        match pointer_width {
            16 => i16::MAX as u128,
            32 => i32::MAX as u128,
            64 => i64::MAX as u128,
            _ => unreachable!("Unsupported pointer width"),
        },
        Size::from_bits(pointer_width),
    )
    .expect("Expected a valid scalar bound");
    Operand::const_from_scalar(
        tcx,
        tcx.types.usize,
        Scalar::Int(isize_max_scalar),
        Span::default(),
    )
}