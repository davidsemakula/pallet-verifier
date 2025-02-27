//! Utilities and helpers for adding MIRAI annotations to MIR.
//!
//! [MIRAI-annotations]: https://crates.io/crates/mirai-annotations

use rustc_abi::{Align, Size};
use rustc_const_eval::interpret::{Allocation, Scalar};
use rustc_hir::def::DefKind;
use rustc_middle::{
    middle::exported_symbols::ExportedSymbol,
    mir::{
        BasicBlockData, BinOp, Body, BorrowKind, CallSource, Const, ConstOperand, ConstValue,
        HasLocalDecls, LocalDecl, Location, Operand, Place, Rvalue, Statement, StatementKind,
        Terminator, TerminatorKind, UnwindAction,
    },
    ty::{GenericArg, List, Region, ScalarInt, Ty, TyCtxt},
};
use rustc_span::{def_id::DefId, source_map::dummy_spanned, Span};

use serde::{Deserialize, Serialize};

use crate::utils;

/// An annotation to add to MIR.
#[derive(Debug, Clone)]
pub enum Annotation<'tcx> {
    /// An integer cast overflow check.
    CastOverflow(Location, CondOp, Operand<'tcx>, Operand<'tcx>),
    /// An constant maximum bound annotation (e.g. an `isize::MAX` upper bound).
    ConstMax(Location, CondOp, Place<'tcx>, u128),
    /// A collection length/size bound annotation.
    Len(
        Location,
        /// Conditional operation for the annotation.
        CondOp,
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
    /// Creates an `isize::MAX` bound annotation.
    pub fn new_const_max(
        location: Location,
        cond_op: CondOp,
        place: Place<'tcx>,
        bound: u128,
    ) -> Self {
        Self::ConstMax(location, cond_op, place, bound)
    }

    /// Creates an `isize::MAX` bound annotation.
    pub fn new_isize_max(location: Location, cond_op: CondOp, place: Place<'tcx>) -> Self {
        Self::new_const_max(location, cond_op, place, utils::target_isize_max())
    }

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
        let mut successor_block_data = BasicBlockData::new(terminator, false);
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
                    Rvalue::BinaryOp(assert_cond.into(), Box::new((val_operand, bound_operand)));
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
            Annotation::ConstMax(_, cond_op, op_place, bound) => {
                // Creates `isize::MAX` bound statement.
                let arg_rvalue = Rvalue::BinaryOp(
                    cond_op.into(),
                    Box::new((Operand::Copy(op_place), const_int_operand(bound, tcx))),
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
                            current_arg_ty,
                            rustc_ast::Mutability::Not,
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
                    let next_block_data = BasicBlockData::new(None, false);
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
                            args: Box::new([dummy_spanned(Operand::Move(current_arg_ref_place))]),
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
                        cond_op.into(),
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
                args: annotation_args.into(),
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
            | Annotation::ConstMax(location, ..)
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

/// Conditional operator.
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Ord, Eq, Hash, Serialize, Deserialize)]
pub enum CondOp {
    /// The `==` operator (equality).
    Eq,
    /// The `<=` operator (less than or equal to).
    Le,
    /// The `<` operator (less than).
    Lt,
    /// The `!=` operator (not equal to).
    Ne,
    /// The `>=` operator (greater than or equal to).
    Ge,
    /// The `>` operator (greater than).
    Gt,
}

/// We can't implement `From<BinOp> for CondOp` (because `CondOp` is a subset of `BinOp`),
/// so we implement `Into<BinOp> for CondOp` instead.
#[allow(clippy::from_over_into)]
impl Into<BinOp> for CondOp {
    fn into(self) -> BinOp {
        match self {
            CondOp::Eq => BinOp::Eq,
            CondOp::Lt => BinOp::Lt,
            CondOp::Le => BinOp::Le,
            CondOp::Ne => BinOp::Ne,
            CondOp::Ge => BinOp::Ge,
            CondOp::Gt => BinOp::Gt,
        }
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

// Creates integer operand.
fn const_int_operand(val: u128, tcx: TyCtxt) -> Operand {
    let pointer_width = utils::target_pointer_width();
    let isize_max_scalar = ScalarInt::try_from_uint(val, Size::from_bits(pointer_width))
        .expect("Expected a valid scalar bound");
    Operand::const_from_scalar(
        tcx,
        tcx.types.usize,
        Scalar::Int(isize_max_scalar),
        Span::default(),
    )
}
