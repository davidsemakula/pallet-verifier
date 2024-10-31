//! `rustc` `MirPass` for adding integer cast overflow checks.

use rustc_abi::{Align, Size};
use rustc_const_eval::interpret::{Allocation, Scalar};
use rustc_middle::{
    mir::{
        visit::Visitor, BasicBlockData, BinOp, Body, CallSource, CastKind, Const, ConstOperand,
        ConstValue, HasLocalDecls, LocalDecl, LocalDecls, Location, MirPass, Operand, Place,
        Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnwindAction,
    },
    ty::{ScalarInt, Ty, TyCtxt, TyKind},
};
use rustc_span::{source_map::dummy_spanned, Span};
use rustc_type_ir::{IntTy, UintTy};

use crate::utils;

/// Adds integer cast overflow checks.
pub struct IntCastOverflowChecks;

impl<'tcx> MirPass<'tcx> for IntCastOverflowChecks {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let mut visitor = LossyIntCastVisitor::new(tcx, body.local_decls());
        visitor.visit_body(body);

        let mut checks = visitor.checks;
        if checks.is_empty() {
            return;
        }
        // Reverse sorts integer cast overflow checks by location.
        checks.sort_by(|(loc_a, ..), (loc_b, ..)| loc_b.cmp(loc_a));

        // Creates `mirai_verify` annotation handle and diagnostic message.
        let mirai_verify_def_id = utils::mirai_annotation_fn("mirai_verify", tcx)
            .expect("Expected a fn def for `mirai_verify`");
        let mirai_verify_handle =
            Operand::function_handle(tcx, mirai_verify_def_id, [], Span::default());
        let diag_msg = "attempt to cast with overflow".as_bytes();
        let diag_msg_const = ConstValue::Slice {
            data: tcx.mk_const_alloc(Allocation::from_bytes(
                diag_msg,
                Align::ONE,
                rustc_ast::Mutability::Not,
            )),
            meta: diag_msg.len() as u64,
        };
        let diag_msg_op = Operand::Constant(Box::new(ConstOperand {
            span: Span::default(),
            user_ty: None,
            const_: Const::from_value(diag_msg_const, Ty::new_static_str(tcx)),
        }));

        // Adds integer cast overflow checks.
        for (location, assert_cond, val_operand, bound_operand) in checks {
            let Some(basic_block) = body.basic_blocks.get(location.block) else {
                continue;
            };
            let Some(cast_stmt) = basic_block.statements.get(location.statement_index) else {
                continue;
            };
            let source_info = cast_stmt.source_info;

            // Extracts predecessors and successors.
            let (predecessors, successors) =
                basic_block.statements.split_at(location.statement_index);
            let mut predecessors = predecessors.to_vec();
            let successors = successors.to_vec();
            let terminator = basic_block.terminator.clone();

            // Adds successor block.
            let mut successor_block_data = BasicBlockData::new(terminator);
            successor_block_data.statements = successors;
            let successor_block = body.basic_blocks_mut().push(successor_block_data);

            // Adds condition statement.
            let cond_local_decl =
                LocalDecl::with_source_info(Ty::new(tcx, TyKind::Bool), source_info);
            let cond_local = body.local_decls.push(cond_local_decl);
            let cond_place = Place::from(cond_local);
            let cond_rvalue = Rvalue::BinaryOp(assert_cond, Box::new((val_operand, bound_operand)));
            let cond_stmt = Statement {
                source_info,
                kind: StatementKind::Assign(Box::new((cond_place, cond_rvalue))),
            };
            predecessors.push(cond_stmt);

            // Creates `mirai_verify` annotation call.
            let annotation_ty = Ty::new(tcx, TyKind::Never);
            let annotation_local_decl = LocalDecl::with_source_info(annotation_ty, source_info);
            let annotation_local = body.local_decls.push(annotation_local_decl);
            let annotation_place = Place::from(annotation_local);
            let annotation_call = Terminator {
                source_info,
                kind: TerminatorKind::Call {
                    func: mirai_verify_handle.clone(),
                    args: vec![
                        dummy_spanned(Operand::Move(cond_place)),
                        dummy_spanned(diag_msg_op.clone()),
                    ],
                    destination: annotation_place,
                    target: Some(successor_block),
                    unwind: UnwindAction::Unreachable,
                    call_source: CallSource::Misc,
                    fn_span: Span::default(),
                },
            };

            // Updates target block statements and terminator.
            let basic_blocks = body.basic_blocks_mut();
            basic_blocks[location.block].statements = predecessors;
            basic_blocks[location.block].terminator = Some(annotation_call);
        }
    }
}

/// Collects locations and operands for lossy integer cast operations.
struct LossyIntCastVisitor<'tcx, 'pass> {
    tcx: TyCtxt<'tcx>,
    local_decls: &'pass LocalDecls<'tcx>,
    /// A list of location, assert condition/comparison operation, value and bound operand tuples
    /// for overflow/underflow checks.
    checks: Vec<(Location, BinOp, Operand<'tcx>, Operand<'tcx>)>,
}

impl<'tcx, 'pass> LossyIntCastVisitor<'tcx, 'pass> {
    fn new(tcx: TyCtxt<'tcx>, local_decls: &'pass LocalDecls<'tcx>) -> Self {
        Self {
            tcx,
            local_decls,
            checks: Vec::new(),
        }
    }

    fn process_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Cast(CastKind::IntToInt, operand, ty) = rvalue {
            let op_ty = operand.ty(self.local_decls, self.tcx);
            let pointer_width = utils::target_pointer_width();
            let op_ty_bit_width = match op_ty.kind() {
                TyKind::Uint(uint_ty) => uint_ty.normalize(pointer_width as u32).bit_width(),
                TyKind::Int(int_ty) => int_ty.normalize(pointer_width as u32).bit_width(),
                _ => None,
            };
            let Some(int_bit_width) = op_ty_bit_width else {
                return;
            };
            let host_size = Size::from_bits(int_bit_width);
            let max_scalar = match (ty.kind(), op_ty.kind()) {
                // i8
                (
                    TyKind::Int(IntTy::I8),
                    TyKind::Int(IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize)
                    | TyKind::Uint(
                        UintTy::U8
                        | UintTy::U16
                        | UintTy::U32
                        | UintTy::U64
                        | UintTy::U128
                        | UintTy::Usize,
                    ),
                ) => ScalarInt::try_from_int(i8::MAX, host_size),
                // u8
                (
                    TyKind::Uint(UintTy::U8),
                    TyKind::Uint(
                        UintTy::U16 | UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize,
                    )
                    | TyKind::Int(IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize),
                ) => ScalarInt::try_from_uint(u8::MAX, host_size),
                // i16
                (
                    TyKind::Int(IntTy::I16 | IntTy::Isize),
                    TyKind::Int(IntTy::I32 | IntTy::I64 | IntTy::I128)
                    | TyKind::Uint(
                        UintTy::U16 | UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize,
                    ),
                ) if pointer_width == 16 => ScalarInt::try_from_int(i16::MAX, host_size),
                (
                    TyKind::Int(IntTy::I16),
                    TyKind::Int(IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize)
                    | TyKind::Uint(
                        UintTy::U16 | UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize,
                    ),
                ) if pointer_width != 16 => ScalarInt::try_from_int(i16::MAX, host_size),
                // u16
                (
                    TyKind::Uint(UintTy::U16 | UintTy::Usize),
                    TyKind::Uint(UintTy::U32 | UintTy::U64 | UintTy::U128)
                    | TyKind::Int(IntTy::I32 | IntTy::I64 | IntTy::I128),
                ) if pointer_width == 16 => ScalarInt::try_from_uint(u16::MAX, host_size),
                (
                    TyKind::Uint(UintTy::U16),
                    TyKind::Uint(UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize)
                    | TyKind::Int(IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize),
                ) if pointer_width != 16 => ScalarInt::try_from_uint(u16::MAX, host_size),
                // i32
                (
                    TyKind::Int(IntTy::I32 | IntTy::Isize),
                    TyKind::Int(IntTy::I64 | IntTy::I128)
                    | TyKind::Uint(UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize),
                ) if pointer_width == 32 => ScalarInt::try_from_int(i32::MAX, host_size),
                (
                    TyKind::Int(IntTy::I32),
                    TyKind::Int(IntTy::I64 | IntTy::I128)
                    | TyKind::Uint(UintTy::U32 | UintTy::U64 | UintTy::U128),
                ) if pointer_width == 16 => ScalarInt::try_from_int(i32::MAX, host_size),
                (
                    TyKind::Int(IntTy::I32),
                    TyKind::Int(IntTy::I64 | IntTy::I128 | IntTy::Isize)
                    | TyKind::Uint(UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize),
                ) if pointer_width == 64 => ScalarInt::try_from_int(i32::MAX, host_size),
                // u32
                (
                    TyKind::Uint(UintTy::U32 | UintTy::Usize),
                    TyKind::Uint(UintTy::U64 | UintTy::U128)
                    | TyKind::Int(IntTy::I64 | IntTy::I128),
                ) if pointer_width == 32 => ScalarInt::try_from_uint(u32::MAX, host_size),
                (
                    TyKind::Uint(UintTy::U32),
                    TyKind::Uint(UintTy::U64 | UintTy::U128)
                    | TyKind::Int(IntTy::I64 | IntTy::I128),
                ) if pointer_width == 16 => ScalarInt::try_from_uint(u32::MAX, host_size),
                (
                    TyKind::Uint(UintTy::U32),
                    TyKind::Uint(UintTy::U64 | UintTy::U128 | UintTy::Usize)
                    | TyKind::Int(IntTy::I64 | IntTy::I128 | IntTy::Isize),
                ) if pointer_width == 64 => ScalarInt::try_from_uint(u32::MAX, host_size),
                // i64
                (
                    TyKind::Int(IntTy::I64 | IntTy::Isize),
                    TyKind::Int(IntTy::I128)
                    | TyKind::Uint(UintTy::U64 | UintTy::U128 | UintTy::Usize),
                ) if pointer_width == 64 => ScalarInt::try_from_int(i64::MAX, host_size),
                (
                    TyKind::Int(IntTy::I64),
                    TyKind::Int(IntTy::I128) | TyKind::Uint(UintTy::U64 | UintTy::U128),
                ) if pointer_width != 64 => ScalarInt::try_from_int(i64::MAX, host_size),
                // u64
                (
                    TyKind::Uint(UintTy::U64 | UintTy::Usize),
                    TyKind::Uint(UintTy::U128) | TyKind::Int(IntTy::I128),
                ) if pointer_width == 64 => ScalarInt::try_from_uint(u64::MAX, host_size),
                (
                    TyKind::Uint(UintTy::U64),
                    TyKind::Uint(UintTy::U128) | TyKind::Int(IntTy::I128),
                ) if pointer_width != 64 => ScalarInt::try_from_uint(u64::MAX, host_size),
                // i128
                (TyKind::Int(IntTy::I128), TyKind::Uint(UintTy::U128)) => {
                    ScalarInt::try_from_int(i64::MAX, host_size)
                }
                _ => None,
            };
            let min_scalar = match (ty.kind(), op_ty.kind()) {
                // uint from int
                (TyKind::Uint(_), TyKind::Int(_)) => ScalarInt::try_from_uint(0u8, host_size),
                // i8
                (
                    TyKind::Int(IntTy::I8),
                    TyKind::Int(IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize),
                ) => ScalarInt::try_from_int(i8::MIN, host_size),
                // i16
                (
                    TyKind::Int(IntTy::I16 | IntTy::Isize),
                    TyKind::Int(IntTy::I32 | IntTy::I64 | IntTy::I128),
                ) if pointer_width == 16 => ScalarInt::try_from_int(i16::MIN, host_size),
                (
                    TyKind::Int(IntTy::I16),
                    TyKind::Int(IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize),
                ) if pointer_width != 16 => ScalarInt::try_from_int(i16::MIN, host_size),
                // i32
                (TyKind::Int(IntTy::I32 | IntTy::Isize), TyKind::Int(IntTy::I64 | IntTy::I128))
                    if pointer_width == 32 =>
                {
                    ScalarInt::try_from_int(i32::MIN, host_size)
                }
                (TyKind::Int(IntTy::I32), TyKind::Int(IntTy::I64 | IntTy::I128))
                    if pointer_width == 16 =>
                {
                    ScalarInt::try_from_int(i32::MIN, host_size)
                }
                (TyKind::Int(IntTy::I32), TyKind::Int(IntTy::I64 | IntTy::I128 | IntTy::Isize))
                    if pointer_width == 64 =>
                {
                    ScalarInt::try_from_int(i32::MIN, host_size)
                }
                // i64
                (TyKind::Int(IntTy::I64 | IntTy::Isize), TyKind::Int(IntTy::I128))
                    if pointer_width == 64 =>
                {
                    ScalarInt::try_from_int(i64::MIN, host_size)
                }
                (TyKind::Int(IntTy::I64), TyKind::Int(IntTy::I128)) if pointer_width != 64 => {
                    ScalarInt::try_from_int(i64::MIN, host_size)
                }
                _ => None,
            };

            let mut add_check = |assert_cond, bound_scalar| {
                let mut requires_check = true;
                if let Operand::Constant(const_op) = operand {
                    if let Const::Val(ConstValue::Scalar(Scalar::Int(scalar)), _) = const_op.const_
                    {
                        if (assert_cond == BinOp::Le && scalar <= bound_scalar)
                            || (assert_cond == BinOp::Gt && scalar >= bound_scalar)
                        {
                            requires_check = false;
                        }
                    };
                }

                if requires_check {
                    let max_operand = Operand::const_from_scalar(
                        self.tcx,
                        op_ty,
                        Scalar::Int(bound_scalar),
                        Span::default(),
                    );
                    self.checks
                        .push((location, assert_cond, operand.clone(), max_operand));
                }
            };

            if let Some(max_scalar) = max_scalar {
                add_check(BinOp::Le, max_scalar);
            }
            if let Some(min_scalar) = min_scalar {
                add_check(BinOp::Gt, min_scalar);
            }
        }
    }
}

impl<'tcx, 'pass> Visitor<'tcx> for LossyIntCastVisitor<'tcx, 'pass> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        self.process_rvalue(rvalue, location);
        self.super_rvalue(rvalue, location);
    }
}
