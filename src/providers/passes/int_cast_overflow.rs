//! `rustc` `MirPass` for adding integer cast overflow checks.

use rustc_abi::Size;
use rustc_const_eval::interpret::Scalar;
use rustc_middle::{
    mir::{
        visit::Visitor, Body, CastKind, Const, ConstValue, HasLocalDecls, LocalDecls, Location,
        MirPass, Operand, Rvalue,
    },
    ty::{ScalarInt, TyCtxt, TyKind},
};
use rustc_span::Span;
use rustc_type_ir::{IntTy, UintTy};

use crate::{
    providers::annotate::{self, Annotation, CondOp},
    utils,
};

/// Adds integer cast overflow checks.
pub struct IntCastOverflowChecks;

impl<'tcx> MirPass<'tcx> for IntCastOverflowChecks {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let mut visitor = LossyIntCastVisitor::new(tcx, body.local_decls());
        visitor.visit_body(body);

        // Adds integer cast overflow checks.
        annotate::add_annotations(visitor.checks, body, tcx);
    }
}

/// Collects locations and operands for lossy integer cast operations.
struct LossyIntCastVisitor<'tcx, 'pass> {
    tcx: TyCtxt<'tcx>,
    local_decls: &'pass LocalDecls<'tcx>,
    /// A list of integer cast overflow/underflow checks.
    checks: Vec<Annotation<'tcx>>,
}

impl<'tcx, 'pass> LossyIntCastVisitor<'tcx, 'pass> {
    fn new(tcx: TyCtxt<'tcx>, local_decls: &'pass LocalDecls<'tcx>) -> Self {
        Self {
            tcx,
            local_decls,
            checks: Vec::new(),
        }
    }

    /// Checks `Rvalue`s for lossy integer cast operations and required describes overflow checks.
    fn process_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Cast(CastKind::IntToInt, operand, ty) = rvalue {
            // Retrieves the bitwidth for integer type of the operand.
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

            // Declares the maximum bound for the integer type (if any).
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

            // Declares the minimum bound for the integer type (if any).
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

            // Declares cast overflow checks (if necessary).
            let mut add_check = |assert_cond, bound_scalar| {
                let mut requires_check = true;
                if let Operand::Constant(const_op) = operand {
                    if let Const::Val(ConstValue::Scalar(Scalar::Int(scalar)), _) = const_op.const_
                    {
                        if (assert_cond == CondOp::Le && scalar <= bound_scalar)
                            || (assert_cond == CondOp::Gt && scalar >= bound_scalar)
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
                    self.checks.push(Annotation::CastOverflow(
                        location,
                        assert_cond,
                        operand.clone(),
                        max_operand,
                    ));
                }
            };
            if let Some(max_scalar) = max_scalar {
                add_check(CondOp::Le, max_scalar);
            }
            if let Some(min_scalar) = min_scalar {
                add_check(CondOp::Gt, min_scalar);
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
