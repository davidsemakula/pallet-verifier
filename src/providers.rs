//! `rustc` providers for overriding queries.

use std::env;

use rustc_abi::{Align, Size};
use rustc_const_eval::interpret::{Allocation, Scalar};
use rustc_hir::LangItem;
use rustc_middle::{
    mir::{
        visit::Visitor, BasicBlockData, BinOp, Body, CallSource, CastKind, Const, ConstOperand,
        ConstValue, HasLocalDecls, LocalDecl, LocalDecls, Location, MirPass, Operand, Place,
        Rvalue, Statement, StatementKind, SwitchTargets, Terminator, TerminatorKind, UnwindAction,
    },
    query,
    ty::{ScalarInt, Ty, TyCtxt, TyKind},
};
use rustc_span::{def_id::LocalDefId, source_map::dummy_spanned, Span};
use rustc_type_ir::{IntTy, UintTy};

use crate::ENV_TARGET_POINTER_WIDTH;

/// Overrides the `optimized_mir` query.
pub fn optimized_mir(tcx: TyCtxt<'_>, did: LocalDefId) -> &Body<'_> {
    let mut providers = query::Providers::default();
    rustc_mir_transform::provide(&mut providers);
    let mut body = (providers.optimized_mir)(tcx, did).clone();

    let pass = IntCastOverflowChecks;
    pass.run_pass(tcx, &mut body);

    tcx.arena.alloc(body)
}

/// Adds integer cast overflow checks.
struct IntCastOverflowChecks;

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

        // Creates panic handle.
        let panic_def_id = tcx
            .lang_items()
            .get(LangItem::Panic)
            .expect("Expected panic lang item");
        let panic_msg = "attempt to cast with overflow".as_bytes();
        let panic_msg_const = ConstValue::Slice {
            data: tcx.mk_const_alloc(Allocation::from_bytes(
                panic_msg,
                Align::ONE,
                rustc_ast::Mutability::Not,
            )),
            meta: panic_msg.len() as u64,
        };
        let panic_msg_op = Operand::Constant(Box::new(ConstOperand {
            span: Span::default(),
            user_ty: None,
            const_: Const::from_value(panic_msg_const, Ty::new_static_str(tcx)),
        }));
        let panic_generics = tcx.generics_of(panic_def_id);
        let panic_host_param_def = panic_generics
            .params
            .first()
            .expect("Expected `host` generic param");
        let panic_host_param_value = panic_host_param_def
            .default_value(tcx)
            .expect("Expected `host` generic param default value")
            .skip_binder();
        let panic_handle =
            Operand::function_handle(tcx, panic_def_id, [panic_host_param_value], Span::default());

        // Adds integer cast overflow checks.
        for (location, assert_cond, val_operand, bound_operand) in checks {
            let Some(basic_block) = body.basic_blocks.get(location.block) else {
                continue;
            };
            let Some(cast_stmnt) = basic_block.statements.get(location.statement_index) else {
                continue;
            };
            let source_info = cast_stmnt.source_info;

            // Extracts predecessors and successors.
            let (predecessors, successors) =
                basic_block.statements.split_at(location.statement_index);
            let mut predecessors = predecessors.to_vec();
            let successors = successors.to_vec();
            let terminator = basic_block.terminator.clone();

            // Adds condition statement.
            let cond_ty = Ty::new(tcx, TyKind::Bool);
            let cond_local_decl = LocalDecl::with_source_info(cond_ty, source_info);
            let cond_local = body.local_decls.push(cond_local_decl);
            let cond_place = Place::from(cond_local);
            let cond_rvalue = Rvalue::BinaryOp(assert_cond, Box::new((val_operand, bound_operand)));
            let cond_stmt = Statement {
                source_info,
                kind: StatementKind::Assign(Box::new((cond_place, cond_rvalue))),
            };
            predecessors.push(cond_stmt);

            // Creates panic call.
            let panic_ty = Ty::new(tcx, TyKind::Never);
            let panic_local_decl = LocalDecl::with_source_info(panic_ty, source_info);
            let panic_local = body.local_decls.push(panic_local_decl);
            let panic_place = Place::from(panic_local);
            let panic_call = Terminator {
                source_info,
                kind: TerminatorKind::Call {
                    func: panic_handle.clone(),
                    args: vec![dummy_spanned(panic_msg_op.clone())],
                    destination: panic_place,
                    target: None,
                    unwind: UnwindAction::Continue,
                    call_source: CallSource::Misc,
                    fn_span: Span::default(),
                },
            };

            // Adds successor block.
            let basic_blocks = body.basic_blocks_mut();
            let mut successor_block_data = BasicBlockData::new(terminator);
            successor_block_data.statements = successors;
            let successor_block = basic_blocks.push(successor_block_data);

            // Adds panic block.
            let panic_block_data = BasicBlockData::new(Some(panic_call));
            let panic_block = basic_blocks.push(panic_block_data);

            // Updates terminator.
            let targets = SwitchTargets::new([(0u128, panic_block)].into_iter(), successor_block);
            let terminator_check = Terminator {
                source_info,
                kind: TerminatorKind::SwitchInt {
                    discr: Operand::Move(cond_place),
                    targets,
                },
            };
            basic_blocks[location.block].statements = predecessors;
            basic_blocks[location.block].terminator = Some(terminator_check);
        }
    }
}

pub const HOST_POINTER_WIDTH: usize = std::mem::size_of::<usize>() * 8;

/// Collects locations and operands for lossy integer cast operations.
struct LossyIntCastVisitor<'tcx, 'pass> {
    tcx: TyCtxt<'tcx>,
    local_decls: &'pass LocalDecls<'tcx>,
    /// A list of location, assert condition/comparison operation, value and bound operand tuples
    /// for overflow/underflow checks.
    checks: Vec<(Location, BinOp, Operand<'tcx>, Operand<'tcx>)>,
}

impl<'tcx, 'pass> LossyIntCastVisitor<'tcx, 'pass> {
    pub fn new(tcx: TyCtxt<'tcx>, local_decls: &'pass LocalDecls<'tcx>) -> Self {
        Self {
            tcx,
            local_decls,
            checks: Vec::new(),
        }
    }
}

impl<'tcx, 'pass> Visitor<'tcx> for LossyIntCastVisitor<'tcx, 'pass> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Cast(CastKind::IntToInt, operand, ty) = rvalue {
            let op_ty = operand.ty(self.local_decls, self.tcx);
            let target_pointer_width = match env::var(ENV_TARGET_POINTER_WIDTH).as_deref() {
                Ok("16") => 16,
                Ok("32") => 32,
                Ok("64") => 64,
                _ => HOST_POINTER_WIDTH,
            };
            let bit_width = match op_ty.kind() {
                TyKind::Uint(uint_ty) => uint_ty.normalize(target_pointer_width as u32).bit_width(),
                TyKind::Int(int_ty) => int_ty.normalize(target_pointer_width as u32).bit_width(),
                _ => None,
            };
            if let Some(bit_width) = bit_width {
                let host_size = Size::from_bits(bit_width);
                let max_scalar = match (ty.kind(), op_ty.kind()) {
                    // i8
                    (
                        TyKind::Int(IntTy::I8),
                        TyKind::Int(
                            IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize,
                        )
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
                        | TyKind::Int(
                            IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize,
                        ),
                    ) => ScalarInt::try_from_uint(u8::MAX, host_size),
                    // i16
                    (
                        TyKind::Int(IntTy::I16 | IntTy::Isize),
                        TyKind::Int(IntTy::I32 | IntTy::I64 | IntTy::I128)
                        | TyKind::Uint(
                            UintTy::U16 | UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize,
                        ),
                    ) if target_pointer_width == 16 => ScalarInt::try_from_int(i16::MAX, host_size),
                    (
                        TyKind::Int(IntTy::I16),
                        TyKind::Int(IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize)
                        | TyKind::Uint(
                            UintTy::U16 | UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize,
                        ),
                    ) if target_pointer_width != 16 => ScalarInt::try_from_int(i16::MAX, host_size),
                    // u16
                    (
                        TyKind::Uint(UintTy::U16 | UintTy::Usize),
                        TyKind::Uint(UintTy::U32 | UintTy::U64 | UintTy::U128)
                        | TyKind::Int(IntTy::I32 | IntTy::I64 | IntTy::I128),
                    ) if target_pointer_width == 16 => {
                        ScalarInt::try_from_uint(u16::MAX, host_size)
                    }
                    (
                        TyKind::Uint(UintTy::U16),
                        TyKind::Uint(UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize)
                        | TyKind::Int(IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize),
                    ) if target_pointer_width != 16 => {
                        ScalarInt::try_from_uint(u16::MAX, host_size)
                    }
                    // i32
                    (
                        TyKind::Int(IntTy::I32 | IntTy::Isize),
                        TyKind::Int(IntTy::I64 | IntTy::I128)
                        | TyKind::Uint(UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize),
                    ) if target_pointer_width == 32 => ScalarInt::try_from_int(i32::MAX, host_size),
                    (
                        TyKind::Int(IntTy::I32),
                        TyKind::Int(IntTy::I64 | IntTy::I128)
                        | TyKind::Uint(UintTy::U32 | UintTy::U64 | UintTy::U128),
                    ) if target_pointer_width == 16 => ScalarInt::try_from_int(i32::MAX, host_size),
                    (
                        TyKind::Int(IntTy::I32),
                        TyKind::Int(IntTy::I64 | IntTy::I128 | IntTy::Isize)
                        | TyKind::Uint(UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize),
                    ) if target_pointer_width == 64 => ScalarInt::try_from_int(i32::MAX, host_size),
                    // u32
                    (
                        TyKind::Uint(UintTy::U32 | UintTy::Usize),
                        TyKind::Uint(UintTy::U64 | UintTy::U128)
                        | TyKind::Int(IntTy::I64 | IntTy::I128),
                    ) if target_pointer_width == 32 => {
                        ScalarInt::try_from_uint(u32::MAX, host_size)
                    }
                    (
                        TyKind::Uint(UintTy::U32),
                        TyKind::Uint(UintTy::U64 | UintTy::U128)
                        | TyKind::Int(IntTy::I64 | IntTy::I128),
                    ) if target_pointer_width == 16 => {
                        ScalarInt::try_from_uint(u32::MAX, host_size)
                    }
                    (
                        TyKind::Uint(UintTy::U32),
                        TyKind::Uint(UintTy::U64 | UintTy::U128 | UintTy::Usize)
                        | TyKind::Int(IntTy::I64 | IntTy::I128 | IntTy::Isize),
                    ) if target_pointer_width == 64 => {
                        ScalarInt::try_from_uint(u32::MAX, host_size)
                    }
                    // i64
                    (
                        TyKind::Int(IntTy::I64 | IntTy::Isize),
                        TyKind::Int(IntTy::I128)
                        | TyKind::Uint(UintTy::U64 | UintTy::U128 | UintTy::Usize),
                    ) if target_pointer_width == 64 => ScalarInt::try_from_int(i64::MAX, host_size),
                    (
                        TyKind::Int(IntTy::I64),
                        TyKind::Int(IntTy::I128) | TyKind::Uint(UintTy::U64 | UintTy::U128),
                    ) if target_pointer_width != 64 => ScalarInt::try_from_int(i64::MAX, host_size),
                    // u64
                    (
                        TyKind::Uint(UintTy::U64 | UintTy::Usize),
                        TyKind::Uint(UintTy::U128) | TyKind::Int(IntTy::I128),
                    ) if target_pointer_width == 64 => {
                        ScalarInt::try_from_uint(u64::MAX, host_size)
                    }
                    (
                        TyKind::Uint(UintTy::U64),
                        TyKind::Uint(UintTy::U128) | TyKind::Int(IntTy::I128),
                    ) if target_pointer_width != 64 => {
                        ScalarInt::try_from_uint(u64::MAX, host_size)
                    }
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
                        TyKind::Int(
                            IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize,
                        ),
                    ) => ScalarInt::try_from_int(i8::MIN, host_size),
                    // i16
                    (
                        TyKind::Int(IntTy::I16 | IntTy::Isize),
                        TyKind::Int(IntTy::I32 | IntTy::I64 | IntTy::I128),
                    ) if target_pointer_width == 16 => ScalarInt::try_from_int(i16::MIN, host_size),
                    (
                        TyKind::Int(IntTy::I16),
                        TyKind::Int(IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize),
                    ) if target_pointer_width != 16 => ScalarInt::try_from_int(i16::MIN, host_size),
                    // i32
                    (
                        TyKind::Int(IntTy::I32 | IntTy::Isize),
                        TyKind::Int(IntTy::I64 | IntTy::I128),
                    ) if target_pointer_width == 32 => ScalarInt::try_from_int(i32::MIN, host_size),
                    (TyKind::Int(IntTy::I32), TyKind::Int(IntTy::I64 | IntTy::I128))
                        if target_pointer_width == 16 =>
                    {
                        ScalarInt::try_from_int(i32::MIN, host_size)
                    }
                    (
                        TyKind::Int(IntTy::I32),
                        TyKind::Int(IntTy::I64 | IntTy::I128 | IntTy::Isize),
                    ) if target_pointer_width == 64 => ScalarInt::try_from_int(i32::MIN, host_size),
                    // i64
                    (TyKind::Int(IntTy::I64 | IntTy::Isize), TyKind::Int(IntTy::I128))
                        if target_pointer_width == 64 =>
                    {
                        ScalarInt::try_from_int(i64::MIN, host_size)
                    }
                    (TyKind::Int(IntTy::I64), TyKind::Int(IntTy::I128))
                        if target_pointer_width != 64 =>
                    {
                        ScalarInt::try_from_int(i64::MIN, host_size)
                    }
                    _ => None,
                };

                let mut add_check = |assert_cond, bound_scalar| {
                    let mut requires_check = true;
                    if let Operand::Constant(const_op) = operand {
                        if let Const::Val(ConstValue::Scalar(Scalar::Int(scalar)), _) =
                            const_op.const_
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
        self.super_rvalue(rvalue, location);
    }
}
