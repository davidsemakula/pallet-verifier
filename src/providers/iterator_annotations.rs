//! `rustc` `MirPass` for adding annotations for `Iterator` invariants.

use rustc_abi::Size;
use rustc_const_eval::interpret::Scalar;
use rustc_data_structures::graph::{dominators::Dominators, WithStartNode, WithSuccessors};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::LangItem;
use rustc_middle::{
    mir::{
        visit::Visitor, BasicBlock, BasicBlockData, BasicBlocks, BinOp, Body, BorrowKind,
        CallSource, Const, ConstValue, HasLocalDecls, LocalDecl, LocalDecls, Location, MirPass,
        Operand, Place, PlaceElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
        UnwindAction, RETURN_PLACE,
    },
    ty::{
        AssocKind, GenericArg, ImplSubject, List, Region, ScalarInt, Ty, TyCtxt, TyKind, TypeAndMut,
    },
};
use rustc_span::{
    def_id::DefId,
    source_map::{dummy_spanned, Spanned},
    symbol::Ident,
    Span, Symbol,
};
use rustc_target::abi::VariantIdx;
use rustc_type_ir::UintTy;

use itertools::Itertools;

use crate::utils;

/// Adds invariant annotations to iterators.
pub struct IteratorAnnotations;

impl<'tcx> MirPass<'tcx> for IteratorAnnotations {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let mut visitor = IteratorVisitor::new(tcx, &body.basic_blocks, body.local_decls());
        visitor.visit_body(body);

        let mut annotations = visitor.annotations;
        if annotations.is_empty() {
            return;
        }
        // Reverse sorts annotation declarations by location.
        annotations.sort_by(|a, b| b.location().cmp(a.location()));

        // Creates `mirai_assume` annotation handle.
        let mirai_assume_def_id = utils::mirai_annotation_fn("mirai_assume", tcx)
            .expect("Expected a fn def for `mirai_assume`");
        let mirai_assume_handle =
            Operand::function_handle(tcx, mirai_assume_def_id, [], Span::default());

        // Creates `isize::MAX` operand.
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
        let usize_ty = Ty::new_uint(tcx, UintTy::Usize);
        let isize_max_operand = Operand::const_from_scalar(
            tcx,
            usize_ty,
            Scalar::Int(isize_max_scalar),
            Span::default(),
        );

        // Adds iterator annotations.
        for annotation in annotations {
            let location = *annotation.location();
            let Some(basic_block) = body.basic_blocks.get(location.block) else {
                continue;
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
                continue;
            };

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

            // Adds annotation argument (and related) statements and/or blocks.
            let arg_local_decl =
                LocalDecl::with_source_info(Ty::new(tcx, TyKind::Bool), source_info);
            let arg_local = body.local_decls.push(arg_local_decl);
            let arg_place = Place::from(arg_local);
            let (target_block, target_block_statements) = match annotation {
                Annotation::Isize(_, op_place) => {
                    // Creates `isize::MAX` bound statement.
                    let arg_rvalue = Rvalue::BinaryOp(
                        BinOp::Le,
                        Box::new((Operand::Copy(op_place), isize_max_operand.clone())),
                    );
                    let arg_stmt = Statement {
                        source_info,
                        kind: StatementKind::Assign(Box::new((arg_place, arg_rvalue))),
                    };
                    predecessors.push(arg_stmt);

                    // Returns target block and statements.
                    (location.block, predecessors)
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
                            let current_arg_ref_rvalue = Rvalue::Ref(
                                collection_region,
                                BorrowKind::Shared,
                                current_arg_place,
                            );
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
                    (current_block, current_statements)
                }
            };

            // Creates `mirai_assume` annotation call.
            let annotation_ty = Ty::new(tcx, TyKind::Never);
            let annotation_local_decl = LocalDecl::with_source_info(annotation_ty, source_info);
            let annotation_local = body.local_decls.push(annotation_local_decl);
            let annotation_place = Place::from(annotation_local);
            let annotation_call = Terminator {
                source_info,
                kind: TerminatorKind::Call {
                    func: mirai_assume_handle.clone(),
                    args: vec![dummy_spanned(Operand::Move(arg_place))],
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
    }
}

/// Captures the required info for adding an `Iterator` related annotation.
#[derive(Debug)]
enum Annotation<'tcx> {
    Isize(Location, Place<'tcx>),
    Len(
        Location,
        BinOp,
        Place<'tcx>,
        Place<'tcx>,
        Region<'tcx>,
        Vec<(DefId, &'tcx List<GenericArg<'tcx>>, Ty<'tcx>)>,
    ),
}

impl<'tcx> Annotation<'tcx> {
    fn location(&self) -> &Location {
        match &self {
            Annotation::Isize(location, ..) => location,
            Annotation::Len(location, ..) => location,
        }
    }
}

/// Collects iterator annotations.
struct IteratorVisitor<'tcx, 'pass> {
    tcx: TyCtxt<'tcx>,
    basic_blocks: &'pass BasicBlocks<'tcx>,
    local_decls: &'pass LocalDecls<'tcx>,
    iterator_assoc_items: FxHashMap<Symbol, DefId>,
    /// A list of `Iterator` annotation descriptions.
    annotations: Vec<Annotation<'tcx>>,
}

impl<'tcx, 'pass> IteratorVisitor<'tcx, 'pass> {
    fn new(
        tcx: TyCtxt<'tcx>,
        basic_blocks: &'pass BasicBlocks<'tcx>,
        local_decls: &'pass LocalDecls<'tcx>,
    ) -> Self {
        let iterator_trait_def_id = tcx
            .lang_items()
            .get(LangItem::Iterator)
            .expect("Expected `std::iter::Iterator` lang item");
        let iterator_assoc_items = tcx
            .associated_items(iterator_trait_def_id)
            .in_definition_order()
            .map(|assoc_item| (assoc_item.name, assoc_item.def_id))
            .collect();
        Self {
            tcx,
            basic_blocks,
            local_decls,
            iterator_assoc_items,
            annotations: Vec::new(),
        }
    }

    /// Analyzes and annotates `Iterator` terminators.
    fn process_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } = &terminator.kind
        {
            // Retrieves `fn` definition (if any).
            let Some((def_id, ..)) = func.const_fn_def() else {
                return;
            };

            // Handles calls to `std::iter::Iterator::next`.
            let iterator_next_def_id = *self
                .iterator_assoc_item_def_id("next")
                .expect("Expected DefId for `std::iter::Iterator::next`");
            if def_id == iterator_next_def_id {
                self.process_iterator_next(args, destination, location);
            }

            // Handles calls to `std::iter::Iterator::position` and `std::iter::Iterator::rposition`.
            let iterator_position_def_id = *self
                .iterator_assoc_item_def_id("position")
                .expect("Expected DefId for `std::iter::Iterator::position`");
            let iterator_rposition_def_id = *self
                .iterator_assoc_item_def_id("rposition")
                .expect("Expected DefId for `std::iter::Iterator::rposition`");
            if def_id == iterator_position_def_id || def_id == iterator_rposition_def_id {
                self.process_iterator_position(args, destination, target.as_ref(), location);
            }

            // Handles calls to `std::iter::Iterator::count`.
            let iterator_count_def_id = *self
                .iterator_assoc_item_def_id("count")
                .expect("Expected DefId for `std::iter::Iterator::count`");
            if def_id == iterator_count_def_id {
                self.process_iterator_count(args, destination, target.as_ref(), location);
            }

            // Handles calls to collection `len` methods.
            if self
                .tcx
                .opt_item_name(def_id)
                .is_some_and(|name| name.as_str() == "len")
                && args.len() == 1
            {
                self.process_len(args, destination, target.as_ref(), location);
            }

            // Handles calls to slice `binary_search` methods.
            if self.tcx.opt_item_name(def_id).is_some_and(|name| {
                matches!(
                    name.as_str(),
                    "binary_search" | "binary_search_by" | "binary_search_by_key"
                )
            }) && is_slice_assoc_item(def_id, self.tcx)
            {
                self.process_binary_search(args, destination, target.as_ref(), location);
            }
        }
    }

    /// Analyzes and annotates calls to `std::iter::Iterator::next`.
    fn process_iterator_next(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        location: Location,
    ) {
        // Finds place for `std::iter::Iterator::next` operand/arg.
        let iterator_next_arg = args.first().expect("Expected an arg for `Iterator::next`");
        let Some(iterator_next_arg_place) = iterator_next_arg.node.place() else {
            return;
        };

        // Finds place and basic block (if any) of innermost iterator subject to which
        // no "growing" iterator adapters are applied.
        let dominators = self.basic_blocks.dominators();
        let Some((mut iterator_subject_place, mut iterator_subject_bb)) =
            find_size_invariant_iterator_subject(
                iterator_next_arg_place,
                location.block,
                self.basic_blocks,
                self.local_decls,
                dominators,
                self.tcx,
            )
        else {
            return;
        };

        // Finds place and basic block for a slice `Iterator` operand/arg (if any).
        if self.place_ty(iterator_subject_place).peel_refs().is_slice() {
            let slice_def_call = find_pre_anchor_assign_terminator(
                iterator_subject_place,
                iterator_subject_bb,
                location.block,
                self.basic_blocks,
                dominators,
            );
            let Some((slice_deref_arg_place, slice_deref_bb)) =
                slice_def_call.and_then(|(terminator, bb)| {
                    deref_operand(&terminator, self.tcx).map(|place| (place, bb))
                })
            else {
                return;
            };
            iterator_subject_place = slice_deref_arg_place;
            iterator_subject_bb = slice_deref_bb;
        }

        // Only continues if `Iterator` target either has a length/size with `isize::MAX` maxima,
        // or has a known length/size returning function and is passed by reference.
        let iterator_subject_ty = self.place_ty(iterator_subject_place);
        let is_isize_bound = is_isize_bound_collection(iterator_subject_ty, self.tcx);
        let len_call_info = collection_len_call(iterator_subject_ty, self.tcx);
        let len_bound_info = len_call_info.and_then(|len_call_info| {
            let collection_place_info = deref_place_recursive(
                iterator_subject_place,
                iterator_subject_bb,
                self.basic_blocks,
            )
            .or_else(|| {
                if let TyKind::Ref(region, _, _) = iterator_subject_ty.kind() {
                    Some((iterator_subject_place, *region))
                } else {
                    None
                }
            });
            collection_place_info
                .map(|(collection_place, region)| (collection_place, region, len_call_info))
        });
        if !is_isize_bound && len_bound_info.is_none() {
            return;
        }

        // Collects all recurring/loop blocks and reachable immediate loop successor blocks (if any),
        // using the block containing the `std::iter::Iterator::next` call as the anchor block.
        let loop_blocks = collect_loop_blocks(location.block, self.basic_blocks, dominators);
        if loop_blocks.is_empty() {
            return;
        }
        let loop_successors =
            collect_reachable_loop_successors(location.block, &loop_blocks, self.basic_blocks);

        // Composes annotations for loop invariants based on collection length/size bounds,
        // and indice increment operations.
        let mut pre_loop_len_maxima_places = FxHashSet::default();
        for bb in &loop_blocks {
            let bb_data = &self.basic_blocks[*bb];
            for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
                let inc_invariant_places = unit_incr_assign_places(stmt).filter(|(_, op_place)| {
                    is_zero_initialized_before_anchor(
                        *op_place,
                        location.block,
                        self.basic_blocks,
                        dominators,
                    ) || is_enumerate_index(
                        *op_place,
                        *destination,
                        iterator_next_arg_place,
                        &loop_blocks,
                        self.basic_blocks,
                        self.local_decls,
                        self.tcx,
                    )
                });
                if let Some((_, op_place)) = inc_invariant_places {
                    // Declares an `isize::MAX` bound annotation.
                    if is_isize_bound {
                        self.annotations.push(Annotation::Isize(
                            Location {
                                block: *bb,
                                statement_index: stmt_idx,
                            },
                            op_place,
                        ));
                    }

                    // Tracks operand place for loop successor annotations (if any).
                    if len_bound_info.is_some() && !loop_successors.is_empty() {
                        pre_loop_len_maxima_places.insert(op_place);
                    }
                }
            }
        }

        // Composes collection length/size bound annotations for reachable loop successors (if any).
        if !loop_successors.is_empty() && !pre_loop_len_maxima_places.is_empty() {
            if let Some((collection_place, region, len_call_info)) = len_bound_info {
                for bb in loop_successors {
                    for len_maxima_place in &pre_loop_len_maxima_places {
                        // Declares a collection length/size bound annotation.
                        self.annotations.push(Annotation::Len(
                            Location {
                                block: bb,
                                statement_index: 0,
                            },
                            BinOp::Lt,
                            *len_maxima_place,
                            collection_place,
                            region,
                            len_call_info.clone(),
                        ));
                    }
                }
            }
        }
    }

    /// Analyzes and annotates calls to `std::iter::Iterator::position` and `std::iter::Iterator::rposition`.
    fn process_iterator_position(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: Option<&BasicBlock>,
        location: Location,
    ) {
        // Finds place for `std::iter::Iterator::position` operand/arg.
        let iter_pos_arg = args
            .first()
            .expect("Expected an arg for `Iterator::position`");
        let Some(iter_pos_arg_place) = iter_pos_arg.node.place() else {
            return;
        };

        // Finds place and basic block for an `Iterator` by reference converter method operand/arg (if any).
        // NOTE: We only care about `Iterator`s by reference because our length annotation requires
        // the target collection to be passed by reference (not value) so that
        // it's length/size can still be referenced after this iteration.
        let dominators = self.basic_blocks.dominators();
        let iter_by_ref_arg_def_call = find_pre_anchor_assign_terminator(
            iter_pos_arg_place,
            location.block,
            location.block,
            self.basic_blocks,
            dominators,
        );
        let Some((iter_by_ref_place, iter_by_ref_bb)) =
            iter_by_ref_arg_def_call.and_then(|(terminator, bb)| {
                iter_by_ref_operand(&terminator, self.tcx).map(|place| (place, bb))
            })
        else {
            return;
        };
        let iter_by_ref_ty_def_call = find_pre_anchor_assign_terminator(
            iter_by_ref_place,
            iter_by_ref_bb,
            location.block,
            self.basic_blocks,
            dominators,
        );
        let Some((iter_by_ref_deref_arg_place, iter_by_ref_deref_bb)) = iter_by_ref_ty_def_call
            .and_then(|(terminator, bb)| {
                deref_operand(&terminator, self.tcx).map(|place| (place, bb))
            })
        else {
            return;
        };

        // Only continues if `Iterator` target has a known length/size returning function
        // and is passed by reference.
        let Some(len_call_info) =
            collection_len_call(self.place_ty(iter_by_ref_deref_arg_place), self.tcx)
        else {
            return;
        };
        let collection_place_info = deref_place_recursive(
            iter_by_ref_deref_arg_place,
            iter_by_ref_deref_bb,
            self.basic_blocks,
        )
        .or_else(|| {
            if let TyKind::Ref(region, _, _) = self.place_ty(iter_by_ref_deref_arg_place).kind() {
                Some((iter_by_ref_deref_arg_place, *region))
            } else {
                None
            }
        });
        let Some((collection_place, region)) = collection_place_info else {
            return;
        };

        // Tracks `Option::Some` switch target info of return value of
        // `std::iter::Iterator::position` or `std::iter::Iterator::rposition`.
        // Also tracks variant "safe" transformations (e.g. `ControlFlow::Continue` and
        // `Result::Ok` transformations - see [`track_switch_target_transformations`] for details).
        let mut switch_target_place = *destination;
        let mut switch_target_bb = location.block;
        let mut switch_target_variant_name = "Some".to_string();
        let mut switch_target_variant_idx = variant_idx(LangItem::OptionSome, self.tcx);
        if let Some(target) = target {
            track_safe_primary_opt_result_variant_transformations(
                &mut switch_target_place,
                &mut switch_target_bb,
                &mut switch_target_variant_name,
                &mut switch_target_variant_idx,
                *target,
                self.basic_blocks,
                self.tcx,
            );
        }

        // Finds `Option::Some` (or equivalent safe transformation) target blocks
        // for switches based on the discriminant of return value of
        // `std::iter::Iterator::position` or `std::iter::Iterator::rposition` in successor blocks.
        for target_bb in collect_switch_targets_for_discr_value(
            switch_target_place,
            switch_target_variant_idx.as_u32() as u128,
            switch_target_bb,
            self.basic_blocks,
        ) {
            for (stmt_idx, stmt) in self.basic_blocks[target_bb].statements.iter().enumerate() {
                // Finds variant downcast to `usize` places (if any) for the switch target variant.
                let Some(downcast_place) = variant_downcast_to_usize_place(
                    switch_target_place,
                    &switch_target_variant_name,
                    switch_target_variant_idx,
                    stmt,
                    self.tcx,
                ) else {
                    continue;
                };

                // Declares a collection length/size bound annotation.
                self.annotations.push(Annotation::Len(
                    Location {
                        block: target_bb,
                        statement_index: stmt_idx + 1,
                    },
                    BinOp::Lt,
                    downcast_place,
                    collection_place,
                    region,
                    len_call_info.clone(),
                ));
            }
        }
    }

    /// Analyzes and annotates calls to `std::iter::Iterator::next`.
    fn process_iterator_count(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: Option<&BasicBlock>,
        location: Location,
    ) {
        // Finds place for `std::iter::Iterator::next` operand/arg.
        let iterator_next_arg = args.first().expect("Expected an arg for `Iterator::next`");
        let Some(iterator_next_arg_place) = iterator_next_arg.node.place() else {
            return;
        };

        // Only continues if the terminator has a target basic block.
        let Some(target) = target else {
            return;
        };

        // Finds place and basic block (if any) of innermost iterator subject to which
        // no "growing" iterator adapters are applied.
        let dominators = self.basic_blocks.dominators();
        let Some((mut iterator_subject_place, mut iterator_subject_bb)) =
            find_size_invariant_iterator_subject(
                iterator_next_arg_place,
                location.block,
                self.basic_blocks,
                self.local_decls,
                dominators,
                self.tcx,
            )
        else {
            return;
        };

        // Length invariant annotation are added at the beginning of the next block.
        let annotation_location = Location {
            block: *target,
            statement_index: 0,
        };

        // Finds place and basic block for a slice `Iterator` operand/arg (if any).
        if self.place_ty(iterator_subject_place).peel_refs().is_slice() {
            // Adds a slice length/size bound annotation.
            self.add_slice_len_annotation(
                annotation_location,
                BinOp::Eq,
                *destination,
                iterator_subject_place,
            );

            // Finds `Deref` arg/operand for slice.
            let slice_def_call = find_pre_anchor_assign_terminator(
                iterator_subject_place,
                iterator_subject_bb,
                location.block,
                self.basic_blocks,
                dominators,
            );
            let Some((slice_deref_arg_place, slice_deref_bb)) =
                slice_def_call.and_then(|(terminator, bb)| {
                    deref_operand(&terminator, self.tcx).map(|place| (place, bb))
                })
            else {
                return;
            };
            iterator_subject_place = slice_deref_arg_place;
            iterator_subject_bb = slice_deref_bb;
        }

        // Declares an `isize::MAX` bound annotation (if appropriate).
        let iterator_subject_ty = self.place_ty(iterator_subject_place);
        let is_isize_bound =
            is_isize_bound_collection(self.place_ty(iterator_subject_place), self.tcx);
        if is_isize_bound {
            self.annotations.push(Annotation::Isize(
                Location {
                    block: *target,
                    statement_index: 0,
                },
                *destination,
            ));
        }

        // Declares a collection length/size bound annotation (if appropriate).
        let len_call_info = collection_len_call(iterator_subject_ty, self.tcx);
        if let Some(len_call_info) = len_call_info {
            let collection_place_info = deref_place_recursive(
                iterator_subject_place,
                iterator_subject_bb,
                self.basic_blocks,
            )
            .or_else(|| {
                if let TyKind::Ref(region, _, _) = iterator_subject_ty.kind() {
                    Some((iterator_subject_place, *region))
                } else {
                    None
                }
            });
            if let Some((collection_place, region)) = collection_place_info {
                self.annotations.push(Annotation::Len(
                    Location {
                        block: *target,
                        statement_index: 0,
                    },
                    BinOp::Eq,
                    *destination,
                    collection_place,
                    region,
                    len_call_info.clone(),
                ));
            }
        }
    }

    /// Analyzes and annotates calls to collection `len` methods.
    fn process_len(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: Option<&BasicBlock>,
        _: Location,
    ) {
        // Only continues if `len` method operand/arg has a length/size with `isize::MAX` maxima
        let Some(len_arg) = args.first() else {
            return;
        };
        let len_arg_ty = len_arg.node.ty(self.local_decls, self.tcx);
        if !is_isize_bound_collection(len_arg_ty, self.tcx) {
            return;
        }

        // Only continues if the terminator has a target basic block.
        let Some(target) = target else {
            return;
        };

        // Declares an `isize::MAX` bound annotation.
        self.annotations.push(Annotation::Isize(
            Location {
                block: *target,
                statement_index: 0,
            },
            *destination,
        ));
    }

    /// Analyzes and annotates calls to slice `binary_search` methods.
    fn process_binary_search(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: Option<&BasicBlock>,
        location: Location,
    ) {
        // Finds place for slice `binary_search` operand/arg.
        let binary_search_arg = args
            .first()
            .expect("Expected an arg for slice `binary_search` method");
        let Some(binary_search_arg_place) = binary_search_arg.node.place() else {
            return;
        };

        // Finds place and basic block for a slice `binary_search` operand/arg (if any).
        let dominators = self.basic_blocks.dominators();
        let slice_def_call = find_pre_anchor_assign_terminator(
            binary_search_arg_place,
            location.block,
            location.block,
            self.basic_blocks,
            dominators,
        );
        let Some((slice_deref_arg_place, slice_deref_bb)) =
            slice_def_call.and_then(|(terminator, bb)| {
                deref_operand(&terminator, self.tcx).map(|place| (place, bb))
            })
        else {
            return;
        };

        // Only continues if slice target has a known length/size returning function
        // and is passed by reference.
        let Some(len_call_info) =
            collection_len_call(self.place_ty(slice_deref_arg_place), self.tcx)
        else {
            return;
        };
        let collection_place_info =
            deref_place_recursive(slice_deref_arg_place, slice_deref_bb, self.basic_blocks)
                .or_else(|| {
                    if let TyKind::Ref(region, _, _) = self.place_ty(slice_deref_arg_place).kind() {
                        Some((slice_deref_arg_place, *region))
                    } else {
                        None
                    }
                });
        let Some((collection_place, region)) = collection_place_info else {
            return;
        };

        // Tracks collection length/size bound invariants.
        let mut invariants = Vec::new();

        // Tracks `Result::unwrap_or_else` destination place invariants where
        // the `unwrap_or_else` second arg is an identity function or closure
        // (e.g. `std::convert::identity` or `|x| x`) and Result is the return value of
        // slice `binary_search` methods.
        // Also tracks/allows "safe" transformations before `unwrap_or_else` call
        // (e.g. via `Result::inspect`, `Result::inspect_err` e.t.c).
        // See [`track_safe_result_transformations`] for details.
        if let Some(target) = target {
            let mut unwrap_arg_place = *destination;
            let mut unwrap_arg_def_bb = location.block;
            track_safe_result_transformations(
                &mut unwrap_arg_place,
                &mut unwrap_arg_def_bb,
                *target,
                self.basic_blocks,
                self.tcx,
            );
            let unwrap_place_info =
                call_target(&self.basic_blocks[unwrap_arg_def_bb]).and_then(|next_target| {
                    // Retrieves `Result::unwrap_else` destination place and next target block (if any).
                    let next_bb_data = &self.basic_blocks[next_target];
                    fn crate_adt_and_fn_name_check(
                        crate_name: &str,
                        adt_name: &str,
                        fn_name: &str,
                    ) -> bool {
                        matches!(crate_name, "std" | "core")
                            && adt_name == "Result"
                            && fn_name == "unwrap_or_else"
                    }
                    let (unwrap_dest_place, post_unwrap_target) = safe_transform_destination(
                        unwrap_arg_place,
                        next_bb_data,
                        crate_adt_and_fn_name_check,
                        self.tcx,
                    )?;
                    let next_target_bb = post_unwrap_target?;

                    // Checks that second arg is an identity function or closure and, if true,
                    // returns unwrap destination place and next target.
                    // See [`is_identity_fn`] and [`is_identity_closure`] for details.
                    let unwrap_terminator = next_bb_data.terminator.as_ref()?;
                    let TerminatorKind::Call {
                        args: unwrap_args, ..
                    } = &unwrap_terminator.kind
                    else {
                        return None;
                    };
                    let unwrap_second_arg = unwrap_args.get(1)?;
                    let is_identity = is_identity_fn(&unwrap_second_arg.node, self.tcx)
                        || is_identity_closure(&unwrap_second_arg.node, self.tcx);
                    is_identity.then_some((unwrap_dest_place, next_target_bb))
                });

            if let Some((unwrap_place, post_unwrap_target)) = unwrap_place_info {
                // Declares collection length/size invariant for unwrap place.
                let annotation_location = Location {
                    block: post_unwrap_target,
                    statement_index: 0,
                };
                invariants.push((
                    annotation_location,
                    unwrap_place,
                    // index <= collection length/size for `Result::unwrap_or_else`
                    // where the second arg is an identity function or closure
                    // (e.g. `std::convert::identity` or `|x| x`).
                    BinOp::Le,
                ));
            }
        }

        // Tracks `Result::Ok` switch target info of return value of slice `binary_search` methods.
        // Also tracks variant "safe" transformations (e.g. `ControlFlow::Continue` and
        // `Option::Some` transformations)
        // See [`track_safe_primary_opt_result_variant_transformations`] for details.
        let mut switch_target_place = *destination;
        let mut switch_target_bb = location.block;
        let mut switch_target_variant_name = "Ok".to_string();
        let mut switch_target_variant_idx = variant_idx(LangItem::ResultOk, self.tcx);
        if let Some(target) = target {
            track_safe_primary_opt_result_variant_transformations(
                &mut switch_target_place,
                &mut switch_target_bb,
                &mut switch_target_variant_name,
                &mut switch_target_variant_idx,
                *target,
                self.basic_blocks,
                self.tcx,
            );
        }

        // Tracks `Result::Err` switch target info of return value of slice `binary_search` methods.
        // Also tracks variant "safe" transformations (e.g. to `Option::Some`, then optionally to
        // `ControlFlow::Continue` and `Option::Some` transformations).
        // See [`track_safe_result_err_transformations`] for details.
        let mut switch_target_place_alt = *destination;
        let mut switch_target_bb_alt = location.block;
        let mut switch_target_variant_name_alt = "Err".to_string();
        let mut switch_target_variant_idx_alt = variant_idx(LangItem::ResultErr, self.tcx);
        if let Some(target) = target {
            track_safe_result_err_transformations(
                &mut switch_target_place_alt,
                &mut switch_target_bb_alt,
                &mut switch_target_variant_name_alt,
                &mut switch_target_variant_idx_alt,
                *target,
                self.basic_blocks,
                self.tcx,
            );
        }

        // Collects `Result::Ok` (or equivalent safe transformation) target blocks
        // for switches based on the discriminant of return value of slice `binary_search`
        // in successor blocks.
        let switch_targets = collect_switch_targets_for_discr_value(
            switch_target_place,
            switch_target_variant_idx.as_u32() as u128,
            switch_target_bb,
            self.basic_blocks,
        );

        // Collects `Result::Err` (or equivalent safe transformation) target blocks
        // for switches based on the discriminant of return value of slice `binary_search`
        // in successor blocks.
        let switch_targets_err = collect_switch_targets_for_discr_value(
            switch_target_place_alt,
            switch_target_variant_idx_alt.as_u32() as u128,
            switch_target_bb_alt,
            self.basic_blocks,
        );

        // Declares collection length/size bound invariants
        // for variant downcast to `usize` places (if any) for the switch targets.
        for (target_place, target_variant_name, target_variant_idx, cond_op, targets_blocks) in [
            // `Result::Ok` switch target info.
            (
                switch_target_place,
                &switch_target_variant_name,
                switch_target_variant_idx,
                // index < collection length/size for `Result::Ok`.
                BinOp::Lt,
                switch_targets,
            ),
            // `Result::Err` switch target info.
            (
                switch_target_place_alt,
                &switch_target_variant_name_alt,
                switch_target_variant_idx_alt,
                // index <= collection length/size for `Result::Err`.
                BinOp::Le,
                switch_targets_err,
            ),
        ] {
            for target_bb in targets_blocks {
                for (stmt_idx, stmt) in self.basic_blocks[target_bb].statements.iter().enumerate() {
                    // Finds variant downcast to `usize` places (if any) for the switch target variant.
                    let Some(downcast_place) = variant_downcast_to_usize_place(
                        target_place,
                        target_variant_name,
                        target_variant_idx,
                        stmt,
                        self.tcx,
                    ) else {
                        continue;
                    };

                    // Declares a collection length/size bound invariant.
                    let annotation_location = Location {
                        block: target_bb,
                        statement_index: stmt_idx + 1,
                    };
                    invariants.push((annotation_location, downcast_place, cond_op));
                }
            }
        }

        // Composes collection length/size bound annotations for extracted invariants.
        for (annotation_location, invariant_place, cond_op) in invariants {
            // Adds a collection length/size bound annotation.
            self.annotations.push(Annotation::Len(
                annotation_location,
                cond_op,
                invariant_place,
                collection_place,
                region,
                len_call_info.clone(),
            ));

            // Adds a slice length/size bound annotation.
            self.add_slice_len_annotation(
                annotation_location,
                cond_op,
                invariant_place,
                binary_search_arg_place,
            );
        }
    }

    /// Returns the DefId of an `Iterator` assoc item, given it's name.
    fn iterator_assoc_item_def_id(&self, name: &str) -> Option<&DefId> {
        self.iterator_assoc_items.get(&Symbol::intern(name))
    }

    /// Returns the type for the given place.
    fn place_ty(&self, place: Place<'tcx>) -> Ty<'tcx> {
        place.ty(self.local_decls, self.tcx).ty
    }

    /// Adds a slice length/size bound annotation.
    fn add_slice_len_annotation(
        &mut self,
        annotation_location: Location,
        cond_op: BinOp,
        invariant_place: Place<'tcx>,
        slice_place: Place<'tcx>,
    ) {
        let TyKind::Ref(region, slice_ty, _) = self.place_ty(slice_place).kind() else {
            return;
        };
        if !slice_ty.is_slice() {
            return;
        }
        let slice_len_def_id = self
            .tcx
            .lang_items()
            .get(LangItem::SliceLen)
            .expect("Expected `[T]::len` lang item");
        let slice_len_generics = self.tcx.generics_of(slice_len_def_id);
        let slice_len_host_param_def = slice_len_generics
            .params
            .first()
            .expect("Expected `host` generic param");
        let slice_len_host_param_value = slice_len_host_param_def
            .default_value(self.tcx)
            .expect("Expected `host` generic param default value")
            .skip_binder();
        let gen_ty = slice_ty
            .walk()
            .nth(1)
            .expect("Expected a generic arg for `[T]`");
        let gen_args = self.tcx.mk_args(&[gen_ty, slice_len_host_param_value]);
        self.annotations.push(Annotation::Len(
            annotation_location,
            cond_op,
            invariant_place,
            slice_place,
            *region,
            vec![(
                slice_len_def_id,
                gen_args,
                Ty::new_uint(self.tcx, UintTy::Usize),
            )],
        ));
    }
}

impl<'tcx, 'pass> Visitor<'tcx> for IteratorVisitor<'tcx, 'pass> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.process_terminator(terminator, location);
        self.super_terminator(terminator, location);
    }
}

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
    bb: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
) -> Option<(Place<'tcx>, Region<'tcx>)> {
    let target_place = direct_place(place);
    basic_blocks[bb].statements.iter().find_map(|stmt| {
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
fn deref_place_recursive<'tcx>(
    place: Place<'tcx>,
    bb: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
) -> Option<(Place<'tcx>, Region<'tcx>)> {
    let mut result = None;
    let mut deref_target_place = place;
    while let Some((derefed_place, region)) = deref_place(deref_target_place, bb, basic_blocks) {
        result = Some((derefed_place, region));
        deref_target_place = derefed_place;
    }
    result
}

/// Returns terminator (if any) whose destination is the specified place,
/// and whose basic block is a predecessor of the given anchor block.
fn find_pre_anchor_assign_terminator<'tcx>(
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

    return find_pre_anchor_assign_terminator_inner(
        &mut places,
        anchor_block,
        anchor_block,
        basic_blocks,
        dominators,
        &mut already_visited,
    );

    fn find_pre_anchor_assign_terminator_inner<'tcx>(
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
                let assign = find_pre_anchor_assign_terminator_inner(
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

/// Returns true if the type is a known collection whose length/size maxima is `isize::MAX`.
fn is_isize_bound_collection(ty: Ty, tcx: TyCtxt) -> bool {
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

/// Returns place and basic block (if any) of innermost iterator subject to which
/// no "growing" iterator adapters are applied.
fn find_size_invariant_iterator_subject<'tcx>(
    iterator_arg_place: Place<'tcx>,
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    dominators: &Dominators<BasicBlock>,
    tcx: TyCtxt<'tcx>,
) -> Option<(Place<'tcx>, BasicBlock)> {
    // Finds place and basic block for `std::iter::IntoIterator::into_iter` operand/arg.
    let (terminator, mut iterator_subject_bb) = find_pre_anchor_assign_terminator(
        iterator_arg_place,
        anchor_block,
        anchor_block,
        basic_blocks,
        dominators,
    )?;
    let mut iterator_subject_place = into_iter_operand(&terminator, tcx)
        .or_else(|| iter_by_ref_operand(&terminator, tcx))
        .or_else(|| iterator_adapter_operand(&terminator, tcx))?;

    // Finds place and basic block for the innermost "non-growing" `Iterator` adapter operand/arg (if any).
    track_size_invariant_iterator_transformations(
        &mut iterator_subject_place,
        &mut iterator_subject_bb,
        anchor_block,
        basic_blocks,
        local_decls,
        dominators,
        tcx,
    );

    // Finds place and basic block for a slice `Iterator` or `IntoIter` operand/arg (if any).
    if is_into_iter_ty(iterator_subject_place.ty(local_decls, tcx).ty, tcx) {
        let (into_iter_def_terminator, into_iter_bb) = find_pre_anchor_assign_terminator(
            iterator_subject_place,
            iterator_subject_bb,
            anchor_block,
            basic_blocks,
            dominators,
        )?;
        let collection_place = into_iter_operand(&into_iter_def_terminator, tcx)?;
        iterator_subject_place = collection_place;
        iterator_subject_bb = into_iter_bb;
    } else if is_iter_by_ref_ty(iterator_subject_place.ty(local_decls, tcx).ty, tcx) {
        let (iter_by_ref_terminator, iter_by_ref_bb) = find_pre_anchor_assign_terminator(
            iterator_subject_place,
            iterator_subject_bb,
            anchor_block,
            basic_blocks,
            dominators,
        )?;
        let iter_by_ref_ty_place = iter_by_ref_operand(&iter_by_ref_terminator, tcx)
            .or_else(|| into_iter_operand(&iter_by_ref_terminator, tcx))?;
        iterator_subject_place = iter_by_ref_ty_place;
        iterator_subject_bb = iter_by_ref_bb;
    }

    Some((iterator_subject_place, iterator_subject_bb))
}

// Tracks place and basic block for the innermost "non-growing" `Iterator` adapter operand/arg (if any).
fn track_size_invariant_iterator_transformations<'tcx>(
    iterator_place: &mut Place<'tcx>,
    parent_block: &mut BasicBlock,
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    dominators: &Dominators<BasicBlock>,
    tcx: TyCtxt<'tcx>,
) {
    while is_non_growing_iterator_adapter(iterator_place.ty(local_decls, tcx).ty, tcx) {
        let adapter_def_call = find_pre_anchor_assign_terminator(
            *iterator_place,
            *parent_block,
            anchor_block,
            basic_blocks,
            dominators,
        );
        let Some((adapter_arg_place, adapter_bb)) =
            adapter_def_call.and_then(|(terminator, bb)| {
                iterator_adapter_operand(&terminator, tcx).map(|place| (place, bb))
            })
        else {
            return;
        };
        *iterator_place = adapter_arg_place;
        *parent_block = adapter_bb;
    }
}

/// Returns true if the `Iterator` adapter preserves the `Iterator::count` maxima.
fn is_non_growing_iterator_adapter(ty: Ty, tcx: TyCtxt) -> bool {
    ty.peel_refs().ty_adt_def().is_some_and(|adt_def| {
        let adt_def_id = adt_def.did();
        matches!(
            tcx.item_name(adt_def_id).as_str(),
            "Copied"
                | "Cloned"
                | "Enumerate"
                | "Filter"
                | "FilterMap"
                | "Inspect"
                | "Map"
                | "MapWhile"
                | "Peekable"
                | "Rev"
                | "Skip"
                | "SkipWhile"
                | "Take"
                | "TakeWhile"
        ) && matches!(tcx.crate_name(adt_def_id.krate).as_str(), "core" | "std")
    })
}

/// Returns true if the type is a known `IntoIter` (e.g. `std::vec::IntoIter`).
fn is_into_iter_ty(ty: Ty, tcx: TyCtxt) -> bool {
    ty.peel_refs().ty_adt_def().is_some_and(|adt_def| {
        let adt_def_id = adt_def.did();
        tcx.item_name(adt_def_id).as_str() == "IntoIter"
            && matches!(
                tcx.crate_name(adt_def_id.krate).as_str(),
                "alloc" | "core" | "std"
            )
    })
}

/// Returns true if the type is a known `Iterator` by reference
/// (e.g. `std::slice::Iter`, `std::collections::vec_deque::Iter` e.t.c).
fn is_iter_by_ref_ty(ty: Ty, tcx: TyCtxt) -> bool {
    ty.peel_refs().ty_adt_def().is_some_and(|adt_def| {
        let adt_def_id = adt_def.did();
        matches!(tcx.item_name(adt_def_id).as_str(), "Iter" | "IterMut")
            && matches!(tcx.crate_name(adt_def_id.krate).as_str(), "core" | "std")
    })
}

/// Returns place (if any) for the arg/operand of `std::iter::IntoIterator::into_iter`.
fn into_iter_operand<'tcx>(
    terminator: &Terminator<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<Place<'tcx>> {
    let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
        return None;
    };
    let (def_id, ..) = func.const_fn_def()?;
    let into_iter_def_id = tcx
        .lang_items()
        .get(LangItem::IntoIterIntoIter)
        .expect("Expected `std::iter::IntoIterator::into_iter` lang item");
    if def_id != into_iter_def_id {
        return None;
    }
    match args.first()?.node {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        Operand::Constant(_) => None,
    }
}

/// Returns place (if any) for the arg/operand of an iterator adapter initializer
/// (e.g. `std::iter::Iterator::enumerate`).
fn iterator_adapter_operand<'tcx>(
    terminator: &Terminator<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<Place<'tcx>> {
    let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
        return None;
    };
    let (def_id, ..) = func.const_fn_def()?;
    let is_into_iter_call = matches!(
        tcx.item_name(def_id).as_str(),
        "copied"
            | "cloned"
            | "enumerate"
            | "filter"
            | "filter_map"
            | "inspect"
            | "map"
            | "map_while"
            | "peekable"
            | "rev"
            | "skip"
            | "skip_while"
            | "take"
            | "take_while"
    ) && matches!(tcx.crate_name(def_id.krate).as_str(), "core" | "std")
        && tcx
            .opt_associated_item(def_id)
            .and_then(|assoc_item| assoc_item.trait_container(tcx))
            .is_some_and(|trait_def_id| tcx.item_name(trait_def_id).as_str() == "Iterator");
    if !is_into_iter_call {
        return None;
    }
    match args.first()?.node {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        Operand::Constant(_) => None,
    }
}

/// Returns place (if any) for the arg/operand of a `Iterator` by reference converter method
/// (e.g. `[T]::iter`, `std::vec::Vec::iter` e.t.c).
fn iter_by_ref_operand<'tcx>(
    terminator: &Terminator<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<Place<'tcx>> {
    let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
        return None;
    };
    let (def_id, ..) = func.const_fn_def()?;
    let is_slice_iter_call = tcx.item_name(def_id).as_str() == "iter"
        && matches!(tcx.crate_name(def_id.krate).as_str(), "core" | "std")
        && is_slice_assoc_item(def_id, tcx);
    if !is_slice_iter_call {
        return None;
    }
    match args.first()?.node {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        Operand::Constant(_) => None,
    }
}

/// Returns true if the given `DefId` is an associated item of a slice type `[T]`.
fn is_slice_assoc_item(def_id: DefId, tcx: TyCtxt) -> bool {
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
    match args.first()?.node {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        Operand::Constant(_) => None,
    }
}

/// Returns `DefId` (if known and available) for the length/size call for the given collection type.
fn collection_len_call<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<Vec<(DefId, &'tcx List<GenericArg<'tcx>>, Ty<'tcx>)>> {
    let base_ty = ty.peel_refs();
    let TyKind::Adt(adt_def, gen_args) = base_ty.kind() else {
        return None;
    };
    let adt_def_id = adt_def.did();

    // Finds associated function by name.
    let assoc_fn_def = |name: &str| {
        tcx.inherent_impls(adt_def_id).ok().and_then(|impls_| {
            impls_.iter().find_map(|impl_def_id| {
                tcx.associated_items(impl_def_id)
                    .find_by_name_and_kind(tcx, Ident::from_str(name), AssocKind::Fn, *impl_def_id)
                    .map(|assoc_item| assoc_item.def_id)
            })
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
        let deref_fn_assoc_item = deref_assoc_items.find_by_name_and_kind(
            tcx,
            Ident::from_str("deref"),
            AssocKind::Fn,
            deref_impl,
        )?;
        let deref_target_assoc_item = deref_assoc_items.find_by_name_and_kind(
            tcx,
            Ident::from_str("Target"),
            AssocKind::Type,
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
            .map(|def_id| vec![(def_id, *gen_args, Ty::new_uint(tcx, UintTy::Usize))])
            .or_else(deref_target_assoc_fn),
        _ => None,
    }
}

/// Collects all recurring/loop blocks given an anchor block.
///
/// The anchor block is typically the block with an `std::iter::Iterator::next` terminator.
fn collect_loop_blocks(
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks,
    dominators: &Dominators<BasicBlock>,
) -> FxHashSet<BasicBlock> {
    let mut loop_blocks = FxHashSet::default();
    let mut already_visited = FxHashSet::default();
    collect_loop_blocks_inner(
        anchor_block,
        anchor_block,
        basic_blocks,
        dominators,
        &mut loop_blocks,
        &mut already_visited,
    );
    return loop_blocks;

    fn collect_loop_blocks_inner(
        current_block: BasicBlock,
        anchor_block: BasicBlock,
        basic_blocks: &BasicBlocks,
        dominators: &Dominators<BasicBlock>,
        loop_blocks: &mut FxHashSet<BasicBlock>,
        already_visited: &mut FxHashSet<BasicBlock>,
    ) {
        for pred_bb in &basic_blocks.predecessors()[current_block] {
            if already_visited.contains(pred_bb) {
                continue;
            }
            already_visited.insert(*pred_bb);

            if pred_bb.index() != anchor_block.index()
                && dominators.dominates(anchor_block, *pred_bb)
            {
                loop_blocks.insert(*pred_bb);
                collect_loop_blocks_inner(
                    *pred_bb,
                    anchor_block,
                    basic_blocks,
                    dominators,
                    loop_blocks,
                    already_visited,
                );
            }
        }
    }
}

/// Accumulates all reachable immediate successor blocks,
/// given an anchor block and a list recurring/loop blocks.
///
/// The anchor block is typically the block with an `std::iter::Iterator::next` terminator.
fn collect_reachable_loop_successors(
    anchor_block: BasicBlock,
    loop_blocks: &FxHashSet<BasicBlock>,
    basic_blocks: &BasicBlocks,
) -> FxHashSet<BasicBlock> {
    let mut successors = FxHashSet::default();
    for loop_block in loop_blocks {
        for successor_bb in basic_blocks.successors(*loop_block) {
            if successor_bb.index() != anchor_block.index() && !loop_blocks.contains(&successor_bb)
            {
                let bb_data = &basic_blocks[successor_bb];
                let is_unreachable = bb_data.statements.is_empty()
                    && bb_data
                        .terminator
                        .as_ref()
                        .is_some_and(|terminator| terminator.kind == TerminatorKind::Unreachable);
                if !is_unreachable {
                    successors.insert(successor_bb);
                }
            }
        }
    }
    successors
}

/// Returns places (if any) of the destination and "other" operand for a unit increment assignment
/// (i.e. `x += 1`).
fn unit_incr_assign_places<'tcx>(stmt: &Statement<'tcx>) -> Option<(Place<'tcx>, Place<'tcx>)> {
    let StatementKind::Assign(assign) = &stmt.kind else {
        return None;
    };
    let Rvalue::CheckedBinaryOp(BinOp::Add, operands) = &assign.1 else {
        return None;
    };
    let (const_operand, op_place) = match (&operands.0, &operands.1) {
        (Operand::Constant(const_operand), Operand::Copy(place) | Operand::Move(place))
        | (Operand::Copy(place) | Operand::Move(place), Operand::Constant(const_operand))
            if *const_operand.ty().kind() == TyKind::Uint(UintTy::Usize) =>
        {
            Some((const_operand, place))
        }
        _ => None,
    }?;
    let Const::Val(ConstValue::Scalar(Scalar::Int(scalar)), _) = const_operand.const_ else {
        return None;
    };
    let is_scalar_one = scalar.to_bits(scalar.size()).is_ok_and(|val| val == 1);
    is_scalar_one.then_some((assign.0, *op_place))
}

/// Returns true if place is initialized/assigned to zero before the given anchor block.
fn is_zero_initialized_before_anchor<'tcx>(
    place: Place<'tcx>,
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    dominators: &Dominators<BasicBlock>,
) -> bool {
    let mut already_visited = FxHashSet::default();
    return is_zero_initialized_before_anchor_inner(
        place,
        anchor_block,
        anchor_block,
        basic_blocks,
        dominators,
        &mut already_visited,
    );

    fn is_zero_assignment_to_place<'tcx>(
        place: Place<'tcx>,
        stmt: &Statement<'tcx>,
    ) -> Option<bool> {
        let StatementKind::Assign(assign) = &stmt.kind else {
            return None;
        };
        if place != assign.0 {
            return None;
        }
        let Rvalue::Use(operand) = &assign.1 else {
            return Some(false);
        };
        let Operand::Constant(const_operand) = operand else {
            return Some(false);
        };
        let Const::Val(ConstValue::Scalar(Scalar::Int(scalar)), _) = const_operand.const_ else {
            return Some(false);
        };
        let is_scalar_zero = scalar.to_bits(scalar.size()).is_ok_and(|val| val == 0);
        Some(is_scalar_zero)
    }

    fn is_zero_initialized_before_anchor_inner<'tcx>(
        place: Place<'tcx>,
        current_block: BasicBlock,
        anchor_block: BasicBlock,
        basic_blocks: &BasicBlocks<'tcx>,
        dominators: &Dominators<BasicBlock>,
        already_visited: &mut FxHashSet<BasicBlock>,
    ) -> bool {
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
                    if let Some(res) = is_zero_assignment_to_place(place, stmt) {
                        return res;
                    }
                }
                let res = is_zero_initialized_before_anchor_inner(
                    place,
                    *pred_bb,
                    anchor_block,
                    basic_blocks,
                    dominators,
                    already_visited,
                );
                if res {
                    return true;
                }
            }
        }

        false
    }
}

/// Returns true if place is the index of an `Enumerate::next` call.
fn is_enumerate_index<'tcx>(
    target_place: Place<'tcx>,
    iter_next_dest_place: Place<'tcx>,
    iter_next_arg_place: Place<'tcx>,
    loop_blocks: &FxHashSet<BasicBlock>,
    basic_blocks: &BasicBlocks<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    let iter_next_arg_ty = iter_next_arg_place.ty(local_decls, tcx).ty;
    let Some(adt_def) = iter_next_arg_ty.peel_refs().ty_adt_def() else {
        return false;
    };
    let adt_def_id = adt_def.did();
    if !matches!(tcx.crate_name(adt_def_id.krate).as_str(), "core" | "std")
        || tcx.item_name(adt_def_id).as_str() != "Enumerate"
    {
        return false;
    }

    for bb in loop_blocks {
        for stmt in &basic_blocks[*bb].statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            if assign.0 != target_place {
                continue;
            }
            let Rvalue::Use(Operand::Copy(op_place) | Operand::Move(op_place)) = &assign.1 else {
                continue;
            };
            if op_place.local != iter_next_dest_place.local {
                continue;
            }
            if let Some((
                (_, PlaceElem::Downcast(variant_name, variant_idx)),
                (_, PlaceElem::Field(inner_field_idx, inner_field_ty)),
                (_, PlaceElem::Field(outer_field_idx, outer_field_ty)),
            )) = op_place.iter_projections().collect_tuple()
            {
                let usize_ty = Ty::new_uint(tcx, UintTy::Usize);
                let inner_field_ty_first = match inner_field_ty.kind() {
                    TyKind::Tuple(ty_list) => ty_list.first(),
                    _ => None,
                };
                if (variant_name.is_none()
                    || variant_name.is_some_and(|name| name.as_str() == "Some"))
                    && variant_idx.as_u32() == 1
                    && inner_field_idx.as_u32() == 0
                    && inner_field_ty_first.is_some_and(|ty| *ty == usize_ty)
                    && outer_field_idx.as_u32() == 0
                    && outer_field_ty == usize_ty
                {
                    return true;
                }
            }
        }
    }

    false
}

/// Returns the `VariantIdx` for a `LangItem`.
///
/// # Panics
///
/// Panics if the `LangItem` is not a Variant.
fn variant_idx(lang_item: LangItem, tcx: TyCtxt) -> VariantIdx {
    let variant_def_id = tcx.lang_items().get(lang_item).expect("Expected lang item");
    let adt_def_id = tcx.parent(variant_def_id);
    let adt_def = tcx.adt_def(adt_def_id);
    adt_def.variant_index_with_id(variant_def_id)
}

// Tracks switch target info through "safe" transformations
// (i.e. ones that don't change the target variant's value) between
// `Option::Some`, `Result::Ok` and `ControlFlow::Continue`
// (e.g. via `std::ops::Try::branch` calls, `Option::ok_or`, `Result::ok`, `Result::map_err`
// and `Option::inspect` calls e.t.c).
fn track_safe_result_transformations<'tcx>(
    switch_target_place: &mut Place<'tcx>,
    switch_target_bb: &mut BasicBlock,
    target_bb: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt,
) {
    let mut next_target_bb = Some(target_bb);
    while let Some(target_bb) = next_target_bb {
        let target_bb_data = &basic_blocks[target_bb];
        if let Some((transformer_destination, transformer_target_bb)) =
            safe_result_transform_destination(*switch_target_place, target_bb_data, tcx)
        {
            *switch_target_place = transformer_destination;
            *switch_target_bb = target_bb;
            next_target_bb = transformer_target_bb;
        } else {
            next_target_bb = None;
        }
    }
}

// Tracks switch target info through "safe" transformations
// (i.e. ones that don't change the target variant's value) between
// `Option::Some`, `Result::Ok` and `ControlFlow::Continue`
// (e.g. via `std::ops::Try::branch` calls, `Option::ok_or`, `Result::ok`, `Result::map_err`
// and `Option::inspect` calls e.t.c).
fn track_safe_primary_opt_result_variant_transformations<'tcx>(
    switch_target_place: &mut Place<'tcx>,
    switch_target_bb: &mut BasicBlock,
    switch_target_variant_name: &mut String,
    switch_target_variant_idx: &mut VariantIdx,
    target_bb: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt,
) {
    let mut next_target_bb = Some(target_bb);
    while let Some(target_bb) = next_target_bb {
        let target_bb_data = &basic_blocks[target_bb];
        if let Some((try_branch_destination, try_branch_target_bb)) =
            try_branch_destination(*switch_target_place, target_bb_data, tcx)
        {
            *switch_target_place = try_branch_destination;
            *switch_target_bb = target_bb;
            *switch_target_variant_name = "Continue".to_string();
            *switch_target_variant_idx = variant_idx(LangItem::ControlFlowContinue, tcx);
            next_target_bb = try_branch_target_bb;
        } else if let Some((transformer_destination, transformer_target_bb)) =
            safe_option_some_transform_destination(*switch_target_place, target_bb_data, tcx)
        {
            *switch_target_place = transformer_destination;
            *switch_target_bb = target_bb;
            *switch_target_variant_name = "Some".to_string();
            *switch_target_variant_idx = variant_idx(LangItem::OptionSome, tcx);
            next_target_bb = transformer_target_bb;
        } else if let Some((transformer_destination, transformer_target_bb)) =
            safe_result_ok_transform_destination(*switch_target_place, target_bb_data, tcx)
        {
            *switch_target_place = transformer_destination;
            *switch_target_bb = target_bb;
            *switch_target_variant_name = "Ok".to_string();
            *switch_target_variant_idx = variant_idx(LangItem::ResultOk, tcx);
            next_target_bb = transformer_target_bb;
        } else {
            next_target_bb = None;
        }
    }
}

// Tracks switch target info through "safe" transformations
// (i.e. ones that don't change the target variant's value) from
// `Result::Err` to `Option::Some`, `Result::Ok` and `ControlFlow::Continue`
// (e.g. via `Result::err`, and then optionally through
// `std::ops::Try::branch` calls, `Option::ok_or`, `Result::map_err`
// and `Option::inspect` calls e.t.c).
fn track_safe_result_err_transformations<'tcx>(
    switch_target_place: &mut Place<'tcx>,
    switch_target_bb: &mut BasicBlock,
    switch_target_variant_name: &mut String,
    switch_target_variant_idx: &mut VariantIdx,
    target_bb: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt,
) {
    let mut next_target_bb = Some(target_bb);
    let mut opt_some_target_bb = None;
    fn result_err_crate_adt_and_fn_name_check(
        crate_name: &str,
        adt_name: &str,
        fn_name: &str,
    ) -> bool {
        matches!(crate_name, "std" | "core") && (adt_name == "Result" && fn_name == "err")
    }
    while let Some(target_bb) = next_target_bb {
        let target_bb_data = &basic_blocks[target_bb];
        if let Some((transformer_destination, transformer_target_bb)) = safe_transform_destination(
            *switch_target_place,
            target_bb_data,
            result_err_crate_adt_and_fn_name_check,
            tcx,
        ) {
            *switch_target_place = transformer_destination;
            *switch_target_bb = target_bb;
            *switch_target_variant_name = "Some".to_string();
            *switch_target_variant_idx = variant_idx(LangItem::OptionSome, tcx);
            next_target_bb = None;
            opt_some_target_bb = transformer_target_bb;
        } else if let Some((transformer_destination, transformer_target_bb)) =
            safe_result_err_transform_destination(*switch_target_place, target_bb_data, tcx)
        {
            *switch_target_place = transformer_destination;
            *switch_target_bb = target_bb;
            *switch_target_variant_name = "Err".to_string();
            *switch_target_variant_idx = variant_idx(LangItem::ResultErr, tcx);
            next_target_bb = transformer_target_bb;
        } else {
            next_target_bb = None;
        }
    }

    if let Some(opt_some_target_bb) = opt_some_target_bb {
        track_safe_primary_opt_result_variant_transformations(
            switch_target_place,
            switch_target_bb,
            switch_target_variant_name,
            switch_target_variant_idx,
            opt_some_target_bb,
            basic_blocks,
            tcx,
        );
    }
}

/// Returns the target block for the given basic block's terminator call (if any).
fn call_target(bb_data: &BasicBlockData) -> Option<BasicBlock> {
    let terminator = bb_data.terminator.as_ref()?;
    if let TerminatorKind::Call { target, .. } = &terminator.kind {
        *target
    } else {
        None
    }
}

/// Returns destination place and target block (if any) of an `std::ops::Try::branch` call
/// (i.e. `?` operator) where the given place is the first argument.
fn try_branch_destination<'tcx>(
    place: Place<'tcx>,
    bb_data: &BasicBlockData<'tcx>,
    tcx: TyCtxt,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    let terminator = bb_data.terminator.as_ref()?;
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
    let first_arg_place = args.first().and_then(|arg| match &arg.node {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        Operand::Constant(_) => None,
    })?;
    if *first_arg_place != place {
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
    bb_data: &BasicBlockData<'tcx>,
    tcx: TyCtxt,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    fn crate_adt_and_fn_name_check(crate_name: &str, adt_name: &str, fn_name: &str) -> bool {
        matches!(crate_name, "std" | "core")
            && ((adt_name == "Option"
                && matches!(
                    fn_name,
                    "copied" | "cloned" | "inspect" | "as_ref" | "as_deref"
                ))
                || (adt_name == "Result" && fn_name == "ok"))
    }
    safe_transform_destination(place, bb_data, crate_adt_and_fn_name_check, tcx)
}

/// Returns destination place and target block (if any) of a transformation into `Result`
/// that doesn't change the `Result::Ok` nor `Result::Err` variant values,
/// where the given place is the first argument.
///
/// (e.g. via `Result::inspect`, `Result::inspect_err` calls e.t.c).
fn safe_result_transform_destination<'tcx>(
    place: Place<'tcx>,
    bb_data: &BasicBlockData<'tcx>,
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
    safe_transform_destination(place, bb_data, crate_adt_and_fn_name_check, tcx)
}

/// Returns destination place and target block (if any) of a transformation into `Result`
/// that doesn't change the `Result::Ok` variant value, where the given place is the first argument.
///
/// (e.g. via `Result::map_err`, `Option::ok_or` calls e.t.c).
fn safe_result_ok_transform_destination<'tcx>(
    place: Place<'tcx>,
    bb_data: &BasicBlockData<'tcx>,
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
    safe_transform_destination(place, bb_data, crate_adt_and_fn_name_check, tcx)
}

/// Returns destination place and target block (if any) of a transformation into `Result`
/// that doesn't change the `Result::Err` variant value, where the given place is the first argument.
///
/// (e.g. via `Result::map`, `Result::inspect` calls e.t.c).
fn safe_result_err_transform_destination<'tcx>(
    place: Place<'tcx>,
    bb_data: &BasicBlockData<'tcx>,
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
    safe_transform_destination(place, bb_data, crate_adt_and_fn_name_check, tcx)
}

/// Returns destination place and target block (if any) of a "safe" transformation
/// where the given place is the first argument of the "transformer" call.
///
/// See [`safe_option_transform_destination`] and [`safe_result_transform_destination`] docs
/// for details about the target "safe" transformations.
fn safe_transform_destination<'tcx>(
    place: Place<'tcx>,
    bb_data: &BasicBlockData<'tcx>,
    crate_adt_and_fn_name_check: fn(&str, &str, &str) -> bool,
    tcx: TyCtxt,
) -> Option<(Place<'tcx>, Option<BasicBlock>)> {
    let terminator = bb_data.terminator.as_ref()?;
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
    let first_arg_place = match first_arg.node {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        Operand::Constant(_) => None,
    }?;
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
        crate_adt_and_fn_name_check(crate_name.as_str(), adt_name.as_str(), fn_name.as_str());
    is_safe_transform.then_some((*destination, *target))
}

/// Returns true if the operand is the const identity function (i.e. `std::convert::identity`).
///
/// Ref: <https://doc.rust-lang.org/std/convert/fn.identity.html>
fn is_identity_fn(operand: &Operand, tcx: TyCtxt) -> bool {
    let Some((def_id, ..)) = operand.const_fn_def() else {
        return false;
    };
    let fn_name = tcx.item_name(def_id);
    let crate_name = tcx.crate_name(def_id.krate);
    fn_name.as_str() == "identity" && matches!(crate_name.as_str(), "std" | "core")
}

/// Returns true if the operand is an identity closure (i.e. `|x| x`).
fn is_identity_closure(operand: &Operand, tcx: TyCtxt) -> bool {
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
fn collect_switch_targets_for_discr_value<'tcx>(
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
        for bb in basic_blocks.successors(anchor_block) {
            if already_visited.contains(&bb) {
                continue;
            }
            already_visited.insert(bb);

            // Finds switch target (if any) for the discriminant with the given value.
            if let Some(target_bb) =
                switch_target_for_discr_value(destination, value, &basic_blocks[bb])
            {
                target_blocks.insert(target_bb);
            }

            collect_switch_targets_for_discr_value_inner(
                destination,
                value,
                bb,
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
    bb_data: &BasicBlockData<'tcx>,
) -> Option<BasicBlock> {
    bb_data.statements.iter().find_map(|stmt| {
        let StatementKind::Assign(assign) = &stmt.kind else {
            return None;
        };
        let Rvalue::Discriminant(op_place) = assign.1 else {
            return None;
        };
        if op_place != place {
            return None;
        }

        let terminator = bb_data.terminator.as_ref()?;
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

/// Returns place (if any) for the variant downcast to `usize` of given place.
fn variant_downcast_to_usize_place<'tcx>(
    place: Place<'tcx>,
    variant_name: &str,
    variant_idx: VariantIdx,
    stmt: &Statement<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<Place<'tcx>> {
    let StatementKind::Assign(assign) = &stmt.kind else {
        return None;
    };
    let op_place = match &assign.1 {
        Rvalue::Use(Operand::Copy(op_place) | Operand::Move(op_place))
        | Rvalue::Ref(_, _, op_place) => Some(op_place),
        _ => None,
    }?;
    if op_place.local != place.local {
        return None;
    }
    if let Some((
        (_, PlaceElem::Downcast(op_variant_name, op_variant_idx)),
        (_, PlaceElem::Field(field_idx, field_ty)),
    )) = op_place.iter_projections().collect_tuple()
    {
        if (op_variant_name.is_none()
            || op_variant_name.is_some_and(|name| name.as_str() == variant_name))
            && op_variant_idx == variant_idx
            && field_idx.as_u32() == 0
            && field_ty == Ty::new_uint(tcx, UintTy::Usize)
        {
            return Some(assign.0);
        }
    }

    None
}
