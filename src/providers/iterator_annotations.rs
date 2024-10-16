//! `rustc` `MirPass` for adding annotations for `Iterator` invariants.

use rustc_abi::Size;
use rustc_const_eval::interpret::Scalar;
use rustc_data_structures::graph::{dominators::Dominators, WithSuccessors};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{def::DefKind, LangItem};
use rustc_middle::{
    middle::exported_symbols::ExportedSymbol,
    mir::{
        visit::Visitor, BasicBlock, BasicBlockData, BasicBlocks, BinOp, Body, BorrowKind,
        CallSource, Const, ConstValue, HasLocalDecls, LocalDecl, LocalDecls, Location, MirPass,
        Operand, Place, PlaceElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
        UnwindAction,
    },
    ty::{GenericArg, ImplSubject, List, Region, ScalarInt, Ty, TyCtxt, TyKind, TypeAndMut},
};
use rustc_span::{
    def_id::DefId,
    source_map::{dummy_spanned, Spanned},
    Span, Symbol,
};
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
        // Reverse sorts annotations by location.
        annotations.sort_by(|a, b| b.location().cmp(a.location()));

        // Creates `mirai_assume` annotation handle.
        let mirai_assume_def_id =
            mirai_annotation_fn("mirai_assume", tcx).expect("Expected a fn def for `mirai_assume`");
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
            let location = annotation.location();
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
                    dest_place,
                    collection_place,
                    collection_region,
                    collection_len_def_id,
                    collection_len_gen_args,
                ) => {
                    // Sets collection ref place.
                    let collection_place_ty = collection_place.ty(body.local_decls(), tcx).ty;
                    let collection_ref_place = if collection_place_ty.is_ref() {
                        collection_place
                    } else {
                        // Creates collection ref statement.
                        let collection_ty = collection_place.ty(body.local_decls(), tcx).ty;
                        let collection_ref_ty = Ty::new_ref(
                            tcx,
                            collection_region,
                            TypeAndMut {
                                ty: collection_ty,
                                mutbl: rustc_ast::Mutability::Not,
                            },
                        );
                        let collection_ref_local_decl =
                            LocalDecl::with_source_info(collection_ref_ty, source_info);
                        let collection_ref_local = body.local_decls.push(collection_ref_local_decl);
                        let collection_ref_place = Place::from(collection_ref_local);
                        let collection_ref_rvalue =
                            Rvalue::Ref(collection_region, BorrowKind::Shared, collection_place);
                        let collection_ref_stmt = Statement {
                            source_info,
                            kind: StatementKind::Assign(Box::new((
                                collection_ref_place,
                                collection_ref_rvalue,
                            ))),
                        };
                        predecessors.push(collection_ref_stmt);
                        collection_ref_place
                    };

                    // Creates collection length/size annotation block.
                    let annotation_block_data = BasicBlockData::new(None);
                    let annotation_block = body.basic_blocks_mut().push(annotation_block_data);

                    // Creates collection length/size call.
                    let collection_len_local_decl =
                        LocalDecl::with_source_info(usize_ty, source_info);
                    let collection_len_local = body.local_decls.push(collection_len_local_decl);
                    let collection_len_place = Place::from(collection_len_local);
                    let collection_len_handle = Operand::function_handle(
                        tcx,
                        collection_len_def_id,
                        collection_len_gen_args,
                        Span::default(),
                    );
                    let collection_len_call = Terminator {
                        source_info,
                        kind: TerminatorKind::Call {
                            func: collection_len_handle,
                            args: vec![dummy_spanned(Operand::Move(collection_ref_place))],
                            destination: collection_len_place,
                            target: Some(annotation_block),
                            unwind: UnwindAction::Unreachable,
                            call_source: CallSource::Misc,
                            fn_span: Span::default(),
                        },
                    };

                    // Updates current block statements and terminator.
                    let basic_blocks = body.basic_blocks_mut();
                    basic_blocks[location.block].statements = predecessors;
                    basic_blocks[location.block].terminator = Some(collection_len_call);

                    // Creates collection length/size bound statement.
                    let arg_rvalue = Rvalue::BinaryOp(
                        BinOp::Lt,
                        Box::new((
                            Operand::Copy(dest_place),
                            Operand::Copy(collection_len_place),
                        )),
                    );
                    let arg_stmt = Statement {
                        source_info,
                        kind: StatementKind::Assign(Box::new((arg_place, arg_rvalue))),
                    };

                    // Returns target block and statements.
                    (annotation_block, vec![arg_stmt])
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
        Place<'tcx>,
        Place<'tcx>,
        Region<'tcx>,
        DefId,
        &'tcx List<GenericArg<'tcx>>,
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

    /// Returns the DefId of an `Iterator` assoc item, given it's name.
    fn iterator_assoc_item_def_id(&self, name: &str) -> Option<&DefId> {
        self.iterator_assoc_items.get(&Symbol::intern(name))
    }

    /// Analyses and annotates `Iterator` terminators.
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
                self.process_iterator_position(args, destination, location);
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
        }
    }

    /// Analyzes and annotates calls to `std::iter::Iterator::next`.
    fn process_iterator_next(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        location: Location,
    ) {
        let dominators = self.basic_blocks.dominators();
        let place_ty = |place: Place<'tcx>| place.ty(self.local_decls, self.tcx).ty;

        // Finds place for `std::iter::Iterator::next` operand/arg.
        let iter_next_arg = args.first().expect("Expected an arg for `Iterator::next`");
        let iter_next_arg_place = match &iter_next_arg.node {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => {
                return;
            }
        };

        // Finds place and basic block for `std::iter::IntoIterator::into_iter` operand/arg.
        let iter_next_arg_def_call = find_pre_anchor_terminator_assign(
            *iter_next_arg_place,
            location.block,
            location.block,
            self.basic_blocks,
            dominators,
        );
        let Some((mut iter_target_place, mut iter_target_bb)) =
            iter_next_arg_def_call.clone().and_then(|(terminator, bb)| {
                into_iter_operand(&terminator, self.tcx).map(|place| (place, bb))
            })
        else {
            return;
        };

        // Finds place and basic block for the innermost "non-growing" `Iterator` adapter operand/arg (if any).
        while !is_isize_bound_collection(place_ty(iter_target_place), self.tcx)
            && is_non_growing_iter_adapter(place_ty(iter_target_place), self.tcx)
        {
            let adapter_def_call = find_pre_anchor_terminator_assign(
                iter_target_place,
                iter_target_bb,
                location.block,
                self.basic_blocks,
                dominators,
            );
            let Some((adapter_arg_place, bb)) = adapter_def_call.and_then(|(terminator, bb)| {
                iter_adapter_operand(&terminator, self.tcx).map(|place| (place, bb))
            }) else {
                return;
            };
            iter_target_place = adapter_arg_place;
            iter_target_bb = bb;
        }

        // Finds place and basic block for a slice `Iterator` or `IntoIter` operand/arg (if any).
        let mut iter_target_ty = place_ty(iter_target_place);
        if !is_isize_bound_collection(iter_target_ty, self.tcx) {
            if is_into_iter_ty(iter_target_ty, self.tcx) {
                let into_iter_arg_def_call = find_pre_anchor_terminator_assign(
                    iter_target_place,
                    iter_target_bb,
                    location.block,
                    self.basic_blocks,
                    dominators,
                );
                let Some((collection_place, bb)) =
                    into_iter_arg_def_call.and_then(|(terminator, bb)| {
                        into_iter_operand(&terminator, self.tcx).map(|place| (place, bb))
                    })
                else {
                    return;
                };
                iter_target_place = collection_place;
                iter_target_bb = bb;
            } else if is_slice_iter_ty(iter_target_ty, self.tcx) {
                let slice_iter_arg_def_call = find_pre_anchor_terminator_assign(
                    iter_target_place,
                    iter_target_bb,
                    location.block,
                    self.basic_blocks,
                    dominators,
                );
                let Some((slice_place, slice_bb)) =
                    slice_iter_arg_def_call.and_then(|(terminator, bb)| {
                        slice_iter_operand(&terminator, self.tcx).map(|place| (place, bb))
                    })
                else {
                    return;
                };

                let slice_def_call = find_pre_anchor_terminator_assign(
                    slice_place,
                    slice_bb,
                    location.block,
                    self.basic_blocks,
                    dominators,
                );
                let Some((slice_deref_arg_place, bb)) =
                    slice_def_call.and_then(|(terminator, bb)| {
                        deref_operand(&terminator, self.tcx).map(|place| (place, bb))
                    })
                else {
                    return;
                };
                iter_target_place = slice_deref_arg_place;
                iter_target_bb = bb;
            }
        }

        // Only continues if `Iterator` target either has a length/size with `isize::MAX` maxima,
        // or has a known length/size returning function and is passed by reference.
        iter_target_ty = place_ty(iter_target_place);
        let is_isize_bound = is_isize_bound_collection(iter_target_ty, self.tcx);
        let len_call_info = collection_len_call(iter_target_ty, self.tcx);
        let len_bound_info = len_call_info.and_then(|(len_call_def_id, len_gen_args)| {
            let collection_place_info =
                deref_place_recursive(iter_target_place, iter_target_bb, self.basic_blocks)
                    .or_else(|| {
                        if let TyKind::Ref(region, _, _) = iter_target_ty.kind() {
                            Some((iter_target_place, *region))
                        } else {
                            None
                        }
                    });
            collection_place_info.map(|(collection_place, region)| {
                (collection_place, region, len_call_def_id, len_gen_args)
            })
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
                        *iter_next_arg_place,
                        &loop_blocks,
                        self.basic_blocks,
                        self.local_decls,
                        self.tcx,
                    )
                });
                if let Some((_, op_place)) = inc_invariant_places {
                    // Describes an `isize::MAX` bound annotation.
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
                    if !loop_successors.is_empty() {
                        pre_loop_len_maxima_places.insert(op_place);
                    }
                }
            }
        }

        // Composes collection length/size bound annotations for reachable loop successors (if any).
        if !loop_successors.is_empty() && !pre_loop_len_maxima_places.is_empty() {
            if let Some((collection_place, region, len_call_def_id, len_gen_args)) = len_bound_info
            {
                for bb in loop_successors {
                    for len_maxima_place in &pre_loop_len_maxima_places {
                        // Describes a collection length/size bound annotation.
                        self.annotations.push(Annotation::Len(
                            Location {
                                block: bb,
                                statement_index: 0,
                            },
                            *len_maxima_place,
                            collection_place,
                            region,
                            len_call_def_id,
                            len_gen_args,
                        ));
                    }
                }
            }
        }
    }

    /// Analyzes and annotates calls to collection `len` methods.
    fn process_iterator_position(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        location: Location,
    ) {
        // Finds place for `std::iter::Iterator::position` operand/arg.
        let iter_pos_arg = args
            .first()
            .expect("Expected an arg for `Iterator::position`");
        let iter_pos_arg_place = match &iter_pos_arg.node {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => {
                return;
            }
        };

        // Finds place and basic block for a slice `Iterator` operand/arg (if any).
        // NOTE: We only care about slice `Iterator`s because our length annotation requires
        // the target collection to be passed by reference (not value) so that
        // it's length/size can still be referenced after this iteration.
        let dominators = self.basic_blocks.dominators();
        let slice_iter_arg_def_call = find_pre_anchor_terminator_assign(
            *iter_pos_arg_place,
            location.block,
            location.block,
            self.basic_blocks,
            dominators,
        );
        let Some((slice_place, slice_bb)) = slice_iter_arg_def_call.and_then(|(terminator, bb)| {
            slice_iter_operand(&terminator, self.tcx).map(|place| (place, bb))
        }) else {
            return;
        };
        let slice_def_call = find_pre_anchor_terminator_assign(
            slice_place,
            slice_bb,
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

        // Only continues if `Iterator` target has a known length/size returning function
        // and is passed by reference.
        let Some((len_call_def_id, len_gen_args)) = collection_len_call(
            slice_deref_arg_place.ty(self.local_decls, self.tcx).ty,
            self.tcx,
        ) else {
            return;
        };
        let collection_place_info =
            deref_place_recursive(slice_deref_arg_place, slice_deref_bb, self.basic_blocks)
                .or_else(|| {
                    if let TyKind::Ref(region, _, _) = slice_deref_arg_place
                        .ty(self.local_decls, self.tcx)
                        .ty
                        .kind()
                    {
                        Some((slice_deref_arg_place, *region))
                    } else {
                        None
                    }
                });
        let Some((collection_place, region)) = collection_place_info else {
            return;
        };

        // Finds `Option::Some` target blocks for switches based on the discriminant of
        // return value of `std::iter::Iterator::position` in successor blocks.
        for target_bb in
            collect_some_discr_switch_targets(*destination, location.block, self.basic_blocks)
        {
            for (stmt_idx, stmt) in self.basic_blocks[target_bb].statements.iter().enumerate() {
                // Finds `Option::Some` downcast to `usize` places (if any).
                let Some(some_place) = some_downcast_to_usize_place(*destination, stmt, self.tcx)
                else {
                    continue;
                };

                // Describes a collection length/size bound annotation.
                self.annotations.push(Annotation::Len(
                    Location {
                        block: target_bb,
                        statement_index: stmt_idx + 1,
                    },
                    some_place,
                    collection_place,
                    region,
                    len_call_def_id,
                    len_gen_args,
                ));
            }
        }
    }

    /// Analyzes and annotates calls to `std::iter::Iterator::next`.
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

        // Describes an `isize::MAX` bound annotation.
        self.annotations.push(Annotation::Isize(
            Location {
                block: *target,
                statement_index: 0,
            },
            *destination,
        ));
    }
}

impl<'tcx, 'pass> Visitor<'tcx> for IteratorVisitor<'tcx, 'pass> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.process_terminator(terminator, location);
        self.super_terminator(terminator, location);
    }
}

/// Returns `DefId` (if known) of a mirai annotation function.
fn mirai_annotation_fn(name: &str, tcx: TyCtxt) -> Option<DefId> {
    let annotations_crate = tcx
        .crates(())
        .iter()
        .find(|crate_num| tcx.crate_name(**crate_num).as_str() == "mirai_annotations")
        .expect("Expected `mirai_annotations` crate as a dependency");
    tcx.exported_symbols(*annotations_crate)
        .iter()
        .find_map(|(exported_sym, _)| {
            if let ExportedSymbol::NonGeneric(def_id) = exported_sym {
                if tcx.def_kind(def_id) == DefKind::Fn && tcx.item_name(*def_id).as_str() == name {
                    return Some(*def_id);
                }
            }
            None
        })
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
        Some((direct_place(*op_place), *region))
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
fn find_pre_anchor_terminator_assign<'tcx>(
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

    return find_pre_anchor_terminator_assign_inner(
        &mut places,
        anchor_block,
        anchor_block,
        basic_blocks,
        dominators,
        &mut already_visited,
    );

    fn find_pre_anchor_terminator_assign_inner<'tcx>(
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
                let assign = find_pre_anchor_terminator_assign_inner(
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

/// Returns true if the `Iterator` adapter preserves the `Iterator::count` maxima.
fn is_non_growing_iter_adapter(ty: Ty, tcx: TyCtxt) -> bool {
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

/// Returns true if the type is a known slice `Iterator` (e.g. `std::slice::Iter`).
fn is_slice_iter_ty(ty: Ty, tcx: TyCtxt) -> bool {
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
fn iter_adapter_operand<'tcx>(
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

/// Returns place (if any) for the arg/operand of `[T]::iter`.
fn slice_iter_operand<'tcx>(
    terminator: &Terminator<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<Place<'tcx>> {
    let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
        return None;
    };
    let (def_id, ..) = func.const_fn_def()?;
    let is_slice_iter_call = tcx.item_name(def_id).as_str() == "iter"
        && matches!(tcx.crate_name(def_id.krate).as_str(), "core" | "std")
        && tcx
            .opt_associated_item(def_id)
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
            });
    if !is_slice_iter_call {
        return None;
    }
    match args.first()?.node {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        Operand::Constant(_) => None,
    }
}

/// Returns place (if any) for the arg/operand of `std::ops::Deref` or `std::ops::DerefMut`.
fn deref_operand<'tcx>(terminator: &Terminator<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Place<'tcx>> {
    let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
        return None;
    };
    let (def_id, ..) = func.const_fn_def()?;
    let is_deref_call = matches!(tcx.item_name(def_id).as_str(), "deref" | "deref_mut")
        && matches!(tcx.crate_name(def_id.krate).as_str(), "core" | "std")
        && tcx
            .opt_associated_item(def_id)
            .and_then(|assoc_item| assoc_item.trait_container(tcx))
            .is_some_and(|trait_def_id| {
                matches!(tcx.item_name(trait_def_id).as_str(), "Deref" | "DerefMut")
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
) -> Option<(DefId, &'tcx List<GenericArg<'tcx>>)> {
    match ty.peel_refs().kind() {
        TyKind::Adt(adt_def, gen_args) => {
            let adt_def_id = adt_def.did();
            let assoc_fn_def = |name: &str| {
                tcx.inherent_impls(adt_def_id).ok().and_then(|impls_| {
                    impls_.iter().find_map(|impl_def_id| {
                        tcx.associated_item_def_ids(impl_def_id)
                            .iter()
                            .find(|assoc_item_def_id| {
                                tcx.item_name(**assoc_item_def_id).as_str() == name
                                    && tcx.def_kind(*assoc_item_def_id) == DefKind::AssocFn
                            })
                    })
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
                    .map(|def_id| (*def_id, *gen_args))
                    .filter(|(def_id, _)| tcx.is_mir_available(def_id)),
                _ => None,
            }
        }
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

/// Returns places (if any) of the destination and "other" operand for a unit increment assignment (i.e. `x += 1`).
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

/// Collects target basic blocks (if any) for the `Option::Some` variant of a switch on
/// `Option` discriminant of give place.
fn collect_some_discr_switch_targets<'tcx>(
    place: Place<'tcx>,
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
) -> FxHashSet<BasicBlock> {
    let mut target_blocks = FxHashSet::default();
    let mut already_visited = FxHashSet::default();
    collect_some_discr_switch_targets_inner(
        place,
        anchor_block,
        basic_blocks,
        &mut target_blocks,
        &mut already_visited,
    );
    return target_blocks;
    fn collect_some_discr_switch_targets_inner<'tcx>(
        destination: Place<'tcx>,
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

            // Finds `Option::Some` switch target (if any).
            if let Some(target_bb) = some_discr_switch_target(destination, &basic_blocks[bb]) {
                target_blocks.insert(target_bb);
            }

            collect_some_discr_switch_targets_inner(
                destination,
                bb,
                basic_blocks,
                target_blocks,
                already_visited,
            );
        }
    }
}

/// Returns target basic block (if any) for the `Option::Some` variant of a switch on
/// `Option` discriminant of give place.
fn some_discr_switch_target<'tcx>(
    place: Place<'tcx>,
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

        Some(targets.target_for_value(1))
    })
}

/// Returns place (if any) for the `Option::Some` downcast to `usize` of given place.
fn some_downcast_to_usize_place<'tcx>(
    place: Place,
    stmt: &Statement<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<Place<'tcx>> {
    let StatementKind::Assign(assign) = &stmt.kind else {
        return None;
    };
    let Rvalue::Use(Operand::Copy(op_place) | Operand::Move(op_place)) = &assign.1 else {
        return None;
    };
    if op_place.local != place.local {
        return None;
    }
    if let Some((
        (_, PlaceElem::Downcast(variant_name, variant_idx)),
        (_, PlaceElem::Field(field_idx, field_ty)),
    )) = op_place.iter_projections().collect_tuple()
    {
        if (variant_name.is_none() || variant_name.is_some_and(|name| name.as_str() == "Some"))
            && variant_idx.as_u32() == 1
            && field_idx.as_u32() == 0
            && field_ty == Ty::new_uint(tcx, UintTy::Usize)
        {
            return Some(assign.0);
        }
    }

    None
}
