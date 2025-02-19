//! `rustc` [`MirPass`] for adding annotations for `Iterator` invariants.

use rustc_const_eval::interpret::Scalar;
use rustc_data_structures::graph::{dominators::Dominators, Successors};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::LangItem;
use rustc_middle::{
    mir::{
        visit::Visitor, BasicBlock, BasicBlocks, BinOp, Body, Const, ConstValue, HasLocalDecls,
        LocalDecls, Location, Operand, Place, PlaceElem, Rvalue, Statement, StatementKind,
        Terminator, TerminatorKind, RETURN_PLACE,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::{def_id::DefId, source_map::Spanned, Symbol};
use rustc_type_ir::UintTy;

use itertools::Itertools;

use crate::providers::{
    analyze::{self, SwitchVariant},
    annotate::{self, Annotation, CondOp},
    closure,
    passes::MirPass,
    storage::{
        self, InvariantSource, PropagatedVariant, StorageId, StorageInvariant, StorageInvariantEnv,
    },
};

/// Adds `Iterator` invariant annotations.
pub struct IteratorInvariants;

impl<'tcx> MirPass<'tcx> for IteratorInvariants {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // Generates iterator annotations.
        let def_id = body.source.def_id();
        let mut visitor = IteratorVisitor::new(def_id, &body.basic_blocks, body.local_decls(), tcx);
        visitor.visit_body(body);
        let mut annotations = visitor.annotations;

        // Propagates storage related invariants.
        if !visitor.storage_invariants.is_empty() {
            storage::propagate_invariants(visitor.storage_invariants, &mut annotations, body, tcx);
        }

        // Adds iterator annotations.
        if !annotations.is_empty() {
            annotate::add_annotations(annotations, body, tcx);
        }
    }
}

/// Collects `Iterator` annotations.
struct IteratorVisitor<'tcx, 'pass> {
    def_id: DefId,
    basic_blocks: &'pass BasicBlocks<'tcx>,
    local_decls: &'pass LocalDecls<'tcx>,
    tcx: TyCtxt<'tcx>,
    iterator_assoc_items: FxHashMap<Symbol, DefId>,
    /// A list of annotation declarations.
    annotations: Vec<Annotation<'tcx>>,
    /// A list of FRAME storage related invariants.
    storage_invariants: Vec<StorageInvariant<'tcx>>,
}

impl<'tcx, 'pass> IteratorVisitor<'tcx, 'pass> {
    fn new(
        def_id: DefId,
        basic_blocks: &'pass BasicBlocks<'tcx>,
        local_decls: &'pass LocalDecls<'tcx>,
        tcx: TyCtxt<'tcx>,
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
            def_id,
            basic_blocks,
            local_decls,
            tcx,
            iterator_assoc_items,
            annotations: Vec::new(),
            storage_invariants: Vec::new(),
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

            // Handles propagated return place iterator (r)position invariants.
            let storage_invariant_env = storage::find_invariant_env(def_id, self.tcx)
                .filter(|invariant| invariant.source == InvariantSource::IteratorPosition);
            if let Some(storage_invariant_env) = storage_invariant_env {
                self.propagate_iterator_position_invariant_env(
                    storage_invariant_env,
                    destination,
                    target.as_ref(),
                    location,
                );
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
            size_invariant_iterator_subject(
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

        // Finds place and basic block for slice `Deref` operand/arg (if any).
        if self.place_ty(iterator_subject_place).peel_refs().is_slice() {
            let Some((slice_deref_arg_place, slice_deref_bb)) = analyze::deref_subject(
                iterator_subject_place,
                iterator_subject_bb,
                location.block,
                self.basic_blocks,
                dominators,
                self.tcx,
            ) else {
                return;
            };
            iterator_subject_place = slice_deref_arg_place;
            iterator_subject_bb = slice_deref_bb;
        }

        // Only continues if `Iterator` target either has a length/size with `isize::MAX` maxima,
        // or has a known length/size returning function and is passed by reference.
        let is_isize_bound =
            analyze::is_isize_bound_collection(self.place_ty(iterator_subject_place), self.tcx);
        let len_bound_info = analyze::borrowed_collection_len_call_info(
            iterator_subject_place,
            iterator_subject_bb,
            self.basic_blocks,
            self.local_decls,
            self.tcx,
        );
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
                            CondOp::Lt,
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
                            CondOp::Lt,
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
            .expect("Expected an arg for `Iterator::(r)position`");
        let Some(iter_pos_arg_place) = iter_pos_arg.node.place() else {
            return;
        };

        // Finds place and basic block (if any) of innermost iterator subject to which
        // no "growing" iterator adapters are applied.
        let dominators = self.basic_blocks.dominators();
        let Some((mut iterator_subject_place, mut iterator_subject_bb)) =
            size_invariant_iterator_subject(
                iter_pos_arg_place,
                location.block,
                self.basic_blocks,
                self.local_decls,
                dominators,
                self.tcx,
            )
        else {
            return;
        };

        // Finds place and basic block for slice `Deref` operand/arg (if any).
        if self.place_ty(iterator_subject_place).peel_refs().is_slice() {
            let Some((slice_deref_arg_place, slice_deref_bb)) = analyze::deref_subject(
                iterator_subject_place,
                iterator_subject_bb,
                location.block,
                self.basic_blocks,
                dominators,
                self.tcx,
            ) else {
                return;
            };
            iterator_subject_place = slice_deref_arg_place;
            iterator_subject_bb = slice_deref_bb;
        }

        // Only continues if `Iterator` target has a known length/size returning function
        // and is passed by reference.
        let Some(len_call_info) =
            analyze::collection_len_call(self.place_ty(iterator_subject_place), self.tcx)
        else {
            return;
        };
        let collection_place_info = analyze::deref_place_recursive(
            iterator_subject_place,
            iterator_subject_bb,
            self.basic_blocks,
        )
        .or_else(|| {
            if let TyKind::Ref(region, _, _) = self.place_ty(iterator_subject_place).kind() {
                Some((iterator_subject_place, *region))
            } else {
                None
            }
        });
        let Some((collection_place, region)) = collection_place_info else {
            return;
        };

        // Finds FRAME storage subject (if any).
        let storage_info = storage::storage_subject(
            iterator_subject_place,
            iterator_subject_bb,
            location.block,
            self.basic_blocks,
            dominators,
            self.tcx,
        );

        // Tracks `Option::Some` switch target info of return value of
        // `std::iter::Iterator::position` or `std::iter::Iterator::rposition`.
        // Also tracks variant "safe" transformations (e.g. `ControlFlow::Continue` and
        // `Result::Ok` transformations - see [`track_switch_target_transformations`] for details).
        let mut switch_target_place = *destination;
        let mut switch_target_block = location.block;
        let mut switch_variant = SwitchVariant::OptionSome;
        if let Some(target) = target {
            analyze::track_safe_primary_opt_result_variant_transformations(
                &mut switch_target_place,
                &mut switch_target_block,
                &mut switch_variant,
                *target,
                self.basic_blocks,
                self.tcx,
                false,
            );
        }

        // Finds `Option::Some` (or equivalent safe transformation) target blocks
        // for switches based on the discriminant of return value of
        // `std::iter::Iterator::position` or `std::iter::Iterator::rposition` in successor blocks.
        let switch_targets = analyze::collect_switch_targets_for_discr_value(
            switch_target_place,
            switch_variant.idx(self.tcx).as_u32() as u128,
            switch_target_block,
            self.basic_blocks,
        );

        // Collects collection length/size bound annotations (and storage invariants)
        // for variant downcast to `usize` places (if any) for the switch target.
        let mut storage_invariants = FxHashSet::default();
        for target_bb in switch_targets {
            for (stmt_idx, stmt) in self.basic_blocks[target_bb].statements.iter().enumerate() {
                // Finds variant downcast to `usize` places (if any) for the switch target variant.
                let Some(downcast_place) = analyze::variant_downcast_to_ty_place(
                    switch_target_place,
                    switch_variant.name(),
                    switch_variant.idx(self.tcx),
                    self.tcx.types.usize,
                    stmt,
                ) else {
                    continue;
                };

                // Declares a collection length/size bound annotation.
                let annotation_location = Location {
                    block: target_bb,
                    statement_index: stmt_idx + 1,
                };
                let cond_op = CondOp::Lt;
                self.annotations.push(Annotation::Len(
                    annotation_location,
                    cond_op,
                    downcast_place,
                    collection_place,
                    region,
                    len_call_info.clone(),
                ));

                // Tracks invariants that need to propagated to other storage uses.
                if storage_info.is_some() {
                    storage_invariants.insert((annotation_location, cond_op, downcast_place));
                }
            }
        }

        // Adds storage invariants.
        if !storage_invariants.is_empty() {
            if let Some((storage_item, use_location)) = storage_info {
                self.storage_invariants.push((
                    StorageId::DefId(storage_item.prefix),
                    use_location,
                    storage_invariants,
                ));
            }
        }

        // Propagate position invariant to `Option` (and `Result`) adapter input closures (if any).
        if let Some(next_target) = analyze::call_target(&self.basic_blocks[switch_target_block]) {
            // Collects collection related places (including all deref subjects).
            let mut collection_def_places = vec![(iterator_subject_place, iterator_subject_bb)];
            let deref_subjects = analyze::deref_subjects_recursive(
                iterator_subject_place,
                iterator_subject_bb,
                location.block,
                self.basic_blocks,
                dominators,
                self.tcx,
            );
            if !deref_subjects.is_empty() {
                collection_def_places.extend(deref_subjects);
            }

            // Propagate invariants to closure (if any).
            let next_block_data = &self.basic_blocks[next_target];
            closure::propagate_opt_result_idx_invariant(
                switch_target_place,
                next_block_data,
                &[(iterator_subject_place, iterator_subject_bb)],
                self.basic_blocks,
                self.tcx,
            );
        };

        // Propagate return place storage index invariant to callers.
        let is_primary_variant_return_place = switch_target_place
            .as_local()
            .is_some_and(|local| local == RETURN_PLACE);
        if is_primary_variant_return_place {
            if let Some((storage_item, _)) = storage_info {
                // Composes propagated return place storage invariant environment.
                let storage_invariant_env = StorageInvariantEnv::new_with_id(
                    self.def_id,
                    StorageId::DefId(storage_item.prefix),
                    InvariantSource::IteratorPosition,
                    PropagatedVariant::Primary(switch_variant),
                    self.tcx,
                );

                // Sets propagated return place storage invariant environment.
                storage::set_invariant_env(&storage_invariant_env);
            }
        }
    }

    /// Analyzes and annotates calls to `std::iter::Iterator::count`.
    fn process_iterator_count(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: Option<&BasicBlock>,
        location: Location,
    ) {
        // Finds place for `std::iter::Iterator::count` operand/arg.
        let iterator_count_arg = args.first().expect("Expected an arg for `Iterator::count`");
        let Some(iterator_count_arg_place) = iterator_count_arg.node.place() else {
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
            size_invariant_iterator_subject(
                iterator_count_arg_place,
                location.block,
                self.basic_blocks,
                self.local_decls,
                dominators,
                self.tcx,
            )
        else {
            return;
        };

        // Length invariant annotations are added at the beginning of the next block.
        let annotation_location = Location {
            block: *target,
            statement_index: 0,
        };
        let cond_op = CondOp::Le;

        // Finds place and basic block for a slice `Iterator` operand/arg (if any).
        if self.place_ty(iterator_subject_place).peel_refs().is_slice() {
            // Declares a slice length/size bound annotation.
            if let Some(annotation) = annotate::compose_slice_len_annotation(
                annotation_location,
                cond_op,
                *destination,
                iterator_subject_place,
                self.local_decls,
                self.tcx,
            ) {
                self.annotations.push(annotation);
            }

            // Finds place and basic block for slice `Deref` operand/arg (if any).
            let Some((slice_deref_arg_place, slice_deref_bb)) = analyze::deref_subject(
                iterator_subject_place,
                iterator_subject_bb,
                location.block,
                self.basic_blocks,
                dominators,
                self.tcx,
            ) else {
                return;
            };
            iterator_subject_place = slice_deref_arg_place;
            iterator_subject_bb = slice_deref_bb;
        }

        // Declares an `isize::MAX` bound annotation (if appropriate).
        let iterator_subject_ty = self.place_ty(iterator_subject_place);
        if analyze::is_isize_bound_collection(self.place_ty(iterator_subject_place), self.tcx) {
            self.annotations.push(Annotation::Isize(
                annotation_location,
                cond_op,
                *destination,
            ));
        }

        // Declares a collection length/size bound annotation (if appropriate).
        let len_call_info = analyze::collection_len_call(iterator_subject_ty, self.tcx);
        if let Some(len_call_info) = len_call_info {
            let collection_place_info = analyze::deref_place_recursive(
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
                    annotation_location,
                    cond_op,
                    *destination,
                    collection_place,
                    region,
                    len_call_info.clone(),
                ));

                // Finds FRAME storage subject (if any).
                let storage_info = storage::storage_subject(
                    iterator_subject_place,
                    iterator_subject_bb,
                    location.block,
                    self.basic_blocks,
                    dominators,
                    self.tcx,
                );

                // Adds storage invariants.
                if let Some((storage_item, use_location)) = storage_info {
                    self.storage_invariants.push((
                        StorageId::DefId(storage_item.prefix),
                        use_location,
                        FxHashSet::from_iter([(annotation_location, cond_op, *destination)]),
                    ));
                }
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
        if !analyze::is_isize_bound_collection(len_arg_ty, self.tcx) {
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
            CondOp::Le,
            *destination,
        ));
    }

    // Propagates return place iterator (r)position invariants.
    fn propagate_iterator_position_invariant_env(
        &mut self,
        invariant_env: StorageInvariantEnv,
        destination: &Place<'tcx>,
        target: Option<&BasicBlock>,
        location: Location,
    ) {
        // Tracks `Option::Some` (or "safe" transformation) switch target info of return value of
        // `std::iter::Iterator::position` or `std::iter::Iterator::rposition`.
        // Also tracks variant "safe" transformations (e.g. `ControlFlow::Continue` and
        // `Result::Ok` transformations - see [`track_switch_target_transformations`] for details).
        let mut switch_target_place = *destination;
        let mut switch_target_block = location.block;
        let Some(mut switch_variant) = invariant_env.propagated_variant.as_switch_variant() else {
            return;
        };
        if let Some(target) = target {
            analyze::track_safe_primary_opt_result_variant_transformations(
                &mut switch_target_place,
                &mut switch_target_block,
                &mut switch_variant,
                *target,
                self.basic_blocks,
                self.tcx,
                false,
            );
        }

        // Finds `Option::Some` (or equivalent safe transformation) target blocks
        // for switches based on the discriminant of return value of
        // `std::iter::Iterator::position` or `std::iter::Iterator::rposition` in successor blocks.
        let switch_targets = analyze::collect_switch_targets_for_discr_value(
            switch_target_place,
            switch_variant.idx(self.tcx).as_u32() as u128,
            switch_target_block,
            self.basic_blocks,
        );

        // Collects collection length/size bound annotations (and storage invariants)
        // for variant downcast to `usize` places (if any) for the switch target.
        let mut storage_invariants = FxHashSet::default();
        for target_bb in switch_targets {
            for (stmt_idx, stmt) in self.basic_blocks[target_bb].statements.iter().enumerate() {
                // Finds variant downcast to `usize` places (if any) for the switch target variant.
                let Some(downcast_place) = analyze::variant_downcast_to_ty_place(
                    switch_target_place,
                    switch_variant.name(),
                    switch_variant.idx(self.tcx),
                    self.tcx.types.usize,
                    stmt,
                ) else {
                    continue;
                };

                // Declares transformed storage invariants.
                storage_invariants.insert((
                    Location {
                        block: target_bb,
                        statement_index: stmt_idx + 1,
                    },
                    CondOp::Lt,
                    downcast_place,
                ));
            }
        }

        // Adds storage invariants.
        if !storage_invariants.is_empty() {
            self.storage_invariants.push((
                StorageId::DefHash(invariant_env.storage_def_hash.clone()),
                location.block,
                storage_invariants,
            ));
        }

        // Propagate return place storage index invariant to callers.
        let is_primary_variant_return_place = switch_target_place
            .as_local()
            .is_some_and(|local| local == RETURN_PLACE);
        if is_primary_variant_return_place {
            // Composes propagated return place storage invariant environment.
            let next_invariant_env = StorageInvariantEnv::new(
                self.def_id,
                invariant_env.storage_def_hash,
                InvariantSource::IteratorPosition,
                PropagatedVariant::Primary(switch_variant),
                self.tcx,
            );

            // Sets propagated return place storage invariant environment.
            storage::set_invariant_env(&next_invariant_env);
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
}

impl<'tcx> Visitor<'tcx> for IteratorVisitor<'tcx, '_> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.process_terminator(terminator, location);
        self.super_terminator(terminator, location);
    }
}

/// Returns place and basic block (if any) of innermost iterator subject to which
/// no "growing" iterator adapters are applied.
fn size_invariant_iterator_subject<'tcx>(
    iterator_arg_place: Place<'tcx>,
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    dominators: &Dominators<BasicBlock>,
    tcx: TyCtxt<'tcx>,
) -> Option<(Place<'tcx>, BasicBlock)> {
    // Finds place and basic block for outermost `Iterator` transformation operand/arg (if any).
    let (terminator, mut iterator_subject_bb) = analyze::pre_anchor_assign_terminator(
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

    // Finds place and basic block for innermost `Iterator` transformation operand/arg (if any).
    if is_into_iter_ty(iterator_subject_place.ty(local_decls, tcx).ty, tcx) {
        let (into_iter_def_terminator, into_iter_bb) = analyze::pre_anchor_assign_terminator(
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
        let (iter_by_ref_terminator, iter_by_ref_bb) = analyze::pre_anchor_assign_terminator(
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
    while is_size_invariant_iterator_adapter(iterator_place.ty(local_decls, tcx).ty, tcx) {
        let adapter_def_call = analyze::pre_anchor_assign_terminator(
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
fn is_size_invariant_iterator_adapter(ty: Ty, tcx: TyCtxt) -> bool {
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
    args.first()?.node.place()
}

/// Returns place (if any) for the arg/operand of a `Iterator` by reference conversion
/// (i.e. via `[T]::iter`).
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
        && analyze::is_slice_assoc_item(def_id, tcx);
    if !is_slice_iter_call {
        return None;
    }
    args.first()?.node.place()
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
    let is_adapter_call = matches!(
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
    if !is_adapter_call {
        return None;
    }
    args.first()?.node.place()
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
    // TODO: is `BinOp::Add` necessary?.
    let Rvalue::BinaryOp(BinOp::Add | BinOp::AddWithOverflow, operands) = &assign.1 else {
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
    let is_scalar_one = scalar.try_to_bits(scalar.size()).is_ok_and(|val| val == 1);
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
        let is_scalar_zero = scalar.try_to_bits(scalar.size()).is_ok_and(|val| val == 0);
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
                let inner_field_ty_first = match inner_field_ty.kind() {
                    TyKind::Tuple(ty_list) => ty_list.first(),
                    _ => None,
                };
                if (variant_name.is_none()
                    || variant_name.is_some_and(|name| name.as_str() == "Some"))
                    && variant_idx.as_u32() == 1
                    && inner_field_idx.as_u32() == 0
                    && inner_field_ty_first.is_some_and(|ty| *ty == tcx.types.usize)
                    && outer_field_idx.as_u32() == 0
                    && outer_field_ty == tcx.types.usize
                {
                    return true;
                }
            }
        }
    }

    false
}
