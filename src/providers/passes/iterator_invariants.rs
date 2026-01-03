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
    ty::{GenericArgsRef, Ty, TyCtxt, TyKind},
};
use rustc_span::{def_id::DefId, source_map::Spanned, Symbol};
use rustc_type_ir::UintTy;

use std::ops::Deref;

use itertools::Itertools;

use crate::{
    providers::{
        analyze::{self, SwitchVariant},
        annotate::{self, Annotation, CondOp},
        closure,
        passes::MirPass,
        storage::{
            self, InvariantSource, PropagatedVariant, StorageId, StorageInvariant,
            StorageInvariantEnv,
        },
        summaries,
    },
    utils,
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
            .filter_map(|assoc_item| assoc_item.opt_name().map(|name| (name, assoc_item.def_id)))
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
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } = &terminator.kind
        else {
            return;
        };

        // Retrieves `fn` definition (if any).
        let Some((def_id, gen_args)) = func.const_fn_def() else {
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
            self.process_iterator_count(
                def_id,
                args,
                destination,
                target.as_ref(),
                location,
                gen_args,
            );
        }

        // Handles calls to collection `len` methods.
        if self
            .tcx
            .opt_item_name(def_id)
            .is_some_and(|name| name.as_str() == "len")
            && args.len() == 1
        {
            self.process_len(args, destination, target.as_ref());
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

    /// Analyzes and annotates calls to `std::iter::Iterator::next`.
    fn process_iterator_next(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        location: Location,
    ) {
        // Finds place for `Iterator::next` operand/arg.
        let iterator_next_arg = args.first().expect("Expected an arg for `Iterator::next`");
        let Some(iterator_next_arg_place) = iterator_next_arg.node.place() else {
            return;
        };

        // Finds places and basic blocks (if any) of innermost iterator subjects by chain (if any)
        // to which no "growing" iterator adapters are applied.
        let dominators = self.basic_blocks.dominators();
        let (iterator_subjects, n_empty_subjects) = size_invariant_iterator_subjects_by_chain(
            iterator_next_arg_place,
            location.block,
            self.basic_blocks,
            self.local_decls,
            dominators,
            self.tcx,
        );
        if iterator_subjects.is_empty() {
            return;
        }

        // Determines bounds for collection length/size and index increment operations (if possible).
        let mut upper_bound = UpperBound::new_usize();
        let mut len_bound_info = None;
        let n_non_empty_chains = iterator_subjects.len() - n_empty_subjects;
        for (iterator_subject, mut iterator_subject_block) in iterator_subjects {
            // Unwraps the subject place (if any),
            // or sets the upper bound to zero if subject is `std::iter::Empty`.
            let mut iterator_subject_place = match iterator_subject {
                IterSubject::Place(place) => place,
                IterSubject::Empty => {
                    upper_bound.zero();
                    continue;
                }
            };

            // Finds place and basic block for slice `Deref` operand/arg (if any).
            if self.place_ty(iterator_subject_place).peel_refs().is_slice() {
                let Some((slice_deref_arg_place, slice_deref_bb)) = analyze::deref_subject(
                    iterator_subject_place,
                    iterator_subject_block,
                    location.block,
                    self.basic_blocks,
                    dominators,
                    self.tcx,
                ) else {
                    return;
                };
                iterator_subject_place = slice_deref_arg_place;
                iterator_subject_block = slice_deref_bb;
            }

            // Updates upper bound (if appropriate).
            let iterator_subject_ty = self.place_ty(iterator_subject_place);
            if analyze::is_isize_bound_collection(iterator_subject_ty, self.tcx) {
                upper_bound.increase(utils::target_isize_max());
            } else if is_iter_once_ty(iterator_subject_ty, self.tcx) {
                upper_bound.increase(1);
            } else {
                // NOTE: Any further upper bound updates will be ignored after this.
                upper_bound.invalidate();
            }

            // Updates collection length/size method info (if appropriate).
            if n_non_empty_chains == 1 {
                len_bound_info = analyze::borrowed_collection_len_call_info(
                    iterator_subject_place,
                    iterator_subject_block,
                    self.basic_blocks,
                    self.local_decls,
                    self.tcx,
                );
            }
        }

        // Only continues if iterator subject either has a length/size known upper bound
        // (e.g. `isize::MAX`), or has a known length/size returning method, and is passed by reference.
        if upper_bound.is_none() && len_bound_info.is_none() {
            return;
        }

        // Collects all recurring/loop blocks and reachable immediate loop successor blocks (if any),
        // using the block containing the `Iterator::next` call as the anchor block.
        let loop_blocks = collect_loop_blocks(location.block, self.basic_blocks, dominators);
        if loop_blocks.is_empty() {
            return;
        }
        let loop_successors =
            collect_reachable_loop_successors(location.block, &loop_blocks, self.basic_blocks);

        // Composes annotations for loop invariants based on collection length/size bounds,
        // and index increment operations.
        let mut pre_loop_len_maxima_places = FxHashSet::default();
        for block in &loop_blocks {
            let block_data = &self.basic_blocks[*block];
            for (stmt_idx, stmt) in block_data.statements.iter().enumerate() {
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
                    // Declares an upper bound annotation.
                    if let Some(upper_bound) = upper_bound.value() {
                        self.annotations.push(Annotation::new_const_max(
                            Location {
                                block: *block,
                                statement_index: stmt_idx,
                            },
                            CondOp::Lt,
                            op_place,
                            upper_bound,
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
                for block in &loop_successors {
                    for len_maxima_place in &pre_loop_len_maxima_places {
                        // Declares a collection length/size bound annotation.
                        self.annotations.push(Annotation::Len(
                            Location {
                                block: *block,
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

        // Finds places and basic blocks (if any) of innermost iterator subjects by chain (if any)
        // to which no "growing" iterator adapters are applied.
        let dominators = self.basic_blocks.dominators();
        let (iterator_subjects, n_empty_subjects) = size_invariant_iterator_subjects_by_chain(
            iter_pos_arg_place,
            location.block,
            self.basic_blocks,
            self.local_decls,
            dominators,
            self.tcx,
        );
        if iterator_subjects.is_empty() {
            return;
        }

        // Determines bounds for collection length/size and index increment operations (if possible).
        let mut upper_bound = UpperBound::new_usize();
        let mut len_bound_info = None;
        let mut solo_iterator_subject_info = None;
        let n_non_empty_chains = iterator_subjects.len() - n_empty_subjects;
        for (iterator_subject, mut iterator_subject_block) in iterator_subjects {
            // Unwraps the subject place (if any),
            // or sets the upper bound to zero if subject is `std::iter::Empty`.
            let mut iterator_subject_place = match iterator_subject {
                IterSubject::Place(place) => place,
                IterSubject::Empty => {
                    upper_bound.zero();
                    continue;
                }
            };

            // Finds place and basic block for slice `Deref` operand/arg (if any).
            if self.place_ty(iterator_subject_place).peel_refs().is_slice() {
                let Some((slice_deref_arg_place, slice_deref_block)) = analyze::deref_subject(
                    iterator_subject_place,
                    iterator_subject_block,
                    location.block,
                    self.basic_blocks,
                    dominators,
                    self.tcx,
                ) else {
                    return;
                };
                iterator_subject_place = slice_deref_arg_place;
                iterator_subject_block = slice_deref_block;
            }

            // Updates upper bound (if appropriate).
            let iterator_subject_ty = self.place_ty(iterator_subject_place);
            if analyze::is_isize_bound_collection(iterator_subject_ty, self.tcx) {
                upper_bound.increase(utils::target_isize_max());
            } else if is_iter_once_ty(iterator_subject_ty, self.tcx) {
                upper_bound.increase(1);
            } else {
                // NOTE: Any further upper bound updates will be ignored after this.
                upper_bound.invalidate();
            }

            // Updates collection length/size method info and tracks solo iterator subject (if appropriate).
            if n_non_empty_chains == 1 {
                len_bound_info = analyze::collection_len_call(iterator_subject_ty, self.tcx);
                solo_iterator_subject_info = Some((iterator_subject_place, iterator_subject_block));
            }
        }

        // Only continues if iterator subject either has a length/size known upper bound
        // (e.g. `isize::MAX`), or has a known length/size returning method, and is passed by reference.
        if upper_bound.is_none() && len_bound_info.is_none() {
            return;
        }

        // Finds collection place info (if any).
        let collection_place_info = solo_iterator_subject_info.and_then(
            |(iterator_subject_place, iterator_subject_block)| {
                analyze::deref_place_recursive(
                    iterator_subject_place,
                    iterator_subject_block,
                    self.basic_blocks,
                )
                .or_else(|| {
                    if let TyKind::Ref(region, _, _) = self.place_ty(iterator_subject_place).kind()
                    {
                        Some((iterator_subject_place, *region))
                    } else {
                        None
                    }
                })
            },
        );

        // Finds FRAME storage subject (if any).
        let storage_info = solo_iterator_subject_info.and_then(
            |(iterator_subject_place, iterator_subject_block)| {
                storage::storage_subject(
                    iterator_subject_place,
                    iterator_subject_block,
                    location.block,
                    self.basic_blocks,
                    dominators,
                    self.tcx,
                )
            },
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

                // Declares an upper bound annotation, if one was determined.
                let annotation_location = Location {
                    block: target_bb,
                    statement_index: stmt_idx + 1,
                };
                let cond_op = CondOp::Lt;
                if let Some(upper_bound) = upper_bound.value() {
                    self.annotations.push(Annotation::new_const_max(
                        annotation_location,
                        cond_op,
                        downcast_place,
                        upper_bound,
                    ));
                }

                // Declares a collection length/size bound annotation (if appropriate).
                if let Some(((collection_place, region), len_call_info)) =
                    collection_place_info.zip(len_bound_info.clone())
                {
                    self.annotations.push(Annotation::Len(
                        annotation_location,
                        cond_op,
                        downcast_place,
                        collection_place,
                        region,
                        len_call_info,
                    ));

                    // Tracks invariants that need to propagated to other storage uses.
                    if storage_info.is_some() {
                        storage_invariants.insert((annotation_location, cond_op, downcast_place));
                    }
                }
            }
        }

        // Only continues if iterator subject has a known length/size returning method, and is passed by reference.
        if len_bound_info.is_none() {
            return;
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
        if let Some(((iterator_subject_place, iterator_subject_block), next_target)) =
            solo_iterator_subject_info.zip(analyze::call_target(
                &self.basic_blocks[switch_target_block],
            ))
        {
            // Collects collection related places (including all deref subjects).
            let mut collection_def_places = vec![(iterator_subject_place, iterator_subject_block)];
            let deref_subjects = analyze::deref_subjects_recursive(
                iterator_subject_place,
                iterator_subject_block,
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
                &[(iterator_subject_place, iterator_subject_block)],
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
        def_id: DefId,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: Option<&BasicBlock>,
        location: Location,
        gen_args: GenericArgsRef<'tcx>,
    ) {
        // Finds place for `Iterator::count` operand/arg.
        let iterator_count_arg = args.first().expect("Expected an arg for `Iterator::count`");
        let Some(iterator_count_arg_place) = iterator_count_arg.node.place() else {
            return;
        };

        // Only continues if the terminator has a target basic block.
        let Some(target) = target else {
            return;
        };

        // Finds places and basic blocks (if any) of innermost iterator subjects by chain (if any)
        // to which no "growing" iterator adapters are applied.
        let dominators = self.basic_blocks.dominators();
        let (iterator_subjects, n_empty_subjects) = size_invariant_iterator_subjects_by_chain(
            iterator_count_arg_place,
            location.block,
            self.basic_blocks,
            self.local_decls,
            dominators,
            self.tcx,
        );
        if iterator_subjects.is_empty() {
            return;
        }

        // Determines max bound annotations for `Iterator::count` return place
        // (i.e. the terminator destination).
        let annotation_location = Location {
            block: *target,
            statement_index: 0,
        };
        let cond_op = CondOp::Le;
        let mut upper_bound = UpperBound::new_usize();
        let n_non_empty_chains = iterator_subjects.len() - n_empty_subjects;
        for (iterator_subject, mut iterator_subject_block) in iterator_subjects {
            // Unwraps the subject place (if any),
            // or sets the upper bound to zero if subject is `std::iter::Empty`.
            let mut iterator_subject_place = match iterator_subject {
                IterSubject::Place(place) => place,
                IterSubject::Empty => {
                    upper_bound.zero();
                    continue;
                }
            };

            // Finds place and basic block for a slice `Iterator` operand/arg (if any).
            if self.place_ty(iterator_subject_place).peel_refs().is_slice() {
                // Declares a slice length/size bound annotation.
                if n_non_empty_chains == 1 {
                    if let Some((region, call_info)) = analyze::slice_len_call_info(
                        iterator_subject_place,
                        self.local_decls,
                        self.tcx,
                    ) {
                        self.annotations.push(Annotation::Len(
                            annotation_location,
                            cond_op,
                            *destination,
                            iterator_subject_place,
                            region,
                            call_info,
                        ));
                    }
                }

                // Finds place and basic block for slice `Deref` operand/arg (if any).
                let Some((slice_deref_arg_place, slice_deref_bb)) = analyze::deref_subject(
                    iterator_subject_place,
                    iterator_subject_block,
                    location.block,
                    self.basic_blocks,
                    dominators,
                    self.tcx,
                ) else {
                    return;
                };
                iterator_subject_place = slice_deref_arg_place;
                iterator_subject_block = slice_deref_bb;
            }

            // Updates upper bound (if appropriate).
            let iterator_subject_ty = self.place_ty(iterator_subject_place);
            if analyze::is_isize_bound_collection(iterator_subject_ty, self.tcx) {
                upper_bound.increase(utils::target_isize_max());
            } else if is_iter_once_ty(iterator_subject_ty, self.tcx) {
                upper_bound.increase(1);
            } else {
                // NOTE: Any further upper bound updates will be ignored after this.
                upper_bound.invalidate();
            }

            // Declares a collection length/size bound annotation (if appropriate).
            if n_non_empty_chains != 1 {
                continue;
            }
            let len_call_info = analyze::collection_len_call(iterator_subject_ty, self.tcx);
            if let Some(len_call_info) = len_call_info {
                let collection_place_info = analyze::deref_place_recursive(
                    iterator_subject_place,
                    iterator_subject_block,
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
                        iterator_subject_block,
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

        // Declares an upper bound annotation, if one was determined.
        if let Some(upper_bound) = upper_bound.value() {
            self.annotations.push(Annotation::new_const_max(
                annotation_location,
                cond_op,
                *destination,
                upper_bound,
            ));

            // Adds specialized summary for `Iterator::count` subject.
            summaries::add_summary_target(self.def_id, def_id, gen_args, self.tcx);
        }
    }

    /// Analyzes and annotates calls to collection `len` methods.
    fn process_len(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: Option<&BasicBlock>,
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
        self.annotations.push(Annotation::new_isize_max(
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
        // `std::iter::Iterator::(r)position` in successor blocks.
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

/// Returns places and basic blocks (if any) of innermost iterator subjects
/// per iterator chain (if any) to which no "growing" iterator adapters are applied.
///
/// **NOTE:** Also returns the number of empty subjects.
///
/// **NOTE:** This is similar to [`size_invariant_iterator_subject`] but applied to each chain.
fn size_invariant_iterator_subjects_by_chain<'tcx>(
    iterator_arg_place: Place<'tcx>,
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    dominators: &Dominators<BasicBlock>,
    tcx: TyCtxt<'tcx>,
) -> (FxHashSet<(IterSubject<'tcx>, BasicBlock)>, usize) {
    // Tracks final results.
    let mut results = FxHashSet::default();
    let mut n_empty_subjects = 0;

    // Tracks intermediate results for which the innermost iterator subject still needs to be processed
    // by unwrapping "non-growing" iterator adapters.
    let mut intermediate_subject_places = FxHashSet::default();

    // Handles chains (if any).
    if let Some((first_arg_place, second_arg_place, chain_block)) = iter_chain_subjects(
        iterator_arg_place,
        anchor_block,
        basic_blocks,
        local_decls,
        dominators,
        tcx,
    ) {
        for iter_subject in [first_arg_place, second_arg_place] {
            match iter_subject {
                IterSubject::Place(arg_place) => {
                    if is_iter_chain_ty(arg_place.ty(local_decls, tcx).ty, tcx) {
                        // Recurses to find more chain subjects.
                        let res = size_invariant_iterator_subjects_by_chain(
                            arg_place,
                            chain_block,
                            basic_blocks,
                            local_decls,
                            dominators,
                            tcx,
                        );
                        results.extend(res.0);
                        n_empty_subjects += res.1;
                    } else {
                        // May still be possible to unwrap "non-growing" adapters.
                        intermediate_subject_places.insert((arg_place, chain_block));
                    }
                }
                IterSubject::Empty => {
                    results.insert((IterSubject::Empty, chain_block));
                    n_empty_subjects += 1;
                }
            }
        }
    } else {
        // Handles simple unchained iterators.
        intermediate_subject_places.insert((iterator_arg_place, anchor_block));
    }

    // Processes intermediate results.
    for (intermediate_subject_place, intermediate_subject_block) in intermediate_subject_places {
        let iter_subject_info = size_invariant_iterator_subject(
            intermediate_subject_place,
            intermediate_subject_block,
            basic_blocks,
            local_decls,
            dominators,
            tcx,
        );
        match iter_subject_info {
            Some((iter_subject_place, iter_subject_block)) => {
                if is_iter_chain_ty(iter_subject_place.ty(local_decls, tcx).ty, tcx) {
                    // Recurses to find more chain subjects.
                    let res = size_invariant_iterator_subjects_by_chain(
                        iter_subject_place,
                        iter_subject_block,
                        basic_blocks,
                        local_decls,
                        dominators,
                        tcx,
                    );
                    results.extend(res.0);
                    n_empty_subjects += res.1;
                } else {
                    // We can't unwrap any further, so the current subject is final.
                    results.insert((iter_subject_place.into(), iter_subject_block));
                }
            }
            None => {
                // Analysis results have to be "joined", so we can't lose any branches.
                results.insert((
                    intermediate_subject_place.into(),
                    intermediate_subject_block,
                ));
            }
        }
    }

    (results, n_empty_subjects)
}

/// Returns places and basic block for the args/operands of an `Iterator::chain` call (if any).
fn iter_chain_subjects<'tcx>(
    iterator_arg_place: Place<'tcx>,
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    dominators: &Dominators<BasicBlock>,
    tcx: TyCtxt<'tcx>,
) -> Option<(IterSubject<'tcx>, IterSubject<'tcx>, BasicBlock)> {
    if !is_iter_chain_ty(iterator_arg_place.ty(local_decls, tcx).ty, tcx) {
        return None;
    }
    let (terminator, iterator_subject_block) = analyze::pre_anchor_assign_terminator(
        iterator_arg_place,
        anchor_block,
        anchor_block,
        basic_blocks,
        dominators,
    )?;

    let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
        return None;
    };
    let (def_id, ..) = func.const_fn_def()?;
    let iterator_next_def_id = iterator_assoc_item_def_id("chain", tcx)
        .expect("Expected DefId for `std::iter::Iterator::chain`");
    if def_id != iterator_next_def_id {
        return None;
    }

    match args.deref() {
        [first, second] => {
            let into_iter_subject = |operand: &Operand<'tcx>| {
                operand.place().map(IterSubject::from).or_else(|| {
                    let op_ty = operand.ty(local_decls, tcx);
                    is_iter_empty_ty(op_ty, tcx).then_some(IterSubject::Empty)
                })
            };
            Some((
                into_iter_subject(&first.node)?,
                into_iter_subject(&second.node)?,
                iterator_subject_block,
            ))
        }
        _ => None,
    }
}

/// An iterator subject.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum IterSubject<'tcx> {
    /// Place of an iterator subject.
    Place(Place<'tcx>),
    /// An `std::iter::Empty` subject.
    ///
    /// **NOTE:** It's special cased because it's represented as a constant operand.
    Empty,
}

impl<'tcx> From<Place<'tcx>> for IterSubject<'tcx> {
    fn from(value: Place<'tcx>) -> Self {
        Self::Place(value)
    }
}

/// Returns the DefId of an `Iterator` assoc item, given it's name.
fn iterator_assoc_item_def_id(name: &str, tcx: TyCtxt) -> Option<DefId> {
    let iterator_trait_def_id = tcx
        .lang_items()
        .get(LangItem::Iterator)
        .expect("Expected `std::iter::Iterator` lang item");
    tcx.associated_items(iterator_trait_def_id)
        .filter_by_name_unhygienic(Symbol::intern(name))
        .next()
        .map(|item| item.def_id)
}

/// Returns place and basic block (if any) of innermost iterator subject to which
/// no "growing" iterator adapters are applied.
///
/// **NOTE:** See [`size_invariant_iterator_subject_by_chain`] for a similar function that
/// operates on each chain.
fn size_invariant_iterator_subject<'tcx>(
    iterator_arg_place: Place<'tcx>,
    anchor_block: BasicBlock,
    basic_blocks: &BasicBlocks<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    dominators: &Dominators<BasicBlock>,
    tcx: TyCtxt<'tcx>,
) -> Option<(Place<'tcx>, BasicBlock)> {
    // Finds place and basic block for outermost `Iterator` transformation operand/arg (if any).
    let (terminator, mut iterator_subject_block) = analyze::pre_anchor_assign_terminator(
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
        &mut iterator_subject_block,
        anchor_block,
        basic_blocks,
        local_decls,
        dominators,
        tcx,
    );

    // Finds place and basic block for innermost `Iterator` transformation operand/arg (if any).
    if is_into_iter_ty(iterator_subject_place.ty(local_decls, tcx).ty, tcx) {
        let (into_iter_def_terminator, into_iter_block) = analyze::pre_anchor_assign_terminator(
            iterator_subject_place,
            iterator_subject_block,
            anchor_block,
            basic_blocks,
            dominators,
        )?;
        let collection_place = into_iter_operand(&into_iter_def_terminator, tcx)?;
        iterator_subject_place = collection_place;
        iterator_subject_block = into_iter_block;
    } else if is_iter_by_ref_ty(iterator_subject_place.ty(local_decls, tcx).ty, tcx) {
        let (iter_by_ref_terminator, iter_by_ref_block) = analyze::pre_anchor_assign_terminator(
            iterator_subject_place,
            iterator_subject_block,
            anchor_block,
            basic_blocks,
            dominators,
        )?;
        let iter_by_ref_ty_place = iter_by_ref_operand(&iter_by_ref_terminator, tcx)
            .or_else(|| into_iter_operand(&iter_by_ref_terminator, tcx))?;
        iterator_subject_place = iter_by_ref_ty_place;
        iterator_subject_block = iter_by_ref_block;
    }

    Some((iterator_subject_place, iterator_subject_block))
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
        let Some((adapter_arg_place, adapter_block)) =
            adapter_def_call.and_then(|(terminator, block)| {
                iterator_adapter_operand(&terminator, tcx).map(|place| (place, block))
            })
        else {
            return;
        };
        *iterator_place = adapter_arg_place;
        *parent_block = adapter_block;
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

/// Returns true if the type `Iterator` chain adapter (i.e. `std::iter::Chain`).
fn is_iter_chain_ty(ty: Ty, tcx: TyCtxt) -> bool {
    ty.peel_refs().ty_adt_def().is_some_and(|adt_def| {
        let adt_def_id = adt_def.did();
        tcx.item_name(adt_def_id).as_str() == "Chain"
            && matches!(tcx.crate_name(adt_def_id.krate).as_str(), "core" | "std")
    })
}

/// Returns true if the type is `std::iter::Once`.
fn is_iter_once_ty(ty: Ty, tcx: TyCtxt) -> bool {
    ty.peel_refs().ty_adt_def().is_some_and(|adt_def| {
        let adt_def_id = adt_def.did();
        tcx.item_name(adt_def_id).as_str() == "Once"
            && matches!(tcx.crate_name(adt_def_id.krate).as_str(), "core" | "std")
    })
}

/// Returns true if the type is `std::iter::Empty`.
fn is_iter_empty_ty(ty: Ty, tcx: TyCtxt) -> bool {
    ty.peel_refs().ty_adt_def().is_some_and(|adt_def| {
        let adt_def_id = adt_def.did();
        tcx.item_name(adt_def_id).as_str() == "Empty"
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

/// An upper bound.
#[derive(Debug, Clone, Copy)]
struct UpperBound {
    /// Upper bound value.
    value: Option<u128>,
    /// Maximum possible value from the value domain (used for overflow protection).
    max: u128,
    /// When set to true, value is always return as None.
    invalidated: bool,
}

impl UpperBound {
    /// Creates new upper bound and sets a maxima that it shouldn't overflow.
    pub fn new(value: Option<u128>, max: u128) -> Self {
        Self {
            value,
            max,
            invalidated: false,
        }
    }

    /// Creates new unknown upper bound with a usize maxima.
    pub fn new_usize() -> Self {
        Self::new(None, utils::target_usize_max())
    }

    /// Increase the upper bound by value if it doesn't overflow the maximum value,
    /// otherwise unsets it bound.
    pub fn increase(&mut self, value: u128) {
        if self.invalidated {
            self.set(None);
            return;
        }
        let new_bound = if value > self.max {
            None
        } else {
            match self.value {
                Some(current) if current <= self.max && value <= (self.max - current) => {
                    Some(current + value)
                }
                None => Some(value),
                _ => None,
            }
        };
        self.set(new_bound);
    }

    /// Clears upper bound value and sets a flag for ignoring further updates.
    pub fn invalidate(&mut self) {
        self.value = None;
        self.invalidated = true;
    }

    /// Returns upper bound value.
    pub fn value(&self) -> Option<u128> {
        if self.invalidated {
            None
        } else {
            self.value
        }
    }

    /// Returns `true` if upper bound value is a [`Option::None`].
    pub fn is_none(&self) -> bool {
        self.value.is_none()
    }

    /// Sets upper bound value to zero.
    pub fn zero(&mut self) {
        self.set(Some(0));
    }

    /// Sets upper bound value.
    fn set(&mut self, value: Option<u128>) {
        self.value = if self.invalidated { None } else { value }
    }
}
