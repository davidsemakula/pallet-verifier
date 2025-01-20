//! `rustc` `MirPass` for adding annotations for slice (i.e. `[T]`) invariants.

use rustc_hash::FxHashSet;
use rustc_hir::LangItem;
use rustc_middle::{
    mir::{
        visit::Visitor, BasicBlock, BasicBlocks, Body, HasLocalDecls, LocalDecls, Location,
        MirPass, Operand, Place, Terminator, TerminatorKind,
    },
    ty::TyCtxt,
};
use rustc_span::source_map::Spanned;

use crate::providers::{
    analyze,
    annotate::{self, Annotation, CondOp},
    storage::{self, StorageInvariant},
};

/// Adds slice (i.e. `[T]`) invariant annotations.
pub struct SliceInvariants;

impl<'tcx> MirPass<'tcx> for SliceInvariants {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // Generates slice annotations.
        let mut visitor = SliceVisitor::new(tcx, &body.basic_blocks, body.local_decls());
        visitor.visit_body(body);
        let mut annotations = visitor.annotations;

        // Propagates storage related invariants.
        if !visitor.storage_invariants.is_empty() {
            storage::propagate_invariants(visitor.storage_invariants, &mut annotations, body, tcx);
        }

        // Adds slice annotations.
        if !annotations.is_empty() {
            annotate::add_annotations(annotations, body, tcx);
        }
    }
}

/// Collects slice annotations.
struct SliceVisitor<'tcx, 'pass> {
    tcx: TyCtxt<'tcx>,
    basic_blocks: &'pass BasicBlocks<'tcx>,
    local_decls: &'pass LocalDecls<'tcx>,
    /// A list of slice annotation declarations.
    annotations: Vec<Annotation<'tcx>>,
    /// A list of FRAME storage related invariants.
    storage_invariants: Vec<StorageInvariant<'tcx>>,
}

impl<'tcx, 'pass> SliceVisitor<'tcx, 'pass> {
    fn new(
        tcx: TyCtxt<'tcx>,
        basic_blocks: &'pass BasicBlocks<'tcx>,
        local_decls: &'pass LocalDecls<'tcx>,
    ) -> Self {
        Self {
            tcx,
            basic_blocks,
            local_decls,
            annotations: Vec::new(),
            storage_invariants: Vec::new(),
        }
    }

    /// Analyzes and annotates slice terminators.
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

            // Only continues if `DefId` is a slice associated item.
            if !analyze::is_slice_assoc_item(def_id, self.tcx) {
                return;
            }

            // Handles calls to slice `binary_search` methods.
            if self.tcx.opt_item_name(def_id).is_some_and(|name| {
                matches!(
                    name.as_str(),
                    "binary_search" | "binary_search_by" | "binary_search_by_key"
                )
            }) {
                self.process_binary_search(args, destination, target.as_ref(), location);
            }

            // Handles calls to `[T]::partition_point` methods.
            if self
                .tcx
                .opt_item_name(def_id)
                .is_some_and(|name| name.as_str() == "partition_point")
            {
                self.process_partition_point(args, destination, target.as_ref(), location);
            }
        }
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

        // Finds place for operand/arg and basic block for a slice `Deref` call (if any).
        let dominators = self.basic_blocks.dominators();
        let Some((slice_deref_arg_place, slice_deref_bb)) = analyze::deref_subject(
            binary_search_arg_place,
            location.block,
            location.block,
            self.basic_blocks,
            dominators,
            self.tcx,
        ) else {
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
        // See [`analyze::track_safe_result_transformations`] for details.
        if let Some(target) = target {
            let mut unwrap_arg_place = *destination;
            let mut unwrap_arg_def_bb = location.block;
            analyze::track_safe_result_transformations(
                &mut unwrap_arg_place,
                &mut unwrap_arg_def_bb,
                *target,
                self.basic_blocks,
                self.tcx,
            );
            let unwrap_place_info = analyze::call_target(&self.basic_blocks[unwrap_arg_def_bb])
                .and_then(|next_target| {
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
                    let (unwrap_dest_place, post_unwrap_target) =
                        analyze::safe_transform_destination(
                            unwrap_arg_place,
                            next_bb_data,
                            crate_adt_and_fn_name_check,
                            self.tcx,
                        )?;
                    let next_target_bb = post_unwrap_target?;

                    // Checks that second arg is an identity function or closure and, if true,
                    // returns unwrap destination place and next target.
                    // See [`analyze::is_identity_fn`] and [`analyze::is_identity_closure`] for details.
                    let unwrap_terminator = next_bb_data.terminator.as_ref()?;
                    let TerminatorKind::Call {
                        args: unwrap_args, ..
                    } = &unwrap_terminator.kind
                    else {
                        return None;
                    };
                    let unwrap_second_arg = unwrap_args.get(1)?;
                    let is_identity = analyze::is_identity_fn(&unwrap_second_arg.node, self.tcx)
                        || analyze::is_identity_closure(&unwrap_second_arg.node, self.tcx);
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
                    CondOp::Le,
                ));
            }
        }

        // Tracks `Result::Ok` switch target info of return value of slice `binary_search` methods.
        // Also tracks variant "safe" transformations (e.g. `ControlFlow::Continue` and
        // `Option::Some` transformations)
        // See [`analyze::track_safe_primary_opt_result_variant_transformations`] for details.
        let mut switch_target_place = *destination;
        let mut switch_target_bb = location.block;
        let mut switch_target_variant_name = "Ok".to_string();
        let mut switch_target_variant_idx = analyze::variant_idx(LangItem::ResultOk, self.tcx);
        if let Some(target) = target {
            analyze::track_safe_primary_opt_result_variant_transformations(
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
        // See [`analyze::track_safe_result_err_transformations`] for details.
        let mut switch_target_place_alt = *destination;
        let mut switch_target_bb_alt = location.block;
        let mut switch_target_variant_name_alt = "Err".to_string();
        let mut switch_target_variant_idx_alt = analyze::variant_idx(LangItem::ResultErr, self.tcx);
        if let Some(target) = target {
            analyze::track_safe_result_err_transformations(
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
        let switch_targets = analyze::collect_switch_targets_for_discr_value(
            switch_target_place,
            switch_target_variant_idx.as_u32() as u128,
            switch_target_bb,
            self.basic_blocks,
        );

        // Collects `Result::Err` (or equivalent safe transformation) target blocks
        // for switches based on the discriminant of return value of slice `binary_search`
        // in successor blocks.
        let switch_targets_err = analyze::collect_switch_targets_for_discr_value(
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
                CondOp::Lt,
                switch_targets,
            ),
            // `Result::Err` switch target info.
            (
                switch_target_place_alt,
                &switch_target_variant_name_alt,
                switch_target_variant_idx_alt,
                // index <= collection length/size for `Result::Err`.
                CondOp::Le,
                switch_targets_err,
            ),
        ] {
            for target_bb in targets_blocks {
                for (stmt_idx, stmt) in self.basic_blocks[target_bb].statements.iter().enumerate() {
                    // Finds variant downcast to `usize` places (if any) for the switch target variant.
                    let Some(downcast_place) = analyze::variant_downcast_to_ty_place(
                        target_place,
                        target_variant_name,
                        target_variant_idx,
                        self.tcx.types.usize,
                        stmt,
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

        // Retrieves info needed to construct a collection length/size call for the slice subject
        // (if possible).
        let len_bound_info = analyze::borrowed_collection_len_call_info(
            slice_deref_arg_place,
            slice_deref_bb,
            self.basic_blocks,
            self.local_decls,
            self.tcx,
        );

        // Finds FRAME storage subject (if any).
        let storage_info = storage::storage_subject(
            slice_deref_arg_place,
            slice_deref_bb,
            location.block,
            self.basic_blocks,
            dominators,
            self.tcx,
        );
        let mut storage_invariants = FxHashSet::default();

        // Composes collection length/size bound annotations for extracted invariants.
        for (annotation_location, invariant_place, cond_op) in invariants {
            // Declares a collection length/size bound annotation.
            if let Some((collection_place, region, len_call_info)) = &len_bound_info {
                self.annotations.push(Annotation::Len(
                    annotation_location,
                    cond_op,
                    invariant_place,
                    *collection_place,
                    *region,
                    len_call_info.clone(),
                ));
            }

            // Declares a slice length/size bound annotation.
            if let Some(annotation) = annotate::compose_slice_len_annotation(
                annotation_location,
                cond_op,
                invariant_place,
                binary_search_arg_place,
                self.local_decls,
                self.tcx,
            ) {
                self.annotations.push(annotation);
            }

            // Declares an `isize::MAX` bound annotation (if appropriate).
            if analyze::is_isize_bound_collection(
                slice_deref_arg_place.ty(self.local_decls, self.tcx).ty,
                self.tcx,
            ) {
                self.annotations.push(Annotation::Isize(
                    annotation_location,
                    cond_op,
                    invariant_place,
                ));
            }

            // Tracks invariants that need to propagated to other storage uses.
            if storage_info.is_some() && len_bound_info.is_some() {
                storage_invariants.insert((annotation_location, cond_op, invariant_place));
            }
        }

        // Adds storage invariants.
        if !storage_invariants.is_empty() {
            if let Some((storage_item, use_location)) = storage_info {
                self.storage_invariants
                    .push((storage_item, use_location, storage_invariants));
            }
        }
    }

    /// Analyzes and annotates calls to `[T]::partition_point`.
    fn process_partition_point(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: Option<&BasicBlock>,
        location: Location,
    ) {
        // Only continues if the terminator has a target basic block.
        let Some(target) = target else {
            return;
        };

        // Finds place for slice `partition_point` operand/arg.
        let partition_point_arg = args
            .first()
            .expect("Expected an arg for slice `partition_point` method");
        let Some(partition_point_arg_place) = partition_point_arg.node.place() else {
            return;
        };

        // Length invariant annotations are added at the beginning of the next block.
        let annotation_location = Location {
            block: *target,
            statement_index: 0,
        };
        let cond_op = CondOp::Le;

        // Declares a slice length/size bound annotation.
        if let Some(annotation) = annotate::compose_slice_len_annotation(
            annotation_location,
            cond_op,
            *destination,
            partition_point_arg_place,
            self.local_decls,
            self.tcx,
        ) {
            self.annotations.push(annotation);
        }

        // Finds place for operand/arg and basic block for a slice `Deref` call (if any).
        let dominators = self.basic_blocks.dominators();
        let Some((slice_deref_arg_place, slice_deref_bb)) = analyze::deref_subject(
            partition_point_arg_place,
            location.block,
            location.block,
            self.basic_blocks,
            dominators,
            self.tcx,
        ) else {
            return;
        };

        // Declares an `isize::MAX` bound annotation (if appropriate).
        if analyze::is_isize_bound_collection(
            slice_deref_arg_place.ty(self.local_decls, self.tcx).ty,
            self.tcx,
        ) {
            self.annotations.push(Annotation::Isize(
                annotation_location,
                cond_op,
                *destination,
            ));
        }

        // Retrieves info needed to construct a collection length/size call for the slice subject
        // (if possible).
        let len_bound_info = analyze::borrowed_collection_len_call_info(
            slice_deref_arg_place,
            slice_deref_bb,
            self.basic_blocks,
            self.local_decls,
            self.tcx,
        );

        // Declares a collection length/size bound annotation.
        if let Some((collection_place, region, len_call_info)) = len_bound_info {
            self.annotations.push(Annotation::Len(
                annotation_location,
                cond_op,
                *destination,
                collection_place,
                region,
                len_call_info,
            ));

            // Finds FRAME storage subject (if any).
            let storage_info = storage::storage_subject(
                slice_deref_arg_place,
                slice_deref_bb,
                location.block,
                self.basic_blocks,
                dominators,
                self.tcx,
            );

            // Adds storage invariants.
            if let Some((storage_item, use_location)) = storage_info {
                self.storage_invariants.push((
                    storage_item,
                    use_location,
                    FxHashSet::from_iter([(annotation_location, cond_op, *destination)]),
                ));
            }
        }
    }
}

impl<'tcx, 'pass> Visitor<'tcx> for SliceVisitor<'tcx, 'pass> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.process_terminator(terminator, location);
        self.super_terminator(terminator, location);
    }
}
