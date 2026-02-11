//! `rustc` [`MirPass`] for adding annotations for slice (i.e. `[T]`) invariants.

use rustc_abi::VariantIdx;
use rustc_data_structures::graph::iterate::post_order_from;
use rustc_hash::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, BasicBlocks, Body, HasLocalDecls, LocalDecls, Location, Operand, Place,
        RETURN_PLACE, Rvalue, StatementKind, Terminator, TerminatorKind, UnOp, visit::Visitor,
    },
    ty::TyCtxt,
};
use rustc_span::source_map::Spanned;

use crate::providers::{
    analyze::{self, SwitchVariant},
    annotate::{self, Annotation, CondOp},
    closure,
    passes::MirPass,
    storage::{
        self, InvariantSource, PropagatedVariant, StorageId, StorageInvariant, StorageInvariantEnv,
    },
};

/// Adds slice (i.e. `[T]`) invariant annotations.
pub struct SliceInvariants;

impl<'tcx> MirPass<'tcx> for SliceInvariants {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // Generates slice annotations.
        let def_id = body.source.def_id();
        let mut visitor = SliceVisitor::new(def_id, &body.basic_blocks, body.local_decls(), tcx);
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
    def_id: DefId,
    basic_blocks: &'pass BasicBlocks<'tcx>,
    local_decls: &'pass LocalDecls<'tcx>,
    tcx: TyCtxt<'tcx>,
    /// A list of slice annotation declarations.
    annotations: Vec<Annotation<'tcx>>,
    /// A list of FRAME storage related invariants.
    storage_invariants: Vec<StorageInvariant<'tcx>>,
}

impl<'tcx, 'pass> SliceVisitor<'tcx, 'pass> {
    fn new(
        def_id: DefId,
        basic_blocks: &'pass BasicBlocks<'tcx>,
        local_decls: &'pass LocalDecls<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        Self {
            def_id,
            basic_blocks,
            local_decls,
            tcx,
            annotations: Vec::new(),
            storage_invariants: Vec::new(),
        }
    }

    /// Analyzes and annotates slice terminators.
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
        let Some((def_id, ..)) = func.const_fn_def() else {
            return;
        };

        // Handles slice associated fns.
        if analyze::is_slice_assoc_item(def_id, self.tcx) {
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
        } else {
            // Handles propagated return place storage binary search invariants.
            let storage_invariant_env = storage::find_invariant_env(def_id, self.tcx)
                .filter(|invariant| invariant.source == InvariantSource::SliceBinarySearch);
            if let Some(storage_invariant_env) = storage_invariant_env {
                self.propagate_storage_binary_search_invariant_env(
                    storage_invariant_env,
                    destination,
                    target.as_ref(),
                    location,
                );
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
        let Some((slice_deref_arg_place, slice_deref_block)) = analyze::deref_subject(
            binary_search_arg_place,
            location.block,
            location.block,
            self.basic_blocks,
            dominators,
            self.tcx,
        ) else {
            return;
        };

        // Collects collection length/size bound invariants and returned `Result`
        // (and "safe" transformations) switch target info.
        let (
            // Collection length/size bound invariants.
            invariants,
            // `Result::Ok` (and "safe" transformations) switch target info.
            (switch_target_place, switch_target_block, switch_variant),
            // `Result::Err` (and "safe" transformations) switch target info.
            (switch_target_place_alt, _, switch_variant_alt),
            // `Result::unwrap`, `Result::unwrap_or`, `Result::unwrap_or_else`
            // (through "safe" transformations) destination place target info.
            unwrap_or_else_target_info,
        ) = binary_search_analysis(
            destination,
            target,
            location,
            self.basic_blocks,
            self.local_decls,
            self.tcx,
        );

        // Retrieves info needed to construct a slice length/size call (if possible).
        let slice_len_bound_info =
            analyze::slice_len_call_info(binary_search_arg_place, self.local_decls, self.tcx);

        // Retrieves info needed to construct a collection length/size call for the slice subject (if possible).
        let collection_len_bound_info = analyze::borrowed_collection_len_call_info(
            slice_deref_arg_place,
            slice_deref_block,
            self.basic_blocks,
            self.local_decls,
            self.tcx,
        );

        // Finds FRAME storage subject (if any).
        let storage_info = storage::storage_subject(
            slice_deref_arg_place,
            slice_deref_block,
            location.block,
            self.basic_blocks,
            dominators,
            self.tcx,
        );

        // Composes collection length/size bound annotations for extracted invariants.
        let mut storage_invariants = FxHashSet::default();
        for (annotation_location, cond_op, invariant_place) in invariants {
            // Adds locations of uses of invariant place as terminator operands in subsequent blocks.
            // NOTE: This makes analysis more tractable in cases where the invariant place uses are
            // guarded by complex branching conditions.
            let locations = std::iter::once(annotation_location).chain(
                post_order_from(self.basic_blocks, annotation_location.block)
                    .into_iter()
                    .filter_map(|successor| {
                        if successor != annotation_location.block
                            && let Some(terminator) = &self.basic_blocks[successor].terminator
                            && let TerminatorKind::Call { args, .. } = &terminator.kind
                        {
                            let is_invariant_arg = args.iter().any(|arg| {
                                arg.node
                                    .place()
                                    .is_some_and(|place| place == invariant_place)
                            });
                            is_invariant_arg.then_some(Location {
                                block: successor,
                                statement_index: 0,
                            })
                        } else {
                            None
                        }
                    }),
            );

            // Declares a collection length/size bound annotation.
            if let Some((collection_place, region, len_call_info)) = &collection_len_bound_info {
                self.annotations.extend(locations.clone().map(|location| {
                    Annotation::Len(
                        location,
                        cond_op,
                        invariant_place,
                        *collection_place,
                        *region,
                        len_call_info.clone(),
                    )
                }));
            }

            // Declares slice length/size bound annotations.
            if let Some((region, call_info)) = &slice_len_bound_info {
                self.annotations.extend(locations.clone().map(|location| {
                    Annotation::Len(
                        location,
                        cond_op,
                        invariant_place,
                        binary_search_arg_place,
                        *region,
                        call_info.clone(),
                    )
                }));
            }

            // Declares `isize::MAX` bound annotations (if appropriate).
            if analyze::is_isize_bound_collection(
                slice_deref_arg_place.ty(self.local_decls, self.tcx).ty,
                self.tcx,
            ) {
                self.annotations.extend(
                    locations.clone().map(|location| {
                        Annotation::new_isize_max(location, cond_op, invariant_place)
                    }),
                );
            }

            // Tracks invariants that need to propagated to other storage uses.
            if storage_info.is_some() && collection_len_bound_info.is_some() {
                storage_invariants.insert((annotation_location, cond_op, invariant_place));
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

        // Propagate index invariant to `Result` (and `Option`) adapter input closures (if any).
        if collection_len_bound_info.is_some()
            && let Some(next_target) = analyze::call_target(&self.basic_blocks[switch_target_block])
        {
            // Collects collection related places (including all deref subjects).
            let mut collection_def_places = vec![
                (binary_search_arg_place, location.block),
                (slice_deref_arg_place, slice_deref_block),
            ];
            let deref_subjects = analyze::deref_subjects_recursive(
                slice_deref_arg_place,
                slice_deref_block,
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
                &collection_def_places,
                self.basic_blocks,
                self.tcx,
            );
        }

        // Propagate return place storage index invariant to callers.
        if let Some((storage_item, _)) = storage_info {
            propagate_storage_invariant(
                self.def_id,
                StorageId::DefId(storage_item.prefix),
                Some((switch_target_place, switch_variant)),
                Some((switch_target_place_alt, switch_variant_alt)),
                unwrap_or_else_target_info.map(|(place, _)| place),
                self.tcx,
            );
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
        if let Some((region, call_info)) =
            analyze::slice_len_call_info(partition_point_arg_place, self.local_decls, self.tcx)
        {
            self.annotations.push(Annotation::Len(
                annotation_location,
                cond_op,
                *destination,
                partition_point_arg_place,
                region,
                call_info,
            ));
        }

        // Finds place for operand/arg and basic block for a slice `Deref` call (if any).
        let dominators = self.basic_blocks.dominators();
        let Some((slice_deref_arg_place, slice_deref_block)) = analyze::deref_subject(
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
            self.annotations.push(Annotation::new_isize_max(
                annotation_location,
                cond_op,
                *destination,
            ));
        }

        // Retrieves info needed to construct a collection length/size call for the slice subject
        // (if possible).
        let len_bound_info = analyze::borrowed_collection_len_call_info(
            slice_deref_arg_place,
            slice_deref_block,
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
                slice_deref_block,
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

    // Propagates return place storage binary search invariants.
    fn propagate_storage_binary_search_invariant_env(
        &mut self,
        invariant_env: StorageInvariantEnv,
        destination: &Place<'tcx>,
        target: Option<&BasicBlock>,
        location: Location,
    ) {
        // Collects transformed storage invariants and switch target info.
        let (invariants, switch_target_info, switch_target_info_alt, unified_target_info) =
            match invariant_env.propagated_variant {
                PropagatedVariant::Primary(switch_variant) => {
                    let (invariants, (switch_target_place, _, new_switch_variant)) =
                        binary_search_result_ok_analysis(
                            destination,
                            target,
                            location,
                            switch_variant,
                            self.basic_blocks,
                            self.tcx,
                        );
                    (
                        invariants,
                        Some((switch_target_place, new_switch_variant)),
                        None,
                        None,
                    )
                }
                PropagatedVariant::Alt(switch_variant_alt) => {
                    let (invariants, (switch_target_place_alt, _, new_switch_variant_alt)) =
                        binary_search_result_err_analysis(
                            destination,
                            target,
                            location,
                            switch_variant_alt,
                            self.basic_blocks,
                            self.tcx,
                        );
                    (
                        invariants,
                        None,
                        Some((switch_target_place_alt, new_switch_variant_alt)),
                        None,
                    )
                }
                PropagatedVariant::Unknown(switch_variant, switch_variant_alt) => {
                    let (mut invariants, (switch_target_place, _, new_switch_variant)) =
                        binary_search_result_ok_analysis(
                            destination,
                            target,
                            location,
                            switch_variant,
                            self.basic_blocks,
                            self.tcx,
                        );
                    let (invariants_alt, (switch_target_place_alt, _, new_switch_variant_alt)) =
                        binary_search_result_err_analysis(
                            destination,
                            target,
                            location,
                            switch_variant_alt,
                            self.basic_blocks,
                            self.tcx,
                        );
                    invariants.extend(invariants_alt);
                    (
                        invariants,
                        Some((switch_target_place, new_switch_variant)),
                        Some((switch_target_place_alt, new_switch_variant_alt)),
                        None,
                    )
                }
                PropagatedVariant::Union => (
                    FxHashSet::from_iter([(location, CondOp::Le, *destination)]),
                    None,
                    None,
                    Some(*destination),
                ),
            };

        // Adds storage invariants.
        self.storage_invariants.push((
            StorageId::DefHash(invariant_env.storage_def_hash.clone()),
            location.block,
            invariants,
        ));

        // Propagate return place storage index invariant to callers.
        propagate_storage_invariant(
            self.def_id,
            StorageId::DefHash(invariant_env.storage_def_hash),
            switch_target_info,
            switch_target_info_alt,
            unified_target_info,
            self.tcx,
        );
    }
}

impl<'tcx> Visitor<'tcx> for SliceVisitor<'tcx, '_> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.process_terminator(terminator, location);
        self.super_terminator(terminator, location);
    }
}

/// Convenience alias for tracking invariant info.
type Invariant<'tcx> = (Location, CondOp, Place<'tcx>);

/// Convenience alias for tracking switch target info.
type SwitchTargetInfo<'tcx> = (Place<'tcx>, BasicBlock, SwitchVariant);

/// Collects collection length/size bound invariants and returned `Result`
/// (and "safe" transformations) switch target info for slice `binary_search` methods.
fn binary_search_analysis<'tcx>(
    destination: &Place<'tcx>,
    target: Option<&BasicBlock>,
    location: Location,
    basic_blocks: &BasicBlocks<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> (
    FxHashSet<Invariant<'tcx>>,
    SwitchTargetInfo<'tcx>,
    SwitchTargetInfo<'tcx>,
    Option<(Place<'tcx>, BasicBlock)>,
) {
    // Tracks collection length/size bound invariants.
    let mut invariants = FxHashSet::default();

    // Tracks `Result::unwrap`, `Result::unwrap_or` or `Result::unwrap_or_else`
    // destination place invariants, See [`binary_search_result_unwrap_analysis`] for details.
    // Also tracks/allows "safe" transformations before `unwrap_or_else` call
    // (e.g. via `Result::inspect`, `Result::inspect_err` e.t.c).
    // See [`analyze::track_safe_result_transformations`] for details.
    let mut unwrap_or_else_target_info = None;
    if let Some(target) = target {
        if let Some(results) = binary_search_result_unwrap_analysis(
            destination,
            *target,
            location,
            basic_blocks,
            local_decls,
            tcx,
        ) {
            // Adds collection length/size invariant for unwrap place.
            invariants.extend(results.0);

            // Tracks `Result::unwrap_or_else` target place and block for further analysis.
            unwrap_or_else_target_info = Some(results.1);
        }
    }

    // Collects collection length/size bound invariants and target info for `Result::Ok` and `Result::Err`
    // (or equivalent safe transformation).
    let (ok_invariants, ok_target_info) = binary_search_result_ok_analysis(
        destination,
        target,
        location,
        SwitchVariant::ResultOk,
        basic_blocks,
        tcx,
    );
    let (err_invariants, err_target_info) = binary_search_result_err_analysis(
        destination,
        target,
        location,
        SwitchVariant::ResultErr,
        basic_blocks,
        tcx,
    );
    invariants.extend(ok_invariants);
    invariants.extend(err_invariants);

    // Returns analysis results.
    (
        invariants,
        ok_target_info,
        err_target_info,
        unwrap_or_else_target_info,
    )
}

/// Collects collection length/size bound invariants and returned `Result::Ok`
/// (and "safe" transformations) switch target info for slice `binary_search` methods.
fn binary_search_result_ok_analysis<'tcx>(
    destination: &Place<'tcx>,
    target: Option<&BasicBlock>,
    location: Location,
    mut switch_variant: SwitchVariant,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> (FxHashSet<Invariant<'tcx>>, SwitchTargetInfo<'tcx>) {
    // Tracks `Result::Ok` switch target info of return value of slice `binary_search` methods.
    // Also tracks variant "safe" transformations (e.g. `ControlFlow::Continue` and
    // `Option::Some` transformations)
    // See [`analyze::track_safe_primary_opt_result_variant_transformations`] for details.
    let mut switch_target_place = *destination;
    let mut switch_target_block = location.block;
    if let Some(target) = target {
        analyze::track_safe_primary_opt_result_variant_transformations(
            &mut switch_target_place,
            &mut switch_target_block,
            &mut switch_variant,
            *target,
            basic_blocks,
            tcx,
            false,
        );
    }

    // Collects collection length/size bound invariants
    // for `Result::Ok` (or equivalent safe transformation).
    let invariants = collect_variant_target_invariants(
        switch_target_place,
        switch_target_block,
        switch_variant.name(),
        switch_variant.idx(tcx),
        // index < collection length/size for `Result::Ok`.
        CondOp::Lt,
        basic_blocks,
        tcx,
    );

    // Returns analysis results.
    (
        invariants,
        (switch_target_place, switch_target_block, switch_variant),
    )
}

/// Collects collection length/size bound invariants and returned `Result::Err`
/// (and "safe" transformations) switch target info for slice `binary_search` methods.
fn binary_search_result_err_analysis<'tcx>(
    destination: &Place<'tcx>,
    target: Option<&BasicBlock>,
    location: Location,
    mut switch_variant: SwitchVariant,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> (FxHashSet<Invariant<'tcx>>, SwitchTargetInfo<'tcx>) {
    // Tracks `Result::Err` switch target info of return value of slice `binary_search` methods.
    // Also tracks variant "safe" transformations (e.g. to `Option::Some`, then optionally to
    // `ControlFlow::Continue` and `Option::Some` transformations).
    // See [`analyze::track_safe_result_err_transformations`] for details.
    let mut switch_target_place = *destination;
    let mut switch_target_block = location.block;
    if let Some(target) = target {
        analyze::track_safe_result_err_transformations(
            &mut switch_target_place,
            &mut switch_target_block,
            &mut switch_variant,
            *target,
            basic_blocks,
            tcx,
            false,
        );
    }

    // Collects collection length/size bound invariants
    // for `Result::Err` (or equivalent "safe" transformation).
    let invariants = collect_variant_target_invariants(
        switch_target_place,
        switch_target_block,
        switch_variant.name(),
        switch_variant.idx(tcx),
        // index <= collection length/size for `Result::Err`.
        CondOp::Le,
        basic_blocks,
        tcx,
    );

    // Returns analysis results.
    (
        invariants,
        (switch_target_place, switch_target_block, switch_variant),
    )
}

/// Collects collection length/size bound invariants and returned
/// `Result::unwrap`, `Result::unwrap_or` or `Result::unwrap_or_else`
/// (possibly after "safe" transformations) target info for slice `binary_search` methods.
///
/// # Note
///
/// - For `Result:unwrap_or_else`, the second arg must be an identity function or closure.
/// - For `Result::unwrap_or`, the second arg must be a slice length call for the binary search target,
///   or a collection length call for the binary search target's `Deref` subject.
fn binary_search_result_unwrap_analysis<'tcx>(
    destination: &Place<'tcx>,
    target: BasicBlock,
    location: Location,
    basic_blocks: &BasicBlocks<'tcx>,
    local_decls: &LocalDecls<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<(FxHashSet<Invariant<'tcx>>, (Place<'tcx>, BasicBlock))> {
    // Tracks collection length/size bound invariants.
    let mut invariants = FxHashSet::default();

    // Tracks/allows "safe" transformations before `unwrap_or_else` call
    // (e.g. via `Result::inspect`, `Result::inspect_err` e.t.c).
    // See [`analyze::track_safe_result_transformations`] for details.
    let mut unwrap_arg_place = *destination;
    let mut unwrap_arg_def_block = location.block;
    analyze::track_safe_result_transformations(
        &mut unwrap_arg_place,
        &mut unwrap_arg_def_block,
        target,
        basic_blocks,
        tcx,
    );

    // Retrieves `Result::unwrap`, `Result::unwrap_or` or `Result::unwrap_or_else`
    // destination place, next target block (if any) and
    // collection length upper bound invariant condition (if any).
    let next_block = analyze::call_target(&basic_blocks[unwrap_arg_def_block])?;
    let mut next_target_block = Some(next_block);
    let mut unwrap_place_info = None;
    let mut already_visited = FxHashSet::default();

    while let Some(block) = next_target_block
        && !already_visited.contains(&block)
    {
        let block_data = &basic_blocks[block];
        already_visited.insert(block);
        let terminator = block_data.terminator.as_ref()?;
        if let Some((unwrap_dest_place, post_unwrap_target)) =
            analyze::first_arg_transformer_call_destination(
                unwrap_arg_place,
                terminator,
                |crate_name, adt_name, fn_name| {
                    matches!(crate_name, "std" | "core")
                        && adt_name == "Result"
                        && fn_name == "unwrap"
                },
                tcx,
            )
        {
            unwrap_place_info = Some((unwrap_dest_place, post_unwrap_target, CondOp::Lt));
            next_target_block = None;
        } else if let Some((unwrap_dest_place, post_unwrap_target)) =
            analyze::first_arg_transformer_call_destination(
                unwrap_arg_place,
                terminator,
                |crate_name, adt_name, fn_name| {
                    matches!(crate_name, "std" | "core")
                        && adt_name == "Result"
                        && fn_name == "unwrap_or"
                },
                tcx,
            )
        {
            // Checks if the second `Result::unwrap_or` arg is a slice length call for the binary search target,
            // or a collection length call for the binary search target's `Deref` subject.
            if let TerminatorKind::Call {
                args: unwrap_args, ..
            } = &terminator.kind
                && let Some(unwrap_second_arg) = unwrap_args.get(1)
                && let Some(unwrap_second_arg_place) = unwrap_second_arg.node.place()
                && let Some(slice_place) = basic_blocks[location.block]
                    .terminator
                    .as_ref()
                    .and_then(|terminator| {
                        if let TerminatorKind::Call {
                            args,
                            destination: dest,
                            ..
                        } = &terminator.kind
                            && dest == destination
                        {
                            args.first()?.node.place()
                        } else {
                            None
                        }
                    })
            {
                // Checks if the second `Result::unwrap_or` arg is a slice length call.
                let is_slice_len_metadata_place = block_data.statements.iter().any(|stmt| {
                    if let StatementKind::Assign(assign) = &stmt.kind
                        && assign.0 == unwrap_second_arg_place
                        && let Rvalue::UnaryOp(UnOp::PtrMetadata, op) = &assign.1
                        && op.ty(local_decls, tcx).peel_refs().is_slice()
                        && let Some(op_place) = op.place()
                    {
                        let is_direct_slice_alias = || {
                            let slice_place_aliases = analyze::collect_place_aliases(
                                slice_place,
                                &basic_blocks[location.block],
                            );
                            let op_place_aliases =
                                analyze::collect_place_aliases(op_place, block_data);
                            slice_place_aliases.contains(&op_place)
                                || op_place_aliases.iter().any(|place| {
                                    *place == slice_place || slice_place_aliases.contains(place)
                                })
                        };

                        let is_deref_of_same_subject_as_slice = || {
                            let dominators = basic_blocks.dominators();
                            let slice_deref_subjects = analyze::deref_subjects_recursive(
                                slice_place,
                                location.block,
                                location.block,
                                basic_blocks,
                                dominators,
                                tcx,
                            );
                            let slice_deref_subjects_and_aliases: FxHashSet<_> =
                                slice_deref_subjects
                                    .iter()
                                    .map(|(place, _)| *place)
                                    .chain(slice_deref_subjects.iter().flat_map(
                                        |(deref_subject_place, deref_subject_block)| {
                                            analyze::collect_place_aliases(
                                                *deref_subject_place,
                                                &basic_blocks[*deref_subject_block],
                                            )
                                        },
                                    ))
                                    .collect();

                            let op_deref_subjects = analyze::deref_subjects_recursive(
                                op_place,
                                block,
                                block,
                                basic_blocks,
                                dominators,
                                tcx,
                            );
                            op_deref_subjects.iter().any(
                                |(deref_subject_place, deref_subject_block)| {
                                    if slice_deref_subjects_and_aliases
                                        .contains(deref_subject_place)
                                    {
                                        return true;
                                    }

                                    let deref_subject_aliases = analyze::collect_place_aliases(
                                        *deref_subject_place,
                                        &basic_blocks[*deref_subject_block],
                                    );
                                    deref_subject_aliases.iter().any(|place| {
                                        slice_deref_subjects_and_aliases.contains(place)
                                    })
                                },
                            )
                        };

                        op_place == slice_place
                            || is_direct_slice_alias()
                            || is_deref_of_same_subject_as_slice()
                    } else {
                        false
                    }
                });

                // Returns true if the second `Result::unwrap_or` arg is a collection length call,
                // where the collection is a `Deref` subject of the slice.
                // Note: This accounts for multiple derefs (e.g. `BoundedVec` -> `Vec` -> `slice`).
                let is_slice_deref_subject_len_place = || {
                    let dominators = basic_blocks.dominators();
                    let assign_info = analyze::pre_anchor_assign_terminator(
                        unwrap_second_arg_place,
                        block,
                        block,
                        basic_blocks,
                        dominators,
                    );
                    if let Some((assign_terminator, assign_block)) = assign_info
                        && let TerminatorKind::Call { func, args, .. } = &assign_terminator.kind
                        && args.len() == 1
                        && let Some((def_id, _)) = func.const_fn_def()
                        && let Some(fn_name) = tcx.opt_item_name(def_id)
                        && fn_name.as_str() == "len"
                        && let Some(len_arg_place) = args.first().and_then(|arg| arg.node.place())
                    {
                        // Returns true if any slice `Deref` subject which matches the receiver of the length call (if any).
                        let deref_subjects = analyze::deref_subjects_recursive(
                            slice_place,
                            location.block,
                            location.block,
                            basic_blocks,
                            dominators,
                            tcx,
                        );
                        let len_arg_aliases = analyze::collect_place_aliases(
                            len_arg_place,
                            &basic_blocks[assign_block],
                        );
                        deref_subjects
                            .iter()
                            .any(|(deref_subject_place, deref_subject_block)| {
                                if *deref_subject_place == len_arg_place
                                    || len_arg_aliases.contains(deref_subject_place)
                                {
                                    return true;
                                }

                                let deref_subject_aliases = analyze::collect_place_aliases(
                                    *deref_subject_place,
                                    &basic_blocks[*deref_subject_block],
                                );
                                deref_subject_aliases.iter().any(|place| {
                                    *place == len_arg_place || len_arg_aliases.contains(place)
                                })
                            })
                    } else {
                        false
                    }
                };

                if is_slice_len_metadata_place || is_slice_deref_subject_len_place() {
                    unwrap_place_info = Some((unwrap_dest_place, post_unwrap_target, CondOp::Le));
                }
            }
            next_target_block = None;
        } else if let Some((unwrap_dest_place, post_unwrap_target)) =
            analyze::first_arg_transformer_call_destination(
                unwrap_arg_place,
                terminator,
                |crate_name, adt_name, fn_name| {
                    matches!(crate_name, "std" | "core")
                        && adt_name == "Result"
                        && fn_name == "unwrap_or_else"
                },
                tcx,
            )
        {
            // Checks that second arg is an identity function or closure and, if true,
            // returns unwrap destination place and next target.
            // See [`analyze::is_identity_fn`] and [`analyze::is_identity_closure`] for details.
            if let TerminatorKind::Call {
                args: unwrap_args, ..
            } = &terminator.kind
                && let Some(unwrap_second_arg) = unwrap_args.get(1)
                && (analyze::is_identity_fn(&unwrap_second_arg.node, tcx)
                    || analyze::is_identity_closure(&unwrap_second_arg.node, tcx))
            {
                unwrap_place_info = Some((unwrap_dest_place, post_unwrap_target, CondOp::Le));
            }
            next_target_block = None;
        } else {
            next_target_block = match &terminator.kind {
                TerminatorKind::Call {
                    args,
                    destination,
                    target,
                    ..
                } if *destination != unwrap_arg_place
                    && args.iter().all(|arg| {
                        arg.node
                            .place()
                            .is_none_or(|place| place != unwrap_arg_place)
                    }) =>
                {
                    *target
                }
                TerminatorKind::Drop { place, target, .. } if *place != unwrap_arg_place => {
                    Some(*target)
                }
                TerminatorKind::Goto { target }
                | TerminatorKind::Assert { target, .. }
                | TerminatorKind::FalseEdge {
                    real_target: target,
                    ..
                }
                | TerminatorKind::FalseUnwind {
                    real_target: target,
                    ..
                } => Some(*target),
                TerminatorKind::Yield {
                    value,
                    resume: target,
                    ..
                } if value.place().is_none_or(|place| place != unwrap_arg_place) => Some(*target),
                _ => None,
            };
        }
    }

    let (unwrap_dest_place, post_unwrap_target, cond_op) = unwrap_place_info?;
    let post_unwrap_target = post_unwrap_target?;

    // Declares collection length/size invariant for unwrap place.
    let annotation_location = Location {
        block: post_unwrap_target,
        statement_index: 0,
    };
    invariants.insert((annotation_location, cond_op, unwrap_dest_place));

    // Returns analysis results.
    Some((invariants, (unwrap_dest_place, post_unwrap_target)))
}

/// Collects collection length/size bound invariants for variant downcast to `usize` places (if any)
/// for given variant.
fn collect_variant_target_invariants<'tcx>(
    place: Place<'tcx>,
    block: BasicBlock,
    variant_name: &str,
    variant_idx: VariantIdx,
    cond_op: CondOp,
    basic_blocks: &BasicBlocks<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> FxHashSet<Invariant<'tcx>> {
    let mut results = FxHashSet::default();

    // Collects given variant target blocks for switches based on the discriminant of return value
    // of slice `binary_search` in successor blocks.
    let targets = analyze::collect_switch_targets_for_discr_value(
        place,
        variant_idx.as_u32() as u128,
        block,
        basic_blocks,
    );
    for target_block in targets {
        collect_variant_target_invariants_inner(
            place,
            target_block,
            variant_name,
            variant_idx,
            cond_op,
            basic_blocks,
            tcx,
            &mut results,
        );
    }

    return results;

    // Declares collection length/size bound invariants for variant downcast to `usize` places (if any)
    // for the given switch target.
    #[allow(clippy::too_many_arguments)]
    fn collect_variant_target_invariants_inner<'tcx>(
        place: Place<'tcx>,
        block: BasicBlock,
        variant_name: &str,
        variant_idx: VariantIdx,
        cond_op: CondOp,
        basic_blocks: &BasicBlocks<'tcx>,
        tcx: TyCtxt<'tcx>,
        results: &mut FxHashSet<Invariant<'tcx>>,
    ) {
        let block_data = &basic_blocks[block];
        if block_data.statements.is_empty()
            && let Some(terminator) = &block_data.terminator
        {
            // Handles case of multiple match arms for a single variant.
            if let TerminatorKind::SwitchInt { discr, targets } = &terminator.kind
                && let Operand::Copy(op_place) | Operand::Move(op_place) = discr
                && analyze::is_variant_downcast_to_ty_place(
                    *op_place,
                    place,
                    variant_name,
                    variant_idx,
                    tcx.types.usize,
                )
            {
                for target_block in targets.all_targets() {
                    collect_variant_target_invariants_inner(
                        place,
                        *target_block,
                        variant_name,
                        variant_idx,
                        cond_op,
                        basic_blocks,
                        tcx,
                        results,
                    );
                }
                return;
            }
        }

        for (stmt_idx, stmt) in basic_blocks[block].statements.iter().enumerate() {
            // Finds variant downcast to `usize` places (if any) for the switch target variant.
            if let Some(downcast_place) = analyze::variant_downcast_to_ty_place(
                place,
                variant_name,
                variant_idx,
                tcx.types.usize,
                stmt,
            ) {
                // Declares a collection length/size bound invariant.
                let annotation_location = Location {
                    block,
                    statement_index: stmt_idx + 1,
                };
                results.insert((annotation_location, cond_op, downcast_place));
            }
        }
    }
}

// Propagates return place storage index invariant to callers.
fn propagate_storage_invariant<'tcx>(
    def_id: DefId,
    storage_id: StorageId,
    switch_target_info: Option<(Place<'tcx>, SwitchVariant)>,
    switch_target_info_alt: Option<(Place<'tcx>, SwitchVariant)>,
    unified_target_info: Option<Place<'tcx>>,
    tcx: TyCtxt<'tcx>,
) {
    let is_return_place =
        |place: Place| place.as_local().is_some_and(|local| local == RETURN_PLACE);

    // Composes propagated return place storage invariant environment (if necessary).
    let propagated_variant = match (
        switch_target_info,
        switch_target_info_alt,
        unified_target_info,
    ) {
        // Returns `Result::unwrap_or_else` with a identity closure or fn as input
        // (possibly after "safe" transformations).
        (_, _, Some(unwrap_place)) if is_return_place(unwrap_place) => PropagatedVariant::Union,
        // Returns `Result` (possibly after "safe" transformations).
        (
            Some((switch_target_place, switch_variant)),
            Some((switch_target_place_alt, switch_variant_alt)),
            _,
        ) if is_return_place(switch_target_place) && is_return_place(switch_target_place_alt) => {
            PropagatedVariant::Unknown(switch_variant, switch_variant_alt)
        }
        // Returns safe `Result::Ok` (possibly after "safe" transformations but only for the `Ok` variant).
        (Some((switch_target_place, switch_variant)), _, _)
            if is_return_place(switch_target_place) =>
        {
            PropagatedVariant::Primary(switch_variant)
        }
        // Returns safe `Result::Err` (possibly after "safe" transformations but only for the `Err` variant).
        (_, Some((switch_target_place_alt, switch_variant_alt)), _)
            if is_return_place(switch_target_place_alt) =>
        {
            PropagatedVariant::Alt(switch_variant_alt)
        }
        // Bails for all other cases.
        _ => return,
    };
    let storage_invariant_env = StorageInvariantEnv::new_with_id(
        def_id,
        storage_id,
        InvariantSource::SliceBinarySearch,
        propagated_variant,
        tcx,
    );

    // Sets propagated return place storage invariant environment.
    storage::set_invariant_env(&storage_invariant_env);
}
