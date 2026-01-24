//! `rustc` [`MirPass`] for adding annotations for "collection" invariants.

use rustc_middle::{
    mir::{
        BasicBlock, Body, HasLocalDecls, LocalDecls, Location, Operand, Place, Terminator,
        TerminatorKind, visit::Visitor,
    },
    ty::TyCtxt,
};
use rustc_span::source_map::Spanned;

use crate::providers::{
    analyze,
    annotate::{self, Annotation, CondOp},
    passes::MirPass,
};

/// Adds "collection" invariant annotations.
pub struct CollectionInvariants;

impl<'tcx> MirPass<'tcx> for CollectionInvariants {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // Generates "collection" annotations.
        let mut visitor = CollectionVisitor::new(body.local_decls(), tcx);
        visitor.visit_body(body);
        let annotations = visitor.annotations;

        // Adds "collection" annotations.
        if !annotations.is_empty() {
            annotate::add_annotations(annotations, body, tcx);
        }
    }
}

/// Collects "collection" annotations.
struct CollectionVisitor<'tcx, 'pass> {
    local_decls: &'pass LocalDecls<'tcx>,
    tcx: TyCtxt<'tcx>,
    /// A list of annotation declarations.
    annotations: Vec<Annotation<'tcx>>,
}

impl<'tcx, 'pass> CollectionVisitor<'tcx, 'pass> {
    fn new(local_decls: &'pass LocalDecls<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            local_decls,
            tcx,
            annotations: Vec::new(),
        }
    }

    /// Analyzes and annotates "collection" terminators.
    fn process_terminator(&mut self, terminator: &Terminator<'tcx>, _: Location) {
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
        let Some((def_id, _)) = func.const_fn_def() else {
            return;
        };

        // Handles calls to collection `len` methods.
        if self
            .tcx
            .opt_item_name(def_id)
            .is_some_and(|name| name.as_str() == "len")
            && args.len() == 1
        {
            self.process_len(args, destination, target.as_ref());
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
}

impl<'tcx> Visitor<'tcx> for CollectionVisitor<'tcx, '_> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.process_terminator(terminator, location);
        self.super_terminator(terminator, location);
    }
}
