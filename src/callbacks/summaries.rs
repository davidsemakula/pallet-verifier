//! `rustc` callbacks and utilities for dynamically generating specialized "summaries"
//! for calls that require knowledge of the calling context.
//!
//! See [`SummariesCallbacks`] doc.

use rustc_driver::Compilation;
use rustc_hash::FxHashSet;
use rustc_interface::interface::Compiler;
use rustc_middle::{
    mir::{visit::Visitor, LocalDecls, Location, Terminator, TerminatorKind},
    query,
    ty::{
        AliasTy, AssocItemContainer, GenericArgs, GenericArgsRef, Instance, Ty, TyCtxt, TyKind,
        TypingEnv,
    },
};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_type_ir::{
    ClosureArgs, ClosureArgsParts, CoroutineArgs, CoroutineArgsParts, CoroutineClosureArgs,
    CoroutineClosureArgsParts,
};

use owo_colors::OwoColorize;

use crate::{
    providers::{
        self,
        summaries::{self, SummaryTargetInfo},
    },
    utils, EntryPointsInfo,
};

/// `rustc` callbacks and utilities for dynamically generating specialized "summaries"
/// for calls that require knowledge of the calling context.
///
/// Ref: <https://github.com/endorlabs/MIRAI/blob/main/documentation/Overview.md#summaries>
pub struct SummariesCallbacks<'compilation> {
    entry_points: &'compilation EntryPointsInfo,
    // Specialized summaries.
    pub summaries: FxHashSet<String>,
}

impl<'compilation> SummariesCallbacks<'compilation> {
    pub fn new(entry_points: &'compilation EntryPointsInfo) -> Self {
        Self {
            entry_points,
            summaries: FxHashSet::default(),
        }
    }
}

impl rustc_driver::Callbacks for SummariesCallbacks<'_> {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        // Overrides `optimized_mir` query.
        config.override_queries = Some(|_, providers| {
            providers.queries = query::Providers {
                optimized_mir: providers::optimized_mir,
                ..providers.queries
            };
        });
    }

    fn after_analysis(&mut self, compiler: &Compiler, tcx: TyCtxt) -> Compilation {
        println!(
            "{} specialized summaries ...",
            "Generating".style(utils::highlight_style())
        );

        // Resolves and analyzes the generated entry points.
        let entry_points = utils::resolve_entry_points(self.entry_points, tcx, compiler.sess.dcx());
        for entry_point in entry_points {
            let body = tcx.optimized_mir(entry_point.def_id);
            let mut visitor = SummariesVisitor::new(
                entry_point.def_id,
                entry_point.def_id,
                None,
                &body.local_decls,
                body.typing_env(tcx),
                tcx,
            );
            visitor.visit_body(body);
            self.summaries.extend(visitor.summaries);
        }

        // Continue compilation.
        Compilation::Continue
    }
}

/// MIR visitor that collects specialized summaries.
pub struct SummariesVisitor<'tcx> {
    // `DefId` for root of typing environment (e.g. parent function for a closure).
    root_def_id: LocalDefId,
    // Generic args for root of typing environment.
    root_gen_args: Option<GenericArgsRef<'tcx>>,
    local_decls: &'tcx LocalDecls<'tcx>,
    typing_env: TypingEnv<'tcx>,
    tcx: TyCtxt<'tcx>,
    summary_targets: Option<SummaryTargetInfo>,
    // Specialized summaries.
    summaries: FxHashSet<String>,
}

impl<'tcx> SummariesVisitor<'tcx> {
    fn new(
        def_id: LocalDefId,
        root_def_id: LocalDefId,
        root_gen_args: Option<GenericArgsRef<'tcx>>,
        local_decls: &'tcx LocalDecls<'tcx>,
        typing_env: TypingEnv<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        let summary_targets = summaries::find_summary_targets(def_id.to_def_id(), tcx);
        Self {
            root_def_id,
            root_gen_args,
            local_decls,
            typing_env,
            tcx,
            summary_targets,
            summaries: FxHashSet::default(),
        }
    }

    /// Analyzes terminators.
    fn process_terminator(&mut self, terminator: &Terminator<'tcx>, _: Location) {
        let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
            return;
        };

        // Retrieves `fn` definition (if any).
        let Some((def_id, gen_args)) = func.const_fn_def() else {
            return;
        };

        // Composes specialized summaries.
        let call_def_hash = utils::def_hash_str(def_id, self.tcx);
        let gen_args_key = mirai::utils::argument_types_key_str(self.tcx, Some(gen_args));
        let call_key = (call_def_hash, gen_args_key.to_string());
        let is_summary_target = self
            .summary_targets
            .as_ref()
            .is_some_and(|summary_targets| summary_targets.contains(&call_key));

        let specialized_gen_args = if let Some(root_gen_args) = self.root_gen_args {
            specialize_args(
                def_id,
                self.root_def_id.to_def_id(),
                gen_args,
                root_gen_args,
                self.tcx,
            )
        } else {
            gen_args
        };
        if is_summary_target {
            let specialized_gen_args_key =
                mirai::utils::argument_types_key_str(self.tcx, Some(specialized_gen_args));
            let summary = format!("noop_result!(count{specialized_gen_args_key}, usize);");
            self.summaries.insert(summary);
        }

        // Visits body of local callee.
        let local_body_owner = self.resolve_local_instance(def_id, gen_args);
        let closures: Vec<_> = args
            .iter()
            .filter_map(|arg| {
                let ty = arg.node.ty(self.local_decls, self.tcx);
                match ty.kind() {
                    TyKind::Closure(def_id, _) => def_id.as_local(),
                    _ => None,
                }
            })
            .collect();

        if let Some((local_def_id, gen_args)) = local_body_owner {
            let specialized_gen_args = if let Some(root_gen_args) = self.root_gen_args {
                specialize_args(
                    local_def_id.to_def_id(),
                    self.root_def_id.to_def_id(),
                    gen_args,
                    root_gen_args,
                    self.tcx,
                )
            } else {
                gen_args
            };
            self.visit_local_body_owner(local_def_id, specialized_gen_args);
        }

        for local_def_id in closures {
            self.visit_local_body_owner(local_def_id, specialized_gen_args);
        }
    }

    /// Resolves local instance for given `DefId` (if any).
    fn resolve_local_instance(
        &self,
        def_id: DefId,
        gen_args: GenericArgsRef<'tcx>,
    ) -> Option<(LocalDefId, GenericArgsRef<'tcx>)> {
        // Resolves target instance for trait method calls.
        if let Some(assoc_item) = self.tcx.opt_associated_item(def_id) {
            if assoc_item.container == AssocItemContainer::Trait {
                let result = Instance::try_resolve(self.tcx, self.typing_env, def_id, gen_args);
                if let Ok(Some(instance)) = result {
                    return instance
                        .def_id()
                        .as_local()
                        .map(|local_def_id| (local_def_id, instance.args));
                }
            }
        }

        def_id
            .as_local()
            .map(|local_def_id| (local_def_id, gen_args))
    }

    /// Visits MIR body of given `LocalDefId`.
    fn visit_local_body_owner(&mut self, local_def_id: LocalDefId, gen_args: GenericArgsRef<'tcx>) {
        if !self.tcx.is_mir_available(local_def_id) {
            // Bails if definition has no MIR (e.g. trait assoc function declaration with no body).
            return;
        }
        let body = self.tcx.optimized_mir(local_def_id);
        let (root_def_id, root_gen_args, typing_env) =
            if self.tcx.is_closure_like(local_def_id.to_def_id()) {
                (self.root_def_id, self.root_gen_args, self.typing_env)
            } else {
                (local_def_id, Some(gen_args), body.typing_env(self.tcx))
            };
        let mut visitor = SummariesVisitor::new(
            local_def_id,
            root_def_id,
            root_gen_args,
            &body.local_decls,
            typing_env,
            self.tcx,
        );
        visitor.visit_body(body);
        self.summaries.extend(visitor.summaries);
    }
}

impl<'tcx> Visitor<'tcx> for SummariesVisitor<'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.process_terminator(terminator, location);
        self.super_terminator(terminator, location);
    }
}

/// Specializes type based on the root context.
fn specialize_ty<'tcx>(
    ty: Ty<'tcx>,
    root_def_id: DefId,
    root_args: GenericArgsRef<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Ty<'tcx> {
    match ty.kind() {
        TyKind::Param(param_ty) => {
            let generics = tcx.generics_of(root_def_id);
            let specialized_ty = generics
                .own_params
                .iter()
                .find(|param| param.name == param_ty.name)
                .or_else(|| {
                    generics
                        .parent
                        .as_ref()
                        .map(|impl_def_id| tcx.generics_of(impl_def_id))
                        .and_then(|impl_generics| {
                            impl_generics
                                .own_params
                                .iter()
                                .find(|param| param.name == param_ty.name)
                        })
                })
                .and_then(|param_def| generics.param_def_id_to_index(tcx, param_def.def_id))
                .and_then(|idx| root_args.get(idx as usize))
                .and_then(|arg| arg.as_type());
            if let Some(specialized_ty) = specialized_ty {
                return specialized_ty;
            }
        }
        TyKind::Adt(adt_def, adt_args) if requires_args_specialization(adt_args) => {
            let new_args = specialize_args(adt_def.did(), root_def_id, adt_args, root_args, tcx);
            return Ty::new_adt(tcx, *adt_def, new_args);
        }
        TyKind::Array(elem_ty, size) if requires_specialization(elem_ty) => {
            let new_elem_ty = specialize_ty(*elem_ty, root_def_id, root_args, tcx);
            return Ty::new_array_with_const_len(tcx, new_elem_ty, *size);
        }
        TyKind::Slice(elem_ty) if requires_specialization(elem_ty) => {
            let new_elem_ty = specialize_ty(*elem_ty, root_def_id, root_args, tcx);
            return Ty::new_slice(tcx, new_elem_ty);
        }
        TyKind::Tuple(tys) if requires_specialization(&ty) => {
            let new_tys = tcx.mk_type_list_from_iter(
                tys.iter()
                    .map(|elem_ty| specialize_ty(elem_ty, root_def_id, root_args, tcx)),
            );
            return Ty::new_tup(tcx, new_tys);
        }
        TyKind::Pat(pat_ty, pat) if requires_specialization(pat_ty) => {
            let new_pat_ty = specialize_ty(*pat_ty, root_def_id, root_args, tcx);
            return Ty::new_pat(tcx, new_pat_ty, *pat);
        }
        TyKind::Ref(region, ref_ty, mutability) if requires_specialization(ref_ty) => {
            let new_ref_ty = specialize_ty(*ref_ty, root_def_id, root_args, tcx);
            return Ty::new_ref(tcx, *region, new_ref_ty, *mutability);
        }
        TyKind::RawPtr(ptr_ty, mutability) if requires_specialization(ptr_ty) => {
            let new_ptr_ty = specialize_ty(*ptr_ty, root_def_id, root_args, tcx);
            return Ty::new_ptr(tcx, new_ptr_ty, *mutability);
        }
        TyKind::FnDef(def_id, args) if requires_args_specialization(args) => {
            let new_args = specialize_args(*def_id, root_def_id, args, root_args, tcx);
            return Ty::new_fn_def(tcx, *def_id, new_args);
        }
        TyKind::Closure(def_id, args) if requires_args_specialization(args) => {
            let closure_args = ClosureArgs::<TyCtxt> { args };
            let closure_args_parts = ClosureArgsParts::<TyCtxt> {
                parent_args: root_args,
                closure_kind_ty: specialize_ty(closure_args.kind_ty(), root_def_id, root_args, tcx),
                closure_sig_as_fn_ptr_ty: specialize_ty(
                    closure_args.sig_as_fn_ptr_ty(),
                    root_def_id,
                    root_args,
                    tcx,
                ),
                tupled_upvars_ty: specialize_ty(
                    closure_args.tupled_upvars_ty(),
                    root_def_id,
                    root_args,
                    tcx,
                ),
            };
            let new_closure_args = ClosureArgs::new(tcx, closure_args_parts);
            return Ty::new_closure(tcx, *def_id, new_closure_args.args);
        }
        TyKind::Alias(alias_kind, alias_ty) if requires_args_specialization(alias_ty.args) => {
            let new_args =
                specialize_args(alias_ty.def_id, root_def_id, alias_ty.args, root_args, tcx);
            let new_alias_ty = AliasTy::new(tcx, alias_ty.def_id, new_args);
            return Ty::new_alias(tcx, *alias_kind, new_alias_ty);
        }
        TyKind::Coroutine(def_id, gen_args) => {
            let coroutine_args = CoroutineArgs::<TyCtxt> { args: gen_args };
            let coroutine_args_parts = CoroutineArgsParts::<TyCtxt> {
                parent_args: root_args,
                kind_ty: specialize_ty(coroutine_args.kind_ty(), root_def_id, root_args, tcx),
                resume_ty: specialize_ty(coroutine_args.resume_ty(), root_def_id, root_args, tcx),
                yield_ty: specialize_ty(coroutine_args.yield_ty(), root_def_id, root_args, tcx),
                return_ty: specialize_ty(coroutine_args.return_ty(), root_def_id, root_args, tcx),
                witness: specialize_ty(coroutine_args.witness(), root_def_id, root_args, tcx),
                tupled_upvars_ty: specialize_ty(
                    coroutine_args.tupled_upvars_ty(),
                    root_def_id,
                    root_args,
                    tcx,
                ),
            };
            let new_coroutine_args = CoroutineArgs::new(tcx, coroutine_args_parts);
            return Ty::new_coroutine(tcx, *def_id, new_coroutine_args.args);
        }
        TyKind::CoroutineClosure(def_id, gen_args) => {
            let coroutine_args = CoroutineClosureArgs::<TyCtxt> { args: gen_args };
            let coroutine_args_parts = CoroutineClosureArgsParts::<TyCtxt> {
                parent_args: root_args,
                closure_kind_ty: specialize_ty(
                    coroutine_args.kind_ty(),
                    root_def_id,
                    root_args,
                    tcx,
                ),
                signature_parts_ty: specialize_ty(
                    coroutine_args.signature_parts_ty(),
                    root_def_id,
                    root_args,
                    tcx,
                ),
                tupled_upvars_ty: specialize_ty(
                    coroutine_args.tupled_upvars_ty(),
                    root_def_id,
                    root_args,
                    tcx,
                ),
                coroutine_captures_by_ref_ty: specialize_ty(
                    coroutine_args.coroutine_captures_by_ref_ty(),
                    root_def_id,
                    root_args,
                    tcx,
                ),
                coroutine_witness_ty: specialize_ty(
                    coroutine_args.coroutine_witness_ty(),
                    root_def_id,
                    root_args,
                    tcx,
                ),
            };
            let new_coroutine_args = CoroutineClosureArgs::new(tcx, coroutine_args_parts);
            return Ty::new_coroutine_closure(tcx, *def_id, new_coroutine_args.args);
        }
        TyKind::CoroutineWitness(def_id, args) if requires_args_specialization(args) => {
            let new_args = specialize_args(*def_id, root_def_id, args, root_args, tcx);
            return Ty::new_coroutine_witness(tcx, *def_id, new_args);
        }
        _ => (),
    }
    ty
}

/// Specializes generic args based on the root context.
fn specialize_args<'tcx>(
    def_id: DefId,
    root_def_id: DefId,
    args: GenericArgsRef<'tcx>,
    root_args: GenericArgsRef<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> GenericArgsRef<'tcx> {
    GenericArgs::for_item(tcx, def_id, |param, _| {
        let arg = args[param.index as usize];
        if let Some(ty) = arg.as_type() {
            return specialize_ty(ty, root_def_id, root_args, tcx).into();
        }
        arg
    })
}

/// Returns true if ty contains any type param or closure type.
///
/// **NOTE**: This function walks the whole type tree.
fn requires_specialization(ty: &Ty) -> bool {
    ty.walk().any(|arg| {
        arg.as_type().is_some_and(|ty| match ty.kind() {
            TyKind::Closure(_, _)
            | TyKind::Param(_)
            | TyKind::CoroutineClosure(_, _)
            | TyKind::Coroutine(_, _) => true,
            TyKind::Adt(_, args) => requires_args_specialization(args),
            TyKind::Array(ty, _)
            | TyKind::Pat(ty, _)
            | TyKind::Slice(ty)
            | TyKind::RawPtr(ty, _)
            | TyKind::Ref(_, ty, _) => requires_specialization(ty),
            TyKind::FnDef(_, args) | TyKind::CoroutineWitness(_, args) => {
                requires_args_specialization(args)
            }
            TyKind::FnPtr(binder, _) => binder
                .skip_binder()
                .inputs_and_output
                .iter()
                .any(|ty| requires_specialization(&ty)),
            TyKind::UnsafeBinder(unsafe_binder_inner) => {
                requires_specialization(&unsafe_binder_inner.skip_binder())
            }
            TyKind::Tuple(tys) => tys.iter().any(|ty| requires_specialization(&ty)),
            TyKind::Alias(_, alias_ty) => requires_args_specialization(alias_ty.args),
            _ => false,
        })
    })
}

/// Returns true if generic args contain any type param or closure type.
///
/// **NOTE**: This function walks the whole type tree.
fn requires_args_specialization(args: GenericArgsRef) -> bool {
    args.iter().any(|arg| {
        arg.as_type().is_some_and(|ty| {
            ty.walk().any(|arg| {
                arg.as_type()
                    .is_some_and(|ty| matches!(ty.kind(), TyKind::Closure(..) | TyKind::Param(..)))
            })
        })
    })
}
