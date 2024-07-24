//! `rustc` callbacks and utilities for generating tractable "entry points" for FRAME dispatchable functions.
//!
//! See [`EntryPointsCallbacks`] doc.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def::{DefKind, Res},
    intravisit::Visitor as _,
};
use rustc_middle::{
    mir::{
        visit::Visitor, AggregateKind, Body, HasLocalDecls, Local, LocalDecl, Location, Operand,
        Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::{AssocItemContainer, GenericArg, ImplSubject, Ty, TyCtxt, TyKind, Visibility},
};
use rustc_span::{
    def_id::{DefId, LocalDefId, LocalModDefId, CRATE_DEF_ID},
    BytePos, Pos, Span, Symbol,
};

use itertools::Itertools;

use super::utils;
use crate::ENTRY_POINT_FN_PREFIX;

/// `rustc` callbacks and utilities for generating tractable "entry points" for FRAME dispatchable functions.
///
/// Ref: <https://docs.rs/frame-support/latest/frame_support/pallet_macros/attr.call.html>
///
/// Ref: <https://github.com/facebookexperimental/MIRAI/blob/main/documentation/Overview.md#entry-points>
#[derive(Default)]
pub struct EntryPointsCallbacks {
    /// Map of generated entry point `fn` names and their definitions.
    entry_points: FxHashMap<String, String>,
    /// Use declarations and item definitions for generated entry points.
    use_decls: FxHashSet<String>,
    item_defs: FxHashSet<String>,
}

impl rustc_driver::Callbacks for EntryPointsCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        println!("Searching for dispatchable function declarations ...");
        let mut phase = Phase::Names;
        let mut entry_points = FxHashMap::default();
        let mut use_decls = FxHashSet::default();
        let mut item_defs = FxHashSet::default();

        queries.global_ctxt().unwrap().enter(|tcx| {
            // Find names and parent module of dispatchable functions.
            let Some((dispatchable_names, call_enum_local_def_id)) = dispatchable_calls_info(tcx)
            else {
                return;
            };
            let pallet_mod_local_def_id = tcx.parent_module_from_def_id(call_enum_local_def_id);

            // Finds `DefId`s of dispatchable functions.
            phase = Phase::DefIds;
            println!("Searching for dispatchable function definitions ...");
            let dispatchable_local_def_ids =
                dispatchable_ids(&dispatchable_names, pallet_mod_local_def_id, tcx);
            if dispatchable_local_def_ids.is_empty() {
                return;
            }

            // Adds warnings for `Call` variants whose dispatchable function wasn't found.
            if dispatchable_names.len() != dispatchable_local_def_ids.len() {
                let id_names: Vec<_> = dispatchable_local_def_ids
                    .iter()
                    .filter_map(|local_def_id| utils::def_name(*local_def_id, tcx))
                    .collect();
                for name in dispatchable_names {
                    let symbol = Symbol::intern(name);
                    if !id_names.contains(&symbol) {
                        let mut warning = compiler.sess.dcx().struct_warn(format!(
                            "Couldn't find definition for dispatchable: `{name}`"
                        ));
                        warning.note("This is most likely a bug in pallet-verifier.");
                        warning.help(
                            "Please consider filling a bug report at \
                            https://github.com/davidsemakula/pallet-verifier/issues",
                        );
                        warning.emit();
                    }
                }
            }

            // Finds dispatchable function calls.
            phase = Phase::Calls;
            println!("Searching for dispatchable function calls ...");
            let mut calls = FxHashMap::default();
            let hir = tcx.hir();
            let Some(pallet_struct_def_id) =
                dispatchable_local_def_ids.iter().find_map(|local_def_id| {
                    let (_, impl_) = impl_for_assoc_item(local_def_id.to_def_id(), tcx)?;
                    let adt_def_id = adt_for_impl(&impl_)?;
                    is_pallet_struct(adt_def_id, tcx).then_some(adt_def_id)
                })
            else {
                return;
            };
            for local_def_id in hir.body_owners() {
                let body_owner_kind = hir.body_owner_kind(local_def_id);
                if matches!(
                    body_owner_kind,
                    rustc_hir::BodyOwnerKind::Fn | rustc_hir::BodyOwnerKind::Closure
                ) {
                    let body = tcx.optimized_mir(local_def_id);
                    let mut visitor = PalletCallVisitor::new(pallet_struct_def_id, tcx);
                    visitor.visit_body(body);

                    for (callee_local_def_id, terminator) in visitor.calls {
                        calls.insert(callee_local_def_id, (terminator, body));
                    }
                }
            }
            if calls.is_empty() {
                return;
            }

            // Composes entry points module content and add warnings for missing dispatchable calls.
            println!("Generating tractable entry points for FRAME pallet ...");
            let mut used_items = FxHashSet::default();
            phase = Phase::EntryPoints;
            let Some(generics) = calls
                .iter()
                // Prefer generics from dispatchable function calls.
                .sorted_by_key(|(local_def_id, _)| {
                    if dispatchable_local_def_ids.contains(local_def_id) {
                        0
                    } else {
                        1
                    }
                })
                .find_map(|(local_def_id, (terminator, _))| {
                    if let TerminatorKind::Call { func, .. } = &terminator.kind {
                        let (_, fn_generic_args) = func.const_fn_def()?;
                        let ty_args: Vec<_> = fn_generic_args
                            .iter()
                            .filter_map(GenericArg::as_type)
                            .collect();

                        let assoc_item = tcx.opt_associated_item(local_def_id.to_def_id())?;
                        if assoc_item.container != AssocItemContainer::ImplContainer {
                            return None;
                        }
                        let impl_def_id = assoc_item.container_id(tcx);
                        let impl_local_def_id = impl_def_id.as_local()?;
                        let impl_generics = hir.get_generics(impl_local_def_id)?;
                        let config_param_name = Symbol::intern("T");
                        let config_param_local_def_id =
                            impl_generics.get_named(config_param_name)?.def_id;
                        let config_trait_local_def_id = impl_generics
                            .bounds_for_param(config_param_local_def_id)
                            .find_map(|bound_info| {
                                bound_info.bounds.iter().find_map(|bound| {
                                    let trait_ref = bound.trait_ref()?;
                                    if let Res::Def(DefKind::Trait, trait_def_id) =
                                        trait_ref.path.res
                                    {
                                        let trait_local_def_id = trait_def_id.as_local()?;
                                        let trait_name = utils::def_name(trait_local_def_id, tcx)?;
                                        return (trait_name.as_str() == "Config")
                                            .then_some(trait_local_def_id);
                                    }
                                    None
                                })
                            })?;

                        let ty_params: Vec<_> = impl_generics
                            .params
                            .iter()
                            .filter(|param| {
                                matches!(param.kind, rustc_hir::GenericParamKind::Type { .. })
                            })
                            .collect();
                        let mut ty_param_impls = FxHashMap::default();
                        if ty_params.len() == ty_args.len() {
                            for (idx, param) in ty_params.iter().enumerate() {
                                let param_name = param.name.ident().name;
                                let arg_ty = ty_args
                                    .get(idx)
                                    .expect("Expected a generic arg at index {idx}");
                                ty_param_impls.insert(param_name, *arg_ty);
                            }
                        }

                        Some(Generics::new(
                            config_trait_local_def_id,
                            ty_args,
                            ty_param_impls,
                        ))
                    } else {
                        None
                    }
                })
            else {
                return;
            };
            for local_def_id in dispatchable_local_def_ids {
                let call_info = calls
                    .get(&local_def_id)
                    .map(|(terminator, body)| (terminator, *body));
                let entry_point_result =
                    compose_entry_point(local_def_id, tcx, &generics, call_info);
                if let Some((name, content, local_used_items)) = entry_point_result {
                    entry_points.insert(name, content);
                    used_items.extend(local_used_items);
                } else {
                    let name = utils::def_name(local_def_id, tcx)
                        .expect("Expected a name for dispatchable");
                    let (msg, note, help) = if call_info.is_some() {
                        ("Failed to generate tractable entry point", None, None)
                    } else {
                        (
                            "Couldn't find a call",
                            Some(format!(
                                "pallet-verifier couldn't find a unit test for: `{name}`."
                            )),
                            Some(format!("Add a unit test that calls: `{name}`.")),
                        )
                    };
                    let mut warning = compiler
                        .sess
                        .dcx()
                        .struct_warn(format!("{msg} for dispatchable: `{name}`"));
                    if let Some(note) = note {
                        warning.note(note);
                    }
                    if let Some(help) = help {
                        warning.help(help);
                    }
                    warning.emit();
                }
            }
            if entry_points.is_empty() {
                return;
            }

            // Collects use declarations or copies/re-defines used items.
            process_used_items(used_items, &mut use_decls, &mut item_defs, tcx);
        });

        if entry_points.is_empty() {
            // Stops compilation if we fail to generate any tractable entry points.
            // Sets error message based on the analysis phase reached.
            let (msg, note, help) = match phase {
                Phase::Names => (
                    "Couldn't find any dispatchable functions in public interface",
                    Some("pallet-verifier can only analyze FRAME pallets"),
                    Some("Learn more at https://github.com/davidsemakula/pallet-verifier"),
                ),
                Phase::DefIds => (
                    "Failed to find definitions for any dispatchable function \
                    in public interface",
                    Some("This is most likely a bug in pallet-verifier."),
                    Some(
                        "Please consider filling a bug report at \
                        https://github.com/davidsemakula/pallet-verifier/issues",
                    ),
                ),
                _ => (
                    "Failed to generate tractable entry points for any dispatchable function \
                    in public interface",
                    None,
                    Some("Add some unit tests for all dispatchable functions."),
                ),
            };
            let mut error = compiler.sess.dcx().struct_err(msg);
            if let Some(note) = note {
                error.note(note);
            }
            if let Some(help) = help {
                error.help(help);
            }
            error.emit();
            rustc_driver::Compilation::Stop
        } else {
            // Sets entry point content and continue compilation.
            self.entry_points = entry_points;
            self.use_decls = use_decls;
            self.item_defs = item_defs;
            rustc_driver::Compilation::Continue
        }
    }
}

impl EntryPointsCallbacks {
    /// Returns module content for all generated tractable entry points (if any).
    pub fn entry_points_content(&self) -> Option<String> {
        (!self.entry_points.is_empty()).then(|| {
            let use_decls = self.use_decls.iter().join("\n");
            let item_defs = self.item_defs.iter().join("\n");
            let entry_points = self.entry_points.values().join("\n\n");
            format!(
                r"
#![allow(unused)]
#![allow(nonstandard_style)]
#![allow(private_interfaces)]

{use_decls}

{item_defs}

{entry_points}"
            )
        })
    }

    /// Returns `fn` names of all generated tractable entry points.
    pub fn entry_point_names(&self) -> FxHashSet<&str> {
        self.entry_points.keys().map(String::as_str).collect()
    }
}

/// The analysis phase.
enum Phase {
    /// Finding dispatchable names.
    Names,
    /// Finding dispatchable `DefId`s.
    DefIds,
    /// Finding a call for each dispatchable.
    Calls,
    /// Composing entry points for dispatchables with calls.
    EntryPoints,
}

/// Generic info for specializing entry points.
struct Generics<'tcx> {
    config_trait_local_def_id: LocalDefId,
    ty_args: Vec<Ty<'tcx>>,
    ty_param_impls: FxHashMap<Symbol, Ty<'tcx>>,
}

impl<'tcx> Generics<'tcx> {
    /// Create a new instance of generics info.
    pub fn new(
        config_trait_local_def_id: LocalDefId,
        ty_args: Vec<Ty<'tcx>>,
        ty_param_impls: FxHashMap<Symbol, Ty<'tcx>>,
    ) -> Self {
        Self {
            config_trait_local_def_id,
            ty_args,
            ty_param_impls,
        }
    }

    /// Creates turbofish arguments from generics info.
    pub fn turbofish_args(&self, used_items: &mut FxHashSet<DefId>, tcx: TyCtxt<'_>) -> String {
        format!(
            "::<{}>",
            self.ty_args
                .iter()
                .map(|ty| {
                    tractable_param_type(ty, used_items, tcx)
                        .expect("Expected tractable generic args")
                })
                .join(", ")
        )
    }
}

/// Finds names of dispatchable functions, also returns the `DefId` of the `Call` enum.
///
/// Dispatchable functions are represented as variants of an enum `Call<T: Config>`
/// with attributes `#[codec(index: u8 = ..)]`.
/// Notably, there's a "phantom" variant `__Ignore` which should be, well, ignored :)
fn dispatchable_calls_info(tcx: TyCtxt<'_>) -> Option<(FxHashSet<&str>, LocalDefId)> {
    let mut results = FxHashSet::default();
    let mut enum_def_id = None;
    let hir = tcx.hir();
    let mut call_enums: Vec<_> = hir
        .items()
        .filter_map(|item_id| {
            let item = hir.item(item_id);
            if item.ident.as_str() == "Call" {
                if let rustc_hir::ItemKind::Enum(enum_def, enum_generics) = item.kind {
                    if let Some(enum_local_def_id) = item_id.owner_id.to_def_id().as_local() {
                        if is_config_bounded(enum_generics, tcx) {
                            let parent_mod_def_id =
                                tcx.parent_module_from_def_id(enum_local_def_id).to_def_id();
                            return is_visible_from_crate_root(parent_mod_def_id, tcx)
                                .then_some((enum_local_def_id, enum_def));
                        }
                    }
                }
            }
            None
        })
        .collect();
    let n_call_enums = call_enums.len();
    if n_call_enums > 0 {
        if n_call_enums > 1 {
            // Picks `Call` enum with a definition "closest" to the crate root.
            call_enums
                .sort_by_key(|(local_def_id, _)| tcx.def_path(local_def_id.to_def_id()).data.len());
        }
        let (local_def_id, enum_def) = call_enums.first().expect("Expected one `Call` enum");
        enum_def_id = Some(*local_def_id);
        for variant in enum_def.variants {
            let name = variant.ident.as_str();
            if !name.starts_with("__") {
                results.insert(name);
            }
        }
    }
    (!results.is_empty()).then_some(results).zip(enum_def_id)
}

/// Finds definitions of dispatchable functions.
///
/// Dispatchable function definitions are associated `fn`s of
/// a non-trait `impl<T: Config, *> Pallet<T>`, where `Pallet` is a `struct`,
/// and the name of the `fn` is a variant of the `Call<T: Config, *>` enum.
fn dispatchable_ids(
    names: &FxHashSet<&str>,
    pallet_mod_local_def_id: LocalModDefId,
    tcx: TyCtxt<'_>,
) -> FxHashSet<LocalDefId> {
    let hir = tcx.hir();
    hir.body_owners()
        .filter_map(|local_def_id| {
            let body_owner_kind = hir.body_owner_kind(local_def_id);
            if !matches!(body_owner_kind, rustc_hir::BodyOwnerKind::Fn) {
                return None;
            }
            let fn_name = utils::def_name(local_def_id, tcx)?;
            if !names.contains(&fn_name.as_str()) {
                return None;
            }
            let parent_mod_local_def_id = tcx.parent_module_from_def_id(local_def_id);
            if parent_mod_local_def_id != pallet_mod_local_def_id {
                return None;
            }
            let def_id = local_def_id.to_def_id();
            let (_, impl_) = impl_for_assoc_item(def_id, tcx)?;
            let adt_def_id = adt_for_impl(&impl_)?;
            (impl_.of_trait.is_none()
                && is_config_bounded(impl_.generics, tcx)
                && is_pallet_struct(adt_def_id, tcx))
            .then_some(local_def_id)
        })
        .collect()
}

// Verifies that the definition is a local `struct` named `Pallet`.
fn is_pallet_struct(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    tcx.def_kind(def_id) == DefKind::Struct
        && def_id.as_local().is_some_and(|local_def_id| {
            return utils::def_name(local_def_id, tcx)
                .is_some_and(|name| name.as_str() == "Pallet");
        })
}

/// Verifies that the generics include a `<T: Config>` bound.
fn is_config_bounded(generics: &rustc_hir::Generics, tcx: TyCtxt<'_>) -> bool {
    let param_name = Symbol::intern("T");
    generics.get_named(param_name).is_some_and(|param| {
        generics.bounds_for_param(param.def_id).any(|bound_info| {
            bound_info.bounds.iter().any(|bound| {
                bound.trait_ref().is_some_and(|trait_ref| {
                    if let Res::Def(DefKind::Trait, trait_def_id) = trait_ref.path.res {
                        return trait_def_id.as_local().is_some_and(|trait_local_def_id| {
                            utils::def_name(trait_local_def_id, tcx)
                                .is_some_and(|trait_name| trait_name.as_str() == "Config")
                        });
                    }
                    false
                })
            })
        })
    })
}

/// Composes an entry point (returns a `name`, `content` and "used item" `DefId`s).
///
/// NOTE: This function assumes the terminator wraps a call to a dispatchable function, but doesn't verify it.
fn compose_entry_point<'tcx>(
    fn_local_def_id: LocalDefId,
    tcx: TyCtxt<'tcx>,
    generics: &Generics,
    call_info: Option<(&Terminator<'tcx>, &Body<'tcx>)>,
) -> Option<(String, String, FxHashSet<DefId>)> {
    // Dispatchable name.
    let fn_name = utils::def_name(fn_local_def_id, tcx)?;

    // owner body (if any), call args (if any) and call span (if any).
    let mut owner_body_opt = None;
    let mut call_args_opt = None;
    let mut fn_span_opt = None;
    if let Some((
        TerminatorKind::Call {
            func,
            args,
            fn_span,
            ..
        },
        body,
    )) = call_info.map(|(terminator, body)| (&terminator.kind, body))
    {
        let (fn_def_id, _) = func.const_fn_def()?;
        if fn_def_id != fn_local_def_id.to_def_id() {
            return None;
        }
        owner_body_opt = Some(body);
        call_args_opt = Some(args);
        fn_span_opt = Some(fn_span);
    }

    // Item imports and definitions.
    let mut used_items = FxHashSet::default();
    let mut item_defs = FxHashSet::default();

    // Compose entry point params, and corresponding dispatchable call args.
    let mut params = Vec::new();
    let mut args = Vec::new();
    let mut locals = FxHashSet::default();
    let hir_id = tcx.local_def_id_to_hir_id(fn_local_def_id);
    let hir = tcx.hir();
    let hir_body_id = hir.body_owned_by(fn_local_def_id);
    let hir_body = hir.body(hir_body_id);
    let fn_params = hir_body.params;
    let fn_decl = hir.fn_decl_by_hir_id(hir_id)?;
    let fn_params_ty = fn_decl.inputs;
    let source_map = tcx.sess.source_map();
    let local_decls_opt = owner_body_opt.map(|owner_body| owner_body.local_decls());
    for (idx, fn_param) in fn_params.iter().enumerate() {
        // Creates a unique param name.
        let pat = fn_param.pat;
        let param_name = source_map
            .span_to_snippet(pat.span)
            .expect("Expected snippet for span");
        let unique_name = format!("{param_name}__{fn_name}");

        // Composes entry point param and/or dispatchable call arg.
        let param_ty = fn_params_ty.get(idx).expect("Expected param type");
        let specialized_user_ty =
            tractable_param_hir_type(fn_param, param_ty, generics, &mut used_items, tcx);
        if let Some(specialized_user_ty) = specialized_user_ty {
            // Composes entry point param, and corresponding dispatchable call arg vars,
            // by replacing `T: Config` param types with concrete `Config` type,
            // and integer const generic params with an arbitrary large value.
            params.push(format!("{unique_name}: {specialized_user_ty}"));
            args.push(unique_name);
        } else {
            // Composes entry point param and/or dispatchable call args based on
            // dispatchable call arg type or value.
            let Some(call_args) = call_args_opt else {
                // Bails if call args aren't available.
                return None;
            };
            let call_arg = call_args
                .get(idx)
                .expect("Expected dipatchable call argument: {param_name}");
            match &call_arg.node {
                Operand::Copy(place) | Operand::Move(place) => {
                    // Adds entry point param and/or dispatchable call arg.
                    let local_decl = local_decls_opt
                        .and_then(|local_decls| local_decls.get(place.local))
                        .expect("Expected local declaration");
                    let arg_ty = local_decl.ty;
                    if let Some(arg_ty_str) = tractable_param_type(&arg_ty, &mut used_items, tcx) {
                        // Adds entry point param and dispatchable call arg var,
                        // based on dispatchable call arg type.
                        params.push(format!("{unique_name}: {arg_ty_str}"));
                        args.push(unique_name);
                    } else {
                        // Adds dispatchable call arg value based on user input.
                        let mut span = call_arg.span;
                        if span.from_expansion() {
                            // Adds macro `DefId` to used items.
                            if let Some(macro_def_id) = span.ctxt().outer_expn_data().macro_def_id {
                                used_items.insert(macro_def_id);
                            }
                            // Uses the call site span for macro expansions.
                            span = span.source_callsite();
                            // Collects used items for type.
                            process_type(&arg_ty, &mut used_items);
                        } else {
                            // Collects used local and item definitions, and item imports for arguments.
                            process_operand(
                                &call_arg.node,
                                &mut locals,
                                &mut used_items,
                                &mut item_defs,
                            );
                        }
                        let value = source_map
                            .span_to_snippet(span)
                            .expect("Expected snippet for span");
                        args.push(value);
                    }
                }
                Operand::Constant(constant) => {
                    // Collects used local and item definitions, and item imports for arguments.
                    process_operand(&call_arg.node, &mut locals, &mut used_items, &mut item_defs);

                    // Adds entry point param and/or dispatchable call arg.
                    let arg_ty = constant.ty();
                    if let Some(arg_ty_str) = tractable_param_type(&arg_ty, &mut used_items, tcx) {
                        // Adds entry point param and dispatchable call arg var,
                        // based on dispatchable call arg type.
                        params.push(format!("{unique_name}: {arg_ty_str}"));
                        args.push(unique_name);
                    } else {
                        // Adds dispatchable call arg value based on user input.
                        let value = source_map
                            .span_to_snippet(call_arg.span)
                            .expect("Expected snippet for span");
                        args.push(value);
                    }
                }
            }
        }
    }

    // Collects used local and item definitions, and item imports.
    let mut stmts = FxHashSet::default();
    let mut call_spans = Vec::new();
    if let Some(fn_span) = fn_span_opt {
        call_spans.push(*fn_span);
    }
    while !locals.is_empty() {
        // Adds `let` assignments for locals to statements.
        stmts.extend(locals.iter().filter_map(|local| {
            let local_decl = local_decls_opt.and_then(|local_decls| local_decls.get(*local))?;
            let span = local_decl.source_info.span.source_callsite();
            let is_in_call = call_spans.iter().any(|sp| sp.contains(span));
            if !is_in_call {
                let_statement_for_local(local_decl, tcx)
            } else {
                None
            }
        }));

        // Collects used local and item definitions, and item imports for current locals.
        let mut visitor = ValueVisitor::new(&locals);
        if let Some(owner_body) = owner_body_opt {
            visitor.visit_body(owner_body);
        }

        // Updates used item definitions and imports.
        item_defs.extend(visitor.item_defs);
        used_items.extend(visitor.used_items);

        // Tracks child locals for next iteration.
        let mut next_locals = FxHashSet::default();
        next_locals.extend(visitor.next_locals);

        // Processes function and method calls.
        for call in visitor.calls {
            let TerminatorKind::Call { fn_span, .. } = &call.kind else {
                continue;
            };
            call_spans.push(*fn_span);

            process_call(
                &call,
                &mut next_locals,
                &mut used_items,
                &mut item_defs,
                tcx,
            );
        }

        // Process child locals in next iteration.
        locals = next_locals;
    }

    // Collects used item definitions and imports for closures and coroutines.
    //
    // NOTE: We don't collect locals because captured locals are already handled as locals
    // for the parent function above, while non-captured locals (i.e. locals defined inside the closure)
    // are already defined in the closure's `let` statement above.
    let mut closures: FxHashSet<_> = used_items
        .iter()
        .filter(|item_id| tcx.is_closure_or_coroutine(**item_id))
        .cloned()
        .collect();
    while !closures.is_empty() {
        // Tracks child closures/coroutines for next iteration.
        let mut next_closures = FxHashSet::default();

        for closure_id in closures.drain() {
            // Collects used item definitions and imports for closure.
            let closure_body = tcx.optimized_mir(closure_id);
            let mut visitor = ClosureVisitor::new();
            visitor.visit_body(closure_body);

            // Collects child closures for next iteration of outer while loop.
            next_closures.extend(
                visitor
                    .used_items
                    .iter()
                    .filter(|item_id| tcx.is_closure_or_coroutine(**item_id)),
            );

            // Updates used item definitions and imports.
            item_defs.extend(visitor.item_defs);
            used_items.extend(visitor.used_items);

            // Processes function and method calls.
            for call in visitor.calls {
                process_call(
                    &call,
                    // We don't need to process locals for closures.
                    // See doc at `closures` definition above.
                    &mut FxHashSet::default(),
                    &mut used_items,
                    &mut item_defs,
                    tcx,
                );
            }
        }

        // Process child closures in next iteration.
        closures = next_closures;
    }

    // Adds item definitions to statements.
    for item_id in item_defs {
        let item_local_id = item_id.as_local().expect("Expected local declaration");
        let item_kind = tcx.def_kind(item_local_id);
        if matches!(item_kind, DefKind::Const | DefKind::Closure) {
            // Uses `TyCtxt::source_span` to get the full span, not just the header.
            let span = tcx.source_span(item_local_id);
            let snippet = source_map
                .span_to_snippet(span)
                .expect("Expected snippet for span");
            stmts.insert((snippet, span));
        }
    }

    // Composes entry point.
    let name = format!("{ENTRY_POINT_FN_PREFIX}{fn_name}");
    let params_list = params.join(", ");
    let args_list = args.join(", ");
    let assign_decls = stmts
        .into_iter()
        .sorted_by_key(|(_, span)| *span)
        .map(|(snippet, _)| snippet)
        .join("\n    ");
    let pallet_mod = tcx.parent_module_from_def_id(fn_local_def_id);
    let pallet_mod_path = tcx.def_path_str(pallet_mod);
    let generic_args = generics.turbofish_args(&mut used_items, tcx);
    let content = format!(
        r"
pub fn {name}({params_list}) {{
    {assign_decls}

    crate::{}{}Pallet{generic_args}::{fn_name}({args_list});
}}",
        pallet_mod_path,
        if pallet_mod_path.is_empty() { "" } else { "::" }
    );
    Some((name, content, used_items))
}

/// Collects use declarations or copies/re-defines used items depending on item kind, source,
/// visibility, stability and enabled features.
///
/// NOTE: Ignores items that aren't importable and/or depend on unstable features that aren't enabled.
fn process_used_items(
    used_items: FxHashSet<DefId>,
    use_decls: &mut FxHashSet<String>,
    item_defs: &mut FxHashSet<String>,
    tcx: TyCtxt<'_>,
) {
    let hir = tcx.hir();
    let source_map = tcx.sess.source_map();
    let mut processed_items = FxHashSet::default();
    let mut aliased_used_items: FxHashSet<(DefId, Option<Symbol>)> = used_items
        .into_iter()
        .map(|def_id| (def_id, None))
        .collect();
    while !aliased_used_items.is_empty() {
        // Tracks child used items for next iteration.
        let mut next_used_items = FxHashSet::default();
        for (item_def_id, item_alias) in aliased_used_items.drain() {
            processed_items.insert(item_def_id);
            let item_kind = tcx.def_kind(item_def_id);
            let is_importable = matches!(
                item_kind,
                DefKind::Mod
                    | DefKind::Const
                    | DefKind::Fn
                    | DefKind::Struct
                    | DefKind::Enum
                    | DefKind::Union
                    | DefKind::Trait
                    | DefKind::TraitAlias
                    | DefKind::TyAlias
                    | DefKind::Macro(_)
                    | DefKind::ForeignTy
            );
            let is_stable_or_enabled = matches!(
                tcx.eval_stability(item_def_id, None, rustc_span::DUMMY_SP, None),
                rustc_middle::middle::stability::EvalResult::Allow
            );
            if is_importable && is_stable_or_enabled {
                if !item_def_id.is_local() || is_visible_from_crate_root(item_def_id, tcx) {
                    // Add use declaration for foreign items, and local items that are visible from the crate root.
                    use_decls.insert(format!(
                        "use {}{}{};",
                        if item_def_id.is_local() {
                            "crate::"
                        } else {
                            ""
                        },
                        tcx.def_path_str(item_def_id),
                        if let Some(item_alias) = item_alias {
                            format!(" as {item_alias}")
                        } else {
                            String::new()
                        }
                    ));
                } else {
                    // Copy/re-define local items that aren't visible from the crate root.
                    let item_local_def_id = item_def_id.as_local().expect("Expected local item");
                    let span = tcx.source_span(item_local_def_id);
                    let mut source = source_map
                        .span_to_snippet(span)
                        .expect("Expected snippet for local item");

                    // Collects child used items.
                    let node = tcx.hir_node_by_def_id(item_local_def_id);
                    if let rustc_hir::Node::Item(item) = node {
                        match &item.kind {
                            rustc_hir::ItemKind::Const(ty, generics, _)
                            | rustc_hir::ItemKind::TyAlias(ty, generics) => {
                                process_hir_ty(ty, &mut next_used_items, tcx);
                                process_generics(generics, &mut next_used_items, tcx);
                            }
                            rustc_hir::ItemKind::Fn(fn_sig, generics, _) => {
                                process_fn_sig(fn_sig, &mut next_used_items, tcx);
                                process_generics(generics, &mut next_used_items, tcx);
                            }
                            rustc_hir::ItemKind::Enum(enum_def, generics) => {
                                for variant in enum_def.variants {
                                    process_variants(&variant.data, &mut next_used_items, tcx);
                                }
                                process_generics(generics, &mut next_used_items, tcx);
                            }
                            rustc_hir::ItemKind::Struct(variants, generics)
                            | rustc_hir::ItemKind::Union(variants, generics) => {
                                process_variants(variants, &mut next_used_items, tcx);
                                process_generics(generics, &mut next_used_items, tcx);
                            }
                            rustc_hir::ItemKind::Trait(_, _, generics, bounds, assoc_items) => {
                                for assoc_item_ref in *assoc_items {
                                    let assoc_item = hir.trait_item(assoc_item_ref.id);
                                    match &assoc_item.kind {
                                        rustc_hir::TraitItemKind::Const(ty, _) => {
                                            process_hir_ty(ty, &mut next_used_items, tcx);
                                        }
                                        rustc_hir::TraitItemKind::Fn(fn_sig, _) => {
                                            process_fn_sig(fn_sig, &mut next_used_items, tcx);
                                        }
                                        rustc_hir::TraitItemKind::Type(bounds, ty) => {
                                            for bound in *bounds {
                                                process_generic_bound(bound, &mut next_used_items);
                                            }
                                            if let Some(ty) = ty {
                                                process_hir_ty(ty, &mut next_used_items, tcx);
                                            }
                                        }
                                    }
                                }
                                process_generics(generics, &mut next_used_items, tcx);
                                for bound in *bounds {
                                    process_generic_bound(bound, &mut next_used_items);
                                }
                            }
                            rustc_hir::ItemKind::TraitAlias(generics, bounds) => {
                                process_generics(generics, &mut next_used_items, tcx);
                                for bound in *bounds {
                                    process_generic_bound(bound, &mut next_used_items);
                                }
                            }
                            _ => (),
                        }

                        // Adds `impl`s source snippets for ADT item, and collects child used items for impls.
                        if matches!(item_kind, DefKind::Struct | DefKind::Enum | DefKind::Union) {
                            let mut impls = FxHashSet::default();
                            let adt_impl = |item_id: rustc_hir::ItemId| {
                                let item = hir.item(item_id);
                                let rustc_hir::ItemKind::Impl(impl_item) = item.kind else {
                                    return None;
                                };
                                let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) =
                                    impl_item.self_ty.kind
                                else {
                                    return None;
                                };
                                let Res::Def(
                                    DefKind::Struct | DefKind::Enum | DefKind::Union,
                                    adt_def_id,
                                ) = path.res
                                else {
                                    return None;
                                };
                                (adt_def_id == item_def_id).then_some((impl_item, item.span))
                            };
                            for (impl_item, span) in hir.items().filter_map(adt_impl) {
                                // Collects child used items for `impl`.
                                process_impl(impl_item, &mut next_used_items, tcx);

                                // Adds `impl` snippet.
                                let impl_source = source_map
                                    .span_to_snippet(span)
                                    .expect("Expected snippet for local item");
                                impls.insert(impl_source);
                            }

                            // Adds `impl`s to ADT source.
                            let impls_source = impls.iter().join("\n\n");
                            source = format!("{source}\n\n{impls_source}");
                        }

                        // Adds item source snippet.
                        item_defs.insert(source);
                    }
                }
            } else if matches!(
                item_kind,
                DefKind::AssocTy | DefKind::AssocFn | DefKind::AssocConst
            ) {
                if let Some(trait_def_id) = tcx
                    .opt_associated_item(item_def_id)
                    .and_then(|assoc_item| assoc_item.trait_container(tcx))
                {
                    next_used_items.insert((trait_def_id, None));
                }
            }
        }

        // Process child used items in next iteration.
        aliased_used_items = next_used_items
            .into_iter()
            .filter(|(item_id, _)| !processed_items.contains(item_id))
            .collect();
    }

    /// Collects used items for HIR type.
    fn process_hir_ty<'tcx>(
        ty: &'tcx rustc_hir::Ty<'tcx>,
        used_items: &mut FxHashSet<(DefId, Option<Symbol>)>,
        tcx: TyCtxt<'tcx>,
    ) {
        let mut visitor = TyVisitor::new(tcx);
        visitor.visit_ty(ty);

        for gen_ty in visitor.types {
            if let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) = gen_ty.kind {
                match path.res {
                    Res::Def(def_kind, def_id) => {
                        if matches!(
                            def_kind,
                            DefKind::AssocTy | DefKind::AssocFn | DefKind::AssocConst
                        ) {
                            if let Some(trait_def_id) = tcx
                                .opt_associated_item(def_id)
                                .and_then(|assoc_item| assoc_item.trait_container(tcx))
                            {
                                if let Some((trait_segments, _)) =
                                    path.segments.split_last_chunk::<1>()
                                {
                                    let user_trait_path = trait_segments
                                        .iter()
                                        .map(|segment| segment.ident)
                                        .join("::");
                                    let trait_def_path = tcx.def_path_str(trait_def_id);
                                    if user_trait_path == trait_def_path {
                                        // Ignore fully-qualified trait paths.
                                        continue;
                                    }

                                    let trait_user_name =
                                        trait_segments.last().map(|segment| segment.ident.name);
                                    let trait_def_name = trait_def_path.split("::").last();
                                    if let Some((alias, _)) = trait_user_name
                                        .zip(trait_def_name)
                                        .filter(|(user_name, name)| user_name.as_str() != *name)
                                    {
                                        // Add trait along with it's alias.
                                        used_items.insert((trait_def_id, Some(alias)));
                                        continue;
                                    }
                                }
                            }
                        }

                        if matches!(
                            def_kind,
                            DefKind::Struct | DefKind::Enum | DefKind::Union | DefKind::Trait
                        ) {
                            let user_adt_path =
                                path.segments.iter().map(|segment| segment.ident).join("::");
                            let adt_def_path = tcx.def_path_str(def_id);
                            if user_adt_path == adt_def_path {
                                // Ignore fully-qualified ADT paths.
                                continue;
                            }

                            let adt_user_name =
                                path.segments.last().map(|segment| segment.ident.name);
                            let adt_def_name = adt_def_path.split("::").last();

                            if let Some((alias, _)) = adt_user_name
                                .zip(adt_def_name)
                                .filter(|(user_name, name)| user_name.as_str() != *name)
                            {
                                // Add ADT along with it's alias.
                                used_items.insert((def_id, Some(alias)));
                                continue;
                            }
                        }
                        used_items.insert((def_id, None));
                    }
                    Res::SelfTyParam { trait_: def_id }
                    | Res::SelfTyAlias {
                        alias_to: def_id, ..
                    }
                    | Res::SelfCtor(def_id) => {
                        used_items.insert((def_id, None));
                    }
                    _ => (),
                };
            }
        }
        for anon_const in visitor.anon_consts {
            let const_expr = tcx.hir().body(anon_const.body).value;
            if let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = const_expr.kind
            {
                if let Res::Def(DefKind::Const, const_def_id) = path.res {
                    used_items.insert((const_def_id, None));
                }
            }
        }
    }

    /// Collects child used items in `fn` signature.
    fn process_fn_sig<'tcx>(
        sig: &'tcx rustc_hir::FnSig,
        used_items: &mut FxHashSet<(DefId, Option<Symbol>)>,
        tcx: TyCtxt<'tcx>,
    ) {
        let fn_decl = sig.decl;
        for param_ty in fn_decl.inputs {
            process_hir_ty(param_ty, used_items, tcx);
        }
        if let rustc_hir::FnRetTy::Return(return_ty) = fn_decl.output {
            process_hir_ty(return_ty, used_items, tcx);
        };
    }

    /// Collects child used items for ADT variants.
    fn process_variants<'tcx>(
        variants: &'tcx rustc_hir::VariantData,
        used_items: &mut FxHashSet<(DefId, Option<Symbol>)>,
        tcx: TyCtxt<'tcx>,
    ) {
        if let rustc_hir::VariantData::Tuple(_, _, variant_def_id)
        | rustc_hir::VariantData::Unit(_, variant_def_id) = variants
        {
            used_items.insert((variant_def_id.to_def_id(), None));
        }
        for field in variants.fields() {
            process_hir_ty(field.ty, used_items, tcx);
        }
    }

    /// Collects child used items for `impl`.
    fn process_impl<'tcx>(
        impl_item: &'tcx rustc_hir::Impl,
        used_items: &mut FxHashSet<(DefId, Option<Symbol>)>,
        tcx: TyCtxt<'tcx>,
    ) {
        // Adds trait (if any) to used items.
        let trait_def_id = impl_item
            .of_trait
            .as_ref()
            .and_then(rustc_hir::TraitRef::trait_def_id);
        if let Some(trait_def_id) = trait_def_id {
            used_items.insert((trait_def_id, None));
        }

        // Collects used items in path (if any).
        if let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(self_ty, path)) =
            impl_item.self_ty.kind
        {
            if let Some(self_ty) = self_ty {
                process_hir_ty(self_ty, used_items, tcx);
            }
            let generic_args = path.segments.iter().flat_map(|segment| segment.args().args);
            for arg in generic_args {
                if let rustc_hir::GenericArg::Type(arg_ty) = arg {
                    process_hir_ty(arg_ty, used_items, tcx);
                }
            }
        }

        // Collects used items in generics.
        process_generics(impl_item.generics, used_items, tcx);

        // Collects used items for assoc items.
        for assoc_item_ref in impl_item.items {
            let assoc_item = tcx.hir().impl_item(assoc_item_ref.id);
            match &assoc_item.kind {
                rustc_hir::ImplItemKind::Const(ty, _) => {
                    process_hir_ty(ty, used_items, tcx);
                }
                rustc_hir::ImplItemKind::Fn(fn_sig, _) => {
                    process_fn_sig(fn_sig, used_items, tcx);
                }
                rustc_hir::ImplItemKind::Type(ty) => {
                    process_hir_ty(ty, used_items, tcx);
                }
            }
        }
    }

    /// Collects child used items for generics.
    fn process_generics<'tcx>(
        generics: &'tcx rustc_hir::Generics,
        used_items: &mut FxHashSet<(DefId, Option<Symbol>)>,
        tcx: TyCtxt<'tcx>,
    ) {
        for predicate in generics.predicates {
            match predicate {
                rustc_hir::WherePredicate::BoundPredicate(bound_info) => {
                    for bound in bound_info.bounds {
                        process_generic_bound(bound, used_items);
                    }
                }
                rustc_hir::WherePredicate::EqPredicate(eq_predicate) => {
                    for ty in [eq_predicate.lhs_ty, eq_predicate.rhs_ty] {
                        process_hir_ty(ty, used_items, tcx);
                    }
                }
                rustc_hir::WherePredicate::RegionPredicate(_) => (),
            }
        }
    }

    /// Collects child used items for generic bound.
    fn process_generic_bound(
        bound: &rustc_hir::GenericBound,
        used_items: &mut FxHashSet<(DefId, Option<Symbol>)>,
    ) {
        if let Some(trait_ref) = bound.trait_ref() {
            if let Res::Def(DefKind::Trait, trait_def_id) = trait_ref.path.res {
                used_items.insert((trait_def_id, None));
            }
        }
    }
}

/// MIR visitor that collects "specialized" calls to the pallet struct associated functions.
struct PalletCallVisitor<'tcx> {
    pallet_struct_def_id: DefId,
    tcx: TyCtxt<'tcx>,
    calls: FxHashMap<LocalDefId, Terminator<'tcx>>,
}

impl<'tcx> PalletCallVisitor<'tcx> {
    pub fn new(pallet_struct_def_id: DefId, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            pallet_struct_def_id,
            tcx,
            calls: FxHashMap::default(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for PalletCallVisitor<'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call { func, .. } = &terminator.kind {
            let call_info = func.const_fn_def().and_then(|(def_id, gen_args)| {
                def_id
                    .as_local()
                    .map(|local_def_id| (local_def_id, gen_args))
            });
            if let Some((local_def_id, gen_args)) = call_info {
                let contains_type_params = || {
                    gen_args
                        .iter()
                        .filter_map(GenericArg::as_type)
                        .any(|gen_ty| {
                            let is_param_ty = gen_ty
                                .walk()
                                .filter_map(GenericArg::as_type)
                                .any(|ty| matches!(ty.kind(), TyKind::Param(_)));
                            is_param_ty
                        })
                };
                let is_pallet_assoc_item = || {
                    impl_for_assoc_item(local_def_id.to_def_id(), self.tcx).is_some_and(
                        |(_, impl_)| {
                            adt_for_impl(&impl_)
                                .is_some_and(|adt_def_id| adt_def_id == self.pallet_struct_def_id)
                        },
                    )
                };
                if !self.calls.contains_key(&local_def_id)
                    && !contains_type_params()
                    && is_pallet_assoc_item()
                {
                    self.calls.insert(local_def_id, terminator.clone());
                }
            }
        }

        self.super_terminator(terminator, location);
    }
}

/// MIR visitor that collects used local and item definitions, item imports and fn calls for the specified locals.
struct ValueVisitor<'tcx, 'analysis> {
    locals: &'analysis FxHashSet<Local>,
    used_items: FxHashSet<DefId>,
    item_defs: FxHashSet<DefId>,
    calls: Vec<Terminator<'tcx>>,
    next_locals: FxHashSet<Local>,
}

impl<'tcx, 'analysis> ValueVisitor<'tcx, 'analysis> {
    pub fn new(locals: &'analysis FxHashSet<Local>) -> Self {
        Self {
            locals,
            used_items: FxHashSet::default(),
            item_defs: FxHashSet::default(),
            calls: Vec::new(),
            next_locals: FxHashSet::default(),
        }
    }
}

impl<'tcx, 'analysis> Visitor<'tcx> for ValueVisitor<'tcx, 'analysis> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        if let StatementKind::Assign(assign) = &statement.kind {
            let place = assign.0;
            if self.locals.contains(&place.local) {
                // Collects used local and item definitions, and item imports for assignment.
                let rvalue = &assign.1;
                process_rvalue(
                    rvalue,
                    &mut self.next_locals,
                    &mut self.used_items,
                    &mut self.item_defs,
                );
            }
        }

        self.super_statement(statement, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call { destination, .. } = &terminator.kind {
            if self.locals.contains(&destination.local) {
                // Adds call for further evaluation.
                self.calls.push(terminator.clone());
            }
        }

        self.super_terminator(terminator, location);
    }
}

/// MIR visitor that collects used item definitions and imports, and fn calls for a closure.
struct ClosureVisitor<'tcx> {
    used_items: FxHashSet<DefId>,
    item_defs: FxHashSet<DefId>,
    calls: Vec<Terminator<'tcx>>,
}

impl<'tcx> ClosureVisitor<'tcx> {
    pub fn new() -> Self {
        Self {
            used_items: FxHashSet::default(),
            item_defs: FxHashSet::default(),
            calls: Vec::new(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for ClosureVisitor<'tcx> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        if let StatementKind::Assign(assign) = &statement.kind {
            // Collects used item definitions and imports for assignment.
            let rvalue = &assign.1;
            process_rvalue(
                rvalue,
                // We don't need to process locals for closures.
                // See doc in `compose_entry_point` at the call site of this visitor.
                &mut FxHashSet::default(),
                &mut self.used_items,
                &mut self.item_defs,
            );
        }

        self.super_statement(statement, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call { .. } = &terminator.kind {
            // Adds call for further evaluation.
            self.calls.push(terminator.clone());
        }

        self.super_terminator(terminator, location);
    }
}

/// Collects used local and item definitions, and item imports for an `Terminator::Call`.
fn process_call(
    call: &Terminator,
    locals: &mut FxHashSet<Local>,
    used_items: &mut FxHashSet<DefId>,
    item_defs: &mut FxHashSet<DefId>,
    tcx: TyCtxt,
) {
    let TerminatorKind::Call { func, args, .. } = &call.kind else {
        return;
    };
    let Some((call_def_id, generic_args)) = func.const_fn_def() else {
        return;
    };

    // Adds `fn` item or its implementation subject (i.e. ADT or trait) to used items.
    if let Some(assoc_item) = tcx.opt_associated_item(call_def_id) {
        let container_def_id = assoc_item.container_id(tcx);
        match assoc_item.container {
            AssocItemContainer::TraitContainer => {
                used_items.insert(container_def_id);
            }
            AssocItemContainer::ImplContainer => {
                let impl_subject = tcx.impl_subject(container_def_id).skip_binder();
                match impl_subject {
                    ImplSubject::Trait(trait_ref) => {
                        used_items.insert(trait_ref.def_id);
                    }
                    ImplSubject::Inherent(ty) => {
                        process_type(&ty, used_items);
                    }
                }
            }
        }
    } else {
        used_items.insert(call_def_id);
    }

    // Adds used local and item definitions, and item imports for arguments.
    for arg in args {
        process_operand(&arg.node, locals, used_items, item_defs);
    }

    // Adds used generic types.
    for arg_type in generic_args.iter().filter_map(|arg| arg.as_type()) {
        process_type(&arg_type, used_items);
    }
}

/// Collects used local and item definitions, and item imports for an `Rvalue`.
fn process_rvalue(
    rvalue: &Rvalue,
    locals: &mut FxHashSet<Local>,
    used_items: &mut FxHashSet<DefId>,
    item_defs: &mut FxHashSet<DefId>,
) {
    match rvalue {
        Rvalue::Use(operand) | Rvalue::UnaryOp(_, operand) => {
            process_operand(operand, locals, used_items, item_defs);
        }
        Rvalue::Repeat(operand, _) => {
            process_operand(operand, locals, used_items, item_defs);

            // TODO: Handle const expression for array length.
        }
        Rvalue::Ref(_, _, place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place)
        | Rvalue::Discriminant(place) => {
            locals.insert(place.local);
        }
        // TODO: Handle thread local references.
        Rvalue::ThreadLocalRef(_) => todo!(),
        Rvalue::Cast(_, operand, ty) | Rvalue::ShallowInitBox(operand, ty) => {
            process_operand(operand, locals, used_items, item_defs);
            process_type(ty, used_items);
        }
        Rvalue::BinaryOp(_, operands) | Rvalue::CheckedBinaryOp(_, operands) => {
            for operand in [&operands.0, &operands.1] {
                process_operand(operand, locals, used_items, item_defs);
            }
        }
        Rvalue::NullaryOp(_, ty) => process_type(ty, used_items),
        Rvalue::Aggregate(kind, operands) => {
            for operand in operands {
                process_operand(operand, locals, used_items, item_defs);
            }

            // Adds aggregate and used types.
            match kind.as_ref() {
                AggregateKind::Array(ty) => process_type(ty, used_items),
                AggregateKind::Tuple => (),
                AggregateKind::Adt(def_id, _, generic_args, _, _) => {
                    used_items.insert(*def_id);
                    for arg_ty in generic_args.iter().filter_map(GenericArg::as_type) {
                        process_type(&arg_ty, used_items);
                    }
                }
                AggregateKind::Closure(def_id, args) | AggregateKind::Coroutine(def_id, args) => {
                    used_items.insert(*def_id);
                    for arg_ty in args.iter().filter_map(GenericArg::as_type) {
                        process_type(&arg_ty, used_items);
                    }
                }
            }
        }
    }
}

/// Collects used local and item definitions, and item imports for an `Operand`.
fn process_operand(
    operand: &Operand,
    locals: &mut FxHashSet<Local>,
    used_items: &mut FxHashSet<DefId>,
    item_defs: &mut FxHashSet<DefId>,
) {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            // Adds local for further evaluation.
            locals.insert(place.local);
        }
        Operand::Constant(constant) => {
            // Handles globals.
            let const_kind = constant.const_;
            if let rustc_middle::mir::Const::Unevaluated(uneval_const, ty) = const_kind {
                // Add constant definition.
                item_defs.insert(uneval_const.def);

                // Add constant type.
                process_type(&ty, used_items);

                // Add generic arg types.
                for arg_ty in uneval_const.args.iter().filter_map(GenericArg::as_type) {
                    process_type(&arg_ty, used_items);
                }
            } else {
                // Add constant type to imports.
                process_type(&const_kind.ty(), used_items);
            }
        }
    }
}

/// Collects used items for type.
///
/// Primitive types (e.g. `bool`, `int*`), `str` and unit (i.e. `()`) are ignored.
fn process_type(ty: &Ty, used_items: &mut FxHashSet<DefId>) {
    for gen_ty in ty.walk().filter_map(GenericArg::as_type) {
        match gen_ty.kind() {
            TyKind::Adt(def, _) => {
                used_items.insert(def.did());
            }
            TyKind::Foreign(def_id)
            | TyKind::FnDef(def_id, _)
            | TyKind::Closure(def_id, _)
            | TyKind::Coroutine(def_id, _)
            | TyKind::CoroutineWitness(def_id, _) => {
                used_items.insert(*def_id);
            }
            TyKind::Alias(_, alias) => {
                used_items.insert(alias.def_id);
            }
            _ => (),
        }
    }
}

/// Composes tractable entry point param type from MIR type (if possible).
///
/// NOTE: A tractable type must *NOT* include any generics and/or raw indirection.
fn tractable_param_type(
    ty: &Ty,
    used_items: &mut FxHashSet<DefId>,
    tcx: TyCtxt<'_>,
) -> Option<String> {
    // Checks for "raw" indirection and/or dynamic types.
    let has_raw_indirection_or_dynamic_types = ty.walk().any(|gen_arg| {
        gen_arg.as_type().is_some_and(|gen_ty| {
            matches!(
                gen_ty.peel_refs().kind(),
                TyKind::RawPtr(_)
                    | TyKind::FnDef(_, _)
                    | TyKind::FnPtr(_)
                    | TyKind::Closure(_, _)
                    | TyKind::Dynamic(_, _, _)
                    | TyKind::Coroutine(_, _)
                    | TyKind::CoroutineWitness(_, _)
            )
        })
    });
    if has_raw_indirection_or_dynamic_types {
        return None;
    }

    // Makes local type paths resolvable.
    let mut tractable_ty_path = ty.to_string();
    for gen_ty in ty.walk().filter_map(GenericArg::as_type) {
        if let TyKind::Adt(def, _) = gen_ty.peel_refs().kind() {
            let def_id = def.did();
            if let Some(local_def_id) = def_id.as_local() {
                let gen_ty_path = tcx.def_path_str(def_id);
                let resolvable_ty_path = if is_visible_from_crate_root(def_id, tcx) {
                    format!("crate::{gen_ty_path}")
                } else {
                    used_items.insert(def_id);
                    utils::def_name(local_def_id, tcx)
                        .expect("Expected local definition name")
                        .to_string()
                };
                tractable_ty_path = tractable_ty_path.replace(&gen_ty_path, &resolvable_ty_path);
            } else {
                used_items.insert(def_id);
            }
        }
    }
    Some(tractable_ty_path)
}

/// Composes tractable entry point param type from HIR type (if possible).
///
/// NOTE: A tractable type must *NOT* include any generics and/or raw indirection.
fn tractable_param_hir_type<'tcx>(
    fn_param: &'tcx rustc_hir::Param,
    ty: &'tcx rustc_hir::Ty<'tcx>,
    generics: &Generics,
    used_items: &mut FxHashSet<DefId>,
    tcx: TyCtxt<'tcx>,
) -> Option<String> {
    let mut visitor = TyVisitor::new(tcx);
    visitor.visit_ty(ty);

    let hir = tcx.hir();
    let config_param_name = Symbol::intern("T");
    let mut ty_generic_params = Vec::new();
    let mut int_const_generic_params = Vec::new();
    let mut fq_item_paths = Vec::new();
    let mut config_related_types = FxHashMap::default();

    for gen_ty in visitor.types {
        let has_raw_indirection_dynamic_or_opaque_types = matches!(
            gen_ty.kind,
            rustc_hir::TyKind::Ptr(_)
                | rustc_hir::TyKind::BareFn(_)
                | rustc_hir::TyKind::OpaqueDef(_, _, _)
                | rustc_hir::TyKind::TraitObject(_, _, _)
        );
        if has_raw_indirection_dynamic_or_opaque_types {
            // Bails if any types have "raw" indirection, opaque or dynamic types.
            return None;
        }

        if let Some((_, generic_param_name)) = gen_ty.as_generic_param() {
            let gen_param_impl = generics.ty_param_impls.get(&generic_param_name.name);
            if let Some(arg_ty) = gen_param_impl {
                ty_generic_params.push((gen_ty, arg_ty, generic_param_name.name));
            } else {
                // Bails there are any non-`T: Config` generic params.
                return None;
            }
        } else if let rustc_hir::TyKind::Path(rustc_hir::QPath::TypeRelative(rel_ty, segment)) =
            gen_ty.kind
        {
            let is_config_param =
                rel_ty
                    .as_generic_param()
                    .is_some_and(|(_, generic_param_name)| {
                        generic_param_name.name == config_param_name
                    });
            if is_config_param {
                config_related_types.insert(rel_ty.span, segment);
            }
        } else if let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) = gen_ty.kind {
            match path.res {
                Res::Def(def_kind, def_id) => {
                    if matches!(
                        def_kind,
                        DefKind::Struct
                            | DefKind::Enum
                            | DefKind::Union
                            | DefKind::Trait
                            | DefKind::TyAlias
                            | DefKind::TraitAlias
                    ) && is_visible_from_crate_root(def_id, tcx)
                    {
                        let mut def_path = tcx.def_path_str(def_id);
                        if def_id.is_local() {
                            def_path = format!("crate::{def_path}");
                        }
                        let args_span = path
                            .segments
                            .last()
                            .and_then(|segment| segment.args)
                            .map(|args| args.span_ext);
                        let def_span = match args_span {
                            Some(args_span) => {
                                Span::new(path.span.lo(), args_span.lo(), path.span.ctxt(), None)
                            }
                            None => path.span,
                        };
                        fq_item_paths.push((path, def_id, def_path, def_span));
                    } else {
                        used_items.insert(def_id);
                    }
                }
                Res::SelfTyParam { trait_: def_id }
                | Res::SelfTyAlias {
                    alias_to: def_id, ..
                }
                | Res::SelfCtor(def_id) => {
                    used_items.insert(def_id);
                }
                _ => (),
            };
        }
    }
    for anon_const in visitor.anon_consts {
        let const_expr = hir.body(anon_const.body).value;
        if let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = const_expr.kind {
            match path.res {
                Res::Def(DefKind::ConstParam, const_param_def_id) => {
                    let const_ty = tcx.type_of(const_param_def_id).skip_binder();
                    if matches!(const_ty.kind(), TyKind::Int(_) | TyKind::Uint(_)) {
                        int_const_generic_params.push((const_expr, const_ty));
                    } else {
                        // Bails if there are any non-integer const generic params.
                        return None;
                    }
                }
                Res::Def(DefKind::Const, const_def_id) => {
                    used_items.insert(const_def_id);
                }
                _ => (),
            }
        }
    }

    // Composes entry point param, and corresponding dispatchable call arg vars,
    // by replacing `T: Config` param types with concrete `Config` type,
    // and integer const generic params with an arbitrary large value.
    let source_map = tcx.sess.source_map();
    let mut user_ty = source_map
        .span_to_snippet(fn_param.ty_span)
        .expect("Expected snippet for span");
    if !ty_generic_params.is_empty()
        || !int_const_generic_params.is_empty()
        || !fq_item_paths.is_empty()
    {
        let offset = fn_param.ty_span.lo().to_usize();
        let mut offset_shift = 0;
        let config_trait_item_names =
            trait_assoc_item_names(generics.config_trait_local_def_id, tcx);
        let replacements = ty_generic_params
            .into_iter()
            .map(|(param_ty, arg_ty, generic_param_name)| {
                let mut arg_ty_path = tractable_param_type(arg_ty, used_items, tcx)
                    .expect("Expected tractable generic args");
                if generic_param_name == config_param_name {
                    if let Some(segment) = config_related_types.get(&param_ty.span) {
                        let related_ty_name = segment.ident.as_str();
                        let is_ty_name_in_config_trait = config_trait_item_names
                            .as_ref()
                            .is_some_and(|names| names.contains(related_ty_name));
                        if is_ty_name_in_config_trait {
                            arg_ty_path = format!(
                                "<{arg_ty_path} as crate::{}>",
                                tcx.def_path_str(generics.config_trait_local_def_id)
                            );
                        } else {
                            arg_ty_path = format!("<{arg_ty_path} as frame_system::Config>");
                        }
                    }
                }
                (param_ty.span, arg_ty_path)
            })
            .chain(
                fq_item_paths
                    .into_iter()
                    .map(|(_, _, name, span)| (span, name)),
            )
            .chain(
                // We use 1000 arbitrarily, but the idea is that expressions don't end up exceeding MIRAI's k-limits.
                // Ref: <https://github.com/facebookexperimental/MIRAI/blob/main/documentation/Overview.md#k-limits>
                // Ref: <https://github.com/facebookexperimental/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/k_limits.rs>
                int_const_generic_params
                    .into_iter()
                    .map(|(config_expr, _)| (config_expr.span, "1000".to_string())),
            )
            .unique_by(|(span, _)| *span)
            .sorted_by_key(|(span, _)| *span);
        for (span, replacement) in replacements {
            let start = span.lo().to_usize() - offset + offset_shift;
            let end = span.hi().to_usize() - offset + offset_shift;
            user_ty.replace_range(start..end, &replacement);
            offset_shift += replacement.len() - (end - start);
        }
    }
    Some(user_ty)
}

/// Returns the well-formed `let` statement for the `local` (if any);
fn let_statement_for_local(local_decl: &LocalDecl, tcx: TyCtxt<'_>) -> Option<(String, Span)> {
    let span_local = local_decl.source_info.span;
    let source_map = tcx.sess.source_map();

    // Retrieves snippet from `let` keyword to local `span` (inclusive).
    let span_let_to_span_inclusive = source_map
        .span_extend_to_prev_str(span_local, "let", true, false)
        .map(|sp| sp.with_lo(sp.lo() - BytePos(3)))?;
    let snippet_let_to_span_inclusive = source_map
        .span_to_snippet(span_let_to_span_inclusive)
        .ok()?;

    // Retrieves snippet from span to closing semicolon.
    let next_src = source_map.span_to_next_source(span_local).ok()?;
    let mut has_open_quotes = false;
    let mut quote_char = None;
    let mut prev_char_is_escape = false;
    let mut open_unquoted_brackets = Vec::new();
    let snippet_span_to_semi = next_src
        .chars()
        .take_while_inclusive(|char| {
            // Tracks state for character and string quotes (i.e. `'` and `"`).
            if *char == '"' || *char == '\'' {
                if !has_open_quotes {
                    has_open_quotes = true;
                    quote_char = Some(*char);
                } else if !prev_char_is_escape
                    && quote_char.expect("Expected a quote character") == *char
                {
                    has_open_quotes = false;
                }
            }

            // It's only an escape character if the previous character
            // is not an escape char as well.
            prev_char_is_escape = *char == '\\' && !prev_char_is_escape;

            // Tracks state for square and curly brackets (i.e. `[`, `]`, `{` and `}`).
            if !has_open_quotes && matches!(char, '[' | '{') {
                open_unquoted_brackets.push(*char);
            }
            if !has_open_quotes
                && match char {
                    ']' => matches!(open_unquoted_brackets.last(), Some('[')),
                    '}' => matches!(open_unquoted_brackets.last(), Some('{')),
                    _ => false,
                }
            {
                open_unquoted_brackets.pop();
            }

            // Stop at semicolon, unless it comes after an unclosed quote, or unqouted unclosed square bracket.
            *char != ';' || has_open_quotes || !open_unquoted_brackets.is_empty()
        })
        .join("");

    // Composes `let` statement and its `span`.
    let snippet_stmt = format!("{snippet_let_to_span_inclusive}{snippet_span_to_semi}");
    let span_stmt = span_let_to_span_inclusive
        .with_hi(span_let_to_span_inclusive.hi() + BytePos(snippet_span_to_semi.len() as u32));
    Some((snippet_stmt, span_stmt))
}

/// Collects all HIR types and anonymous constants.
struct TyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    types: Vec<&'tcx rustc_hir::Ty<'tcx>>,
    anon_consts: Vec<&'tcx rustc_hir::AnonConst>,
}

impl<'tcx> TyVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            types: Vec::new(),
            anon_consts: Vec::new(),
        }
    }
}

impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for TyVisitor<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_ty(&mut self, t: &'tcx rustc_hir::Ty<'tcx>) {
        self.types.push(t);
        rustc_hir::intravisit::walk_ty(self, t);
    }

    fn visit_anon_const(&mut self, c: &'tcx rustc_hir::AnonConst) {
        self.anon_consts.push(c);
        rustc_hir::intravisit::walk_anon_const(self, c);
    }
}

/// Returns parent `impl` (if any) of an associated item.
fn impl_for_assoc_item(def_id: DefId, tcx: TyCtxt<'_>) -> Option<(LocalDefId, rustc_hir::Impl)> {
    let assoc_item = tcx.opt_associated_item(def_id)?;
    if assoc_item.container != AssocItemContainer::ImplContainer {
        return None;
    }
    let impl_local_def_id = assoc_item.container_id(tcx).as_local()?;
    let node = tcx.hir_node_by_def_id(impl_local_def_id);
    if let rustc_hir::Node::Item(item) = node {
        if let rustc_hir::ItemKind::Impl(impl_) = item.kind {
            return Some((impl_local_def_id, *impl_));
        }
    }
    None
}

/// Returns subject `ADT` (if any) for an `impl`.
fn adt_for_impl(impl_: &rustc_hir::Impl) -> Option<DefId> {
    if let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) = impl_.self_ty.kind {
        if let Res::Def(DefKind::Struct | DefKind::Enum | DefKind::Union, adt_def_id) = path.res {
            return Some(adt_def_id);
        }
    }
    None
}

/// Checks if an item (given it's `DefId`) is "visible" from the crate root.
fn is_visible_from_crate_root(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    let crate_vis = Visibility::Restricted(CRATE_DEF_ID.to_def_id());
    let vis = tcx.visibility(def_id);
    if vis.is_at_least(crate_vis, tcx) {
        if let Some(local_def_id) = def_id.as_local() {
            let mut parent_mod_def_id = tcx.parent_module_from_def_id(local_def_id);
            loop {
                if parent_mod_def_id.is_top_level_module() {
                    return true;
                }
                if is_visible_from_crate_root(parent_mod_def_id.to_def_id(), tcx) {
                    parent_mod_def_id =
                        tcx.parent_module_from_def_id(parent_mod_def_id.to_local_def_id());
                } else {
                    return false;
                }
            }
        } else {
            return true;
        }
    }
    false
}

/// Returns names of associated items of a trait.
fn trait_assoc_item_names(
    trait_local_def_id: LocalDefId,
    tcx: TyCtxt<'_>,
) -> Option<FxHashSet<&str>> {
    let trait_node = tcx.hir_node_by_def_id(trait_local_def_id);
    let rustc_hir::Node::Item(trait_item) = trait_node else {
        return None;
    };
    let rustc_hir::ItemKind::Trait(.., trait_item_refs) = trait_item.kind else {
        return None;
    };
    Some(
        trait_item_refs
            .iter()
            .map(|item| item.ident.as_str())
            .collect(),
    )
}
