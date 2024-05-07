//! `rustc` callbacks and utilities for generating tractable entry points for FRAME dispatchable functions.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def::{DefKind, Res},
    definitions::{DefPathData, DisambiguatedDefPathData},
    Generics, ItemKind,
};
use rustc_middle::{
    mir::{
        visit::Visitor, AggregateKind, Body, HasLocalDecls, Local, LocalDecl, Location, Operand,
        Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::{AssocItemContainer, GenericArg, ImplSubject, Ty, TyCtxt, TyKind},
};
use rustc_span::{
    def_id::{DefId, LocalDefId},
    BytePos, Span, Symbol,
};

use itertools::Itertools;

/// `rustc` callbacks for generating tractable entry points for FRAME dispatchable functions.
#[derive(Default)]
pub struct EntryPointCallbacks(FxHashMap<String, String>);

impl EntryPointCallbacks {
    /// Returns the generated tractable entry points (if any) as a `name` -> `content` map.
    pub fn entry_points(&self) -> &FxHashMap<String, String> {
        &self.0
    }
}

impl rustc_driver::Callbacks for EntryPointCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _handler: &rustc_session::EarlyErrorHandler,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        println!("Searching for dispatchable function declarations ...");
        let mut phase = Phase::Names;
        let mut entry_points = FxHashMap::default();

        queries.global_ctxt().unwrap().enter(|tcx| {
            // Find names of dispatchable functions.
            let names = dispatchable_names(tcx);
            if names.is_empty() {
                return;
            }

            // Finds `DefId`s of dispatchable functions.
            phase = Phase::DefIds;
            println!("Searching for dispatchable function definitions ...");
            let def_ids = dispatchable_ids(&names, tcx);
            if def_ids.is_empty() {
                return;
            }

            // Adds warnings for `Call` variants whose dispatchable function wasn't found.
            if names.len() != def_ids.len() {
                let id_names: Vec<_> = def_ids
                    .iter()
                    .filter_map(|def_id| {
                        def_id
                            .as_local()
                            .and_then(|local_def_id| def_name(local_def_id, tcx))
                    })
                    .collect();
                for name in names {
                    let symbol = Symbol::intern(name);
                    if !id_names.contains(&symbol) {
                        let mut warning = compiler.session().struct_warn(format!(
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
            for local_def_id in hir.body_owners() {
                let body_owner_kind = hir.body_owner_kind(local_def_id);
                if matches!(
                    body_owner_kind,
                    rustc_hir::BodyOwnerKind::Fn | rustc_hir::BodyOwnerKind::Closure
                ) {
                    let body = tcx.optimized_mir(local_def_id);
                    let mut visitor = DispatchableCallVisitor::new(&def_ids);
                    visitor.visit_body(body);

                    for (def_id, terminator) in visitor.calls {
                        calls.insert(def_id, (body, terminator));
                    }
                }
            }
            if calls.is_empty() {
                return;
            }

            // Compose entry points module content and add warnings for missing missing dispatchable calls.
            println!("Generating tractable entry points for FRAME pallet ...");
            phase = Phase::EntryPoints;
            for def_id in def_ids.iter() {
                let call = calls
                    .get(def_id)
                    .and_then(|(body, terminator)| compose_entry_point(terminator, body, tcx));
                if let Some((name, content)) = call {
                    entry_points.insert(name, content);
                } else {
                    let local_def_id = def_id
                        .as_local()
                        .expect("Expected local def id for dispatchable");
                    let name =
                        def_name(local_def_id, tcx).expect("Expected a name for dispatchable");
                    let mut warning = compiler
                        .session()
                        .struct_warn(format!("Couldn't find a call for dispatchable: `{name}`"));
                    warning.note(format!(
                        "pallet-verifier couldn't find a unit test\
                        or benchmark that calls: `{name}`."
                    ));
                    warning.help(format!(
                        "Add a unit test or benchmark that calls: `{name}`."
                    ));
                    warning.emit();
                }
            }
        });

        if entry_points.is_empty() {
            // Stops compilation if we fail to generate any tractable entry points.
            // Sets error message based on the analysis phase reached.
            let (msg, note, help) = match phase {
                Phase::Names => (
                    "Couldn't find any dispatchable functions",
                    Some("pallet-verifier can only analyze FRAME pallets"),
                    Some("Learn more at https://github.com/davidsemakula/pallet-verifier"),
                ),
                Phase::DefIds => (
                    "Failed to find definitions for any dispatchable function",
                    Some("This is most likely a bug in pallet-verifier."),
                    Some(
                        "Please consider filling a bug report at \
                        https://github.com/davidsemakula/pallet-verifier/issues",
                    ),
                ),
                Phase::Calls | Phase::EntryPoints => (
                    "Failed to generate tractable entry points",
                    None,
                    Some("Add some unit tests or benchmarks for all dispatchable functions."),
                ),
            };
            let mut error = compiler.session().struct_err(msg);
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
            self.0 = entry_points;
            rustc_driver::Compilation::Continue
        }
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

/// Composes an entry point (returns a `name` and `content` pair).
///
/// NOTE: This function assumes the terminator wraps a call to a dispatchable function, but doesn't verify it.
fn compose_entry_point<'tcx>(
    terminator: &Terminator<'tcx>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<(String, String)> {
    let TerminatorKind::Call {
        func,
        args,
        fn_span,
        ..
    } = &terminator.kind
    else {
        return None;
    };
    let (def_id, generic_args) = func.const_fn_def()?;

    // Dispatchable name.
    let local_def_id = def_id.as_local()?;
    let dispatchable_name = def_name(local_def_id, tcx)?;

    // `T: Config` type and name.
    let config_type = generic_args.first()?.as_type()?;
    let config_def_id = config_type.ty_adt_def()?.did();
    let config_local_def_id = config_def_id.as_local()?;
    let config_name = def_name(config_local_def_id, tcx)?;

    // Item imports and definitions.
    let mut used_items = FxHashSet::default();
    let mut item_defs = FxHashSet::default();
    used_items.insert(config_def_id);

    // Compose arguments.
    let mut locals = FxHashSet::default();
    let source_map = tcx.sess.source_map();
    let local_decls = body.local_decls();
    let args_list = args
        .iter()
        .map(|arg| {
            // Collect used local and item definitions, and item imports for arguments.
            process_operand(arg, &mut locals, &mut used_items, &mut item_defs);

            // Add value based on user input.
            match arg {
                Operand::Copy(place) | Operand::Move(place) => {
                    let local_decl = &local_decls
                        .get(place.local)
                        .expect("Expected local declaration");
                    let span = local_decl.source_info.span;
                    source_map
                        .span_to_snippet(span)
                        .expect("Expected snippet for span")
                }
                Operand::Constant(constant) => source_map
                    .span_to_snippet(constant.span)
                    .expect("Expected snippet for span"),
            }
        })
        .join(", ");

    // Collects used local and item definitions, and item imports.
    let mut stmts = FxHashSet::default();
    let mut call_spans = vec![*fn_span];
    while !locals.is_empty() {
        // Adds `let` assignments for locals to statements.
        stmts.extend(locals.iter().filter_map(|local| {
            let local_decl = local_decls.get(*local).expect("Expected local declaration");
            let span = local_decl.source_info.span;
            let is_in_call = call_spans.iter().any(|sp| sp.contains(span));
            if !is_in_call {
                let_statement_for_local(local_decl, tcx)
            } else {
                None
            }
        }));

        // Collects used local and item definitions, and item imports for current locals.
        let mut visitor = ValueVisitor::new(&locals);
        visitor.visit_body(body);

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

    // Collects used item definitions and imports for closures.
    //
    // NOTE: We don't collect locals because captured locals are already handled as locals
    // for the parent function above, while non-captured locals (i.e. locals defined inside the closure)
    // are already defined in the closure's `let` statement above.
    let mut closures: FxHashSet<_> = used_items
        .iter()
        .filter(|item_id| tcx.is_closure(**item_id))
        .cloned()
        .collect();
    while !closures.is_empty() {
        // Tracks child closures for next iteration.
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
                    .filter(|item_id| tcx.is_closure(**item_id)),
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
        // Uses `TyCtxt::source_span` to get the full span, not just the header.
        let decl_local_id = item_id.as_local().expect("Expected local declaration");
        let span = tcx.source_span(decl_local_id);
        let snippet = source_map
            .span_to_snippet(span)
            .expect("Expected snippet for span");
        stmts.insert((snippet, span));
    }

    // Composes entry point.
    let use_decls = used_items
        .into_iter()
        .filter_map(|item_id| {
            let item_kind = tcx.def_kind(item_id);
            (!matches!(item_kind, DefKind::Closure | DefKind::Generator)).then_some(format!(
                "use {}{};",
                if item_id.is_local() { "crate::" } else { "" },
                tcx.def_path_str(item_id)
            ))
        })
        .join("\n    ");
    let assign_decls = stmts
        .into_iter()
        .sorted_by_key(|(_, span)| *span)
        .map(|(snippet, _)| snippet)
        .join("\n    ");
    let name = format!("__pallet_verifier_entry_point__{dispatchable_name}");
    let content = format!(
        r"
#[allow(unused)]
#[allow(nonstandard_style)]
pub fn {name}() {{
    {use_decls}

    {assign_decls}

    crate::Pallet::<{config_name}>::{dispatchable_name}({args_list});
}}"
    );
    Some((name, content))
}

/// MIR visitor that collects calls to the specified dispatchables functions.
pub struct DispatchableCallVisitor<'tcx, 'a> {
    def_ids: &'a FxHashSet<DefId>,
    calls: FxHashMap<DefId, Terminator<'tcx>>,
}

impl<'tcx, 'a> DispatchableCallVisitor<'tcx, 'a> {
    pub fn new(def_ids: &'a FxHashSet<DefId>) -> Self {
        Self {
            def_ids,
            calls: FxHashMap::default(),
        }
    }
}

impl<'tcx, 'a> Visitor<'tcx> for DispatchableCallVisitor<'tcx, 'a> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call { func, .. } = &terminator.kind {
            let call_info = func.const_fn_def().filter(|(def_id, _)| {
                self.def_ids.contains(def_id) && !self.calls.contains_key(def_id)
            });
            if let Some((def_id, _)) = call_info {
                self.calls.insert(def_id, terminator.clone());
            }
        }

        self.super_terminator(terminator, location);
    }
}

/// MIR visitor that collects used local and item definitions, item imports and fn calls for the specified locals.
pub struct ValueVisitor<'tcx, 'a> {
    locals: &'a FxHashSet<Local>,
    used_items: FxHashSet<DefId>,
    item_defs: FxHashSet<DefId>,
    calls: Vec<Terminator<'tcx>>,
    next_locals: FxHashSet<Local>,
}

impl<'tcx, 'a> ValueVisitor<'tcx, 'a> {
    pub fn new(locals: &'a FxHashSet<Local>) -> Self {
        Self {
            locals,
            used_items: FxHashSet::default(),
            item_defs: FxHashSet::default(),
            calls: Vec::new(),
            next_locals: FxHashSet::default(),
        }
    }
}

impl<'tcx, 'a> Visitor<'tcx> for ValueVisitor<'tcx, 'a> {
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
pub struct ClosureVisitor<'tcx> {
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

/// Finds names of dispatchable functions.
///
/// Dispatchable functions are represented as variants of an enum `Call<T: Config>`
/// with attributes `#[codec(index: u8 = ..)]`.
/// Notably, there's a "phantom" variant `__Ignore` which should be, well, ignored :)
fn dispatchable_names(tcx: TyCtxt<'_>) -> FxHashSet<&str> {
    let mut results = FxHashSet::default();
    let hir = tcx.hir();
    for item_id in hir.items() {
        let item = hir.item(item_id);
        if item.ident.as_str() == "Call" {
            if let ItemKind::Enum(enum_def, enum_generics) = item.kind {
                if !is_config_bounded(enum_generics, tcx) {
                    continue;
                }
                for variant in enum_def.variants {
                    let name = variant.ident.as_str();
                    if !name.starts_with("__") {
                        results.insert(name);
                    }
                }
            }
        }
    }
    results
}

/// Finds `DefId`s of dispatchable functions.
///
/// Dispatchable function definitions are associated `fn`s of `impl<T: Config> Pallet<T>`.
fn dispatchable_ids(names: &FxHashSet<&str>, tcx: TyCtxt<'_>) -> FxHashSet<DefId> {
    let hir = tcx.hir();
    hir.body_owners()
        .filter_map(|local_def_id| {
            let body_owner_kind = hir.body_owner_kind(local_def_id);
            if !matches!(body_owner_kind, rustc_hir::BodyOwnerKind::Fn) {
                return None;
            }
            let fn_name = def_name(local_def_id, tcx)?;
            if !names.contains(&fn_name.as_str()) {
                return None;
            }
            let def_id = local_def_id.to_def_id();
            let assoc_item = tcx.opt_associated_item(def_id)?;
            if assoc_item.container != AssocItemContainer::ImplContainer {
                return None;
            }
            let impl_def_id = assoc_item.container_id(tcx);
            let impl_local_def_id = impl_def_id.as_local()?;
            let item = hir.get_by_def_id(impl_local_def_id);
            let rustc_hir::Node::Item(item) = item else {
                return None;
            };
            let ItemKind::Impl(impl_item) = item.kind else {
                return None;
            };
            let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) =
                impl_item.self_ty.kind
            else {
                return None;
            };
            if !is_config_bounded(impl_item.generics, tcx) {
                return None;
            }
            let Res::Def(DefKind::Struct, struct_def_id) = path.res else {
                return None;
            };
            let is_pallet_struct_impl = struct_def_id
                .as_local()
                .and_then(|struct_local_def_id| def_name(struct_local_def_id, tcx))
                .is_some_and(|struct_name| struct_name.as_str() == "Pallet");
            is_pallet_struct_impl.then_some(local_def_id.to_def_id())
        })
        .collect()
}

/// Returns the name of the `LocalDefId` as a `Symbol` (if any).
fn def_name(local_def_id: LocalDefId, tcx: TyCtxt<'_>) -> Option<Symbol> {
    let def_path = tcx.hir().def_path(local_def_id);
    let def_path_data = def_path.data.last()?;
    match def_path_data {
        DisambiguatedDefPathData {
            data:
                DefPathData::MacroNs(name)
                | DefPathData::LifetimeNs(name)
                | DefPathData::TypeNs(name)
                | DefPathData::ValueNs(name),
            ..
        } => Some(*name),
        _ => None,
    }
}

/// Verifies that the generics only include a `<T: Config>` bound.
fn is_config_bounded(generics: &Generics, tcx: TyCtxt<'_>) -> bool {
    if generics.params.len() == 1 {
        let param_name = Symbol::intern("T");
        if let Some((bounds_info,)) = generics
            .get_named(param_name)
            .and_then(|param| generics.bounds_for_param(param.def_id).collect_tuple())
        {
            if bounds_info.bounds.len() == 1 {
                if let Some(trait_ref) = bounds_info.bounds[0].trait_ref() {
                    if let Res::Def(DefKind::Trait, trait_def_id) = trait_ref.path.res {
                        if let Some(trait_name) = trait_def_id
                            .as_local()
                            .and_then(|trait_local_def_id| def_name(trait_local_def_id, tcx))
                        {
                            return trait_name.as_str() == "Config";
                        }
                    }
                }
            }
        }
    }

    false
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
        process_operand(arg, locals, used_items, item_defs);
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
                AggregateKind::Closure(def_id, args)
                | AggregateKind::Generator(def_id, args, _) => {
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
            let const_kind = constant.literal;
            if let rustc_middle::mir::ConstantKind::Unevaluated(uneval_const, ty) = const_kind {
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
    match ty.peel_refs().kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Never
        | TyKind::FnPtr(_)
        | TyKind::Dynamic(_, _, _)
        | TyKind::Param(_)
        | TyKind::Bound(_, _)
        | TyKind::Placeholder(_)
        | TyKind::Infer(_)
        | TyKind::Error(_) => (),
        TyKind::Adt(def, args) => {
            used_items.insert(def.did());
            for arg_ty in args.iter().filter_map(GenericArg::as_type) {
                process_type(&arg_ty, used_items);
            }
        }
        TyKind::Foreign(def_id) => {
            used_items.insert(*def_id);
        }
        TyKind::Array(ty, _) | TyKind::Slice(ty) | TyKind::Ref(_, ty, _) => {
            process_type(ty, used_items);
        }
        TyKind::RawPtr(ty_mut) => {
            process_type(&ty_mut.ty, used_items);
        }
        TyKind::FnDef(def_id, args) => {
            used_items.insert(*def_id);
            for arg_ty in args.iter().filter_map(GenericArg::as_type) {
                process_type(&arg_ty, used_items);
            }
        }
        TyKind::Closure(def_id, args)
        | TyKind::Generator(def_id, args, _)
        | TyKind::GeneratorWitnessMIR(def_id, args) => {
            used_items.insert(*def_id);
            for arg_ty in args.iter().filter_map(GenericArg::as_type) {
                process_type(&arg_ty, used_items);
            }
        }
        TyKind::GeneratorWitness(types) => {
            for ty in types.skip_binder() {
                process_type(&ty, used_items);
            }
        }
        TyKind::Tuple(types) => {
            for ty in *types {
                process_type(&ty, used_items);
            }
        }
        TyKind::Alias(_, alias) => {
            used_items.insert(alias.def_id);
            for arg_ty in alias.args.iter().filter_map(GenericArg::as_type) {
                process_type(&arg_ty, used_items);
            }
        }
    }
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
