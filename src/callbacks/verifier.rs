//! `rustc` callbacks and utilities for analyzing FRAME pallet with MIRAI.

use rustc_ast::NestedMetaItem;
use rustc_driver::Compilation;
use rustc_errors::{DiagnosticBuilder, Level, MultiSpan, Style, SubDiagnostic};
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::{AssocKind, TyCtxt};
use rustc_span::{
    def_id::{DefId, LocalDefId},
    Span, Symbol,
};

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use mirai::{
    body_visitor::BodyVisitor, call_graph::CallGraph, constant_domain::ConstantValueCache,
    crate_visitor::CrateVisitor, known_names::KnownNamesCache, summaries::PersistentSummaryCache,
    type_visitor::TypeCache,
};
use tempfile::TempDir;

use super::utils;
use crate::{CONTRACTS_MOD_NAME, ENTRY_POINT_FN_PREFIX};

/// `rustc` callbacks for analyzing FRAME pallet with MIRAI.
pub struct VerifierCallbacks<'compilation> {
    entry_point_names: &'compilation FxHashSet<&'compilation str>,
    mirai_config: Option<MiraiConfig>,
}

impl<'compilation> VerifierCallbacks<'compilation> {
    pub fn new(entry_point_names: &'compilation FxHashSet<&'compilation str>) -> Self {
        Self {
            entry_point_names,
            mirai_config: None,
        }
    }
}

impl<'compilation> rustc_driver::Callbacks for VerifierCallbacks<'compilation> {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        // Initializes MIRAI config.
        // Ref: <https://github.com/facebookexperimental/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/callbacks.rs#L75-L92>
        // Ref: <https://github.com/facebookexperimental/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/callbacks.rs#L143-L149>
        let file_name = config
            .input
            .source_name()
            .prefer_remapped_unconditionaly()
            .to_string();
        let temp_dir = TempDir::new().expect("Failed to create a temp directory.");
        let summary_store_path = String::from(
            temp_dir
                .into_path()
                .to_str()
                .expect("Expected a valid temp directory."),
        );
        // Sets MIRAI options similar to MIRAI CLI defaults.
        // Ref: <https://github.com/facebookexperimental/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/options.rs#L14-L72>
        // Ref: <https://github.com/facebookexperimental/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/callbacks.rs#L143-L149>
        let max_time_body = 60;
        // Between 300 and 600 seconds.
        let max_time_crate = ((5 + self.entry_point_names.len()) * max_time_body as usize)
            .max(max_time_body as usize * 10) as u64;
        let options = mirai::options::Options {
            diag_level: mirai::options::DiagLevel::Paranoid,
            max_analysis_time_for_crate: max_time_crate,
            max_analysis_time_for_body: max_time_body,
            ..mirai::options::Options::default()
        };
        self.mirai_config = Some(MiraiConfig {
            options,
            file_name,
            summary_store_path,
        });
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> Compilation {
        println!("Analyzing FRAME pallet with MIRAI ...");
        let Some(mirai_config) = &self.mirai_config else {
            // Analysis callback was called before `config` callback,
            // so MIRAI configs are not yet initialized.
            let mut err = compiler
                .sess
                .dcx()
                .struct_err("MIRAI config is not yet initialzed");
            err.help("Call the `config` callback before calling `*_analysis` callbacks.");
            err.emit();
            return Compilation::Stop;
        };

        queries.global_ctxt().unwrap().enter(|tcx| {
            // Creates MIRAI crate visitor.
            // Ref: <https://github.com/facebookexperimental/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/callbacks.rs#L130-L174>
            let call_graph_config = mirai_config.options.call_graph_config.to_owned();
            let mut crate_visitor = CrateVisitor {
                buffered_diagnostics: Vec::new(),
                constant_time_tag_cache: None,
                constant_time_tag_not_found: false,
                constant_value_cache: ConstantValueCache::default(),
                diagnostics_for: HashMap::new(),
                file_name: mirai_config.file_name.as_str(),
                known_names_cache: KnownNamesCache::create_cache_from_language_items(),
                options: &mirai_config.options,
                session: &compiler.sess,
                generic_args_cache: HashMap::new(),
                summary_cache: PersistentSummaryCache::new(
                    tcx,
                    mirai_config.summary_store_path.to_owned(),
                ),
                tcx,
                test_run: false,
                type_cache: Rc::new(RefCell::new(TypeCache::new())),
                call_graph: CallGraph::new(call_graph_config, tcx),
            };

            // Finds "contracts" module and collects test module spans.
            let hir = tcx.hir();
            let mut contracts_mod_def_id = None;
            let mut test_mod_spans = FxHashSet::default();
            hir.for_each_module(|mod_def_id| {
                let mod_local_def_id = mod_def_id.to_local_def_id();
                let is_contracts_mod = utils::def_name(mod_local_def_id, tcx)
                    .is_some_and(|name| name.as_str() == CONTRACTS_MOD_NAME);
                if is_contracts_mod {
                    contracts_mod_def_id = Some(mod_def_id);
                } else {
                    let (mod_data, mod_decl_span, mod_hir_id) = hir.get_module(mod_def_id);
                    let mod_body_span = mod_data.spans.inner_span;
                    let mod_attrs = hir.attrs(mod_hir_id);
                    let has_cfg_test_attr = mod_attrs.iter().any(|attr| {
                        let is_cfg_path = attr.has_name(Symbol::intern("cfg"));
                        is_cfg_path
                            && attr.meta_item_list().is_some_and(|meta_items| {
                                let test_symbol = Symbol::intern("test");
                                let is_test_path = |meta_items: &[NestedMetaItem]| {
                                    meta_items
                                        .iter()
                                        .any(|meta_item| meta_item.has_name(test_symbol))
                                };
                                is_test_path(&meta_items)
                                    || meta_items.iter().any(|meta_item| {
                                        (meta_item.has_name(Symbol::intern("any"))
                                            || meta_item.has_name(Symbol::intern("all")))
                                            && meta_item.meta_item_list().is_some_and(is_test_path)
                                    })
                            })
                    });
                    if has_cfg_test_attr
                        && !test_mod_spans.iter().any(|span: &Span| {
                            span.contains(mod_decl_span) || span.contains(mod_body_span)
                        })
                    {
                        test_mod_spans.insert(mod_body_span);
                    }
                }
            });

            // Creates "summaries" for "contracts" (if any) with MIRAI.
            // Ref: <https://github.com/facebookexperimental/MIRAI/blob/main/documentation/Overview.md#summaries>
            if let Some(contracts_mod_def_id) = contracts_mod_def_id {
                println!("Creating summaries for FRAME and Substrate functions ...");
                // Collect "contract" `fn` ids.
                let mut visitor = ContractsVisitor::new(tcx);
                hir.visit_item_likes_in_module(contracts_mod_def_id, &mut visitor);

                for contract_local_def_id in visitor.fns {
                    // Analyzes "contract" with MIRAI and produces "summaries".
                    let contract_def_id = contract_local_def_id.to_def_id();
                    let mut diagnostics = Vec::new();
                    analyze(contract_def_id, &mut crate_visitor, &mut diagnostics, true);

                    // Ignores/cancels diagnostics from "contracts".
                    diagnostics.into_iter().for_each(DiagnosticBuilder::cancel);
                }
            }

            // Finds and analyzes the generated entry points.
            for local_def_id in hir.body_owners() {
                let entry_point_info = utils::def_name(local_def_id, tcx)
                    .filter(|def_name| self.entry_point_names.contains(def_name.as_str()));
                if let Some(entry_point_name) = entry_point_info {
                    println!(
                        "Analyzing dispatchable: `{}` ...",
                        entry_point_name.as_str().replace(ENTRY_POINT_FN_PREFIX, "")
                    );

                    // Analyzes entry point with MIRAI and collects diagnostics.
                    let mut diagnostics = Vec::new();
                    let def_id = local_def_id.to_def_id();
                    analyze(def_id, &mut crate_visitor, &mut diagnostics, false);

                    // Emit diagnostics for generated entry point (if necessary).
                    emit_diagnostics(diagnostics, local_def_id, tcx, &test_mod_spans);
                }
            }

            // Outputs call graph.
            crate_visitor.call_graph.output();
        });
        Compilation::Continue
    }
}

/// MIRAI configuration.
/// Ref: <https://github.com/facebookexperimental/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/callbacks.rs#L29-L39>
#[derive(Debug)]
struct MiraiConfig {
    // MIRAI options.
    // Ref: <https://github.com/facebookexperimental/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/options.rs#L74-L86>
    options: mirai::options::Options,
    /// The relative path of the file being analyzed.
    file_name: String,
    /// A path to the directory where the summary cache should be stored.
    // Ref: <https://github.com/facebookexperimental/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/callbacks.rs#L144-L149>
    summary_store_path: String,
}

// Analyzes `fn` `DefId` with MIRAI.
//
// i.e. Runs the abstract interpreter over the function body and produce a summary of its effects and collect any diagnostics.
//
// Ref: <https://github.com/facebookexperimental/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/crate_visitor.rs#L126-L127>
// Ref: <https://github.com/facebookexperimental/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/crate_visitor.rs#L171-L194>
fn analyze<'analysis>(
    def_id: DefId,
    crate_visitor: &mut CrateVisitor<'analysis, '_>,
    diagnostics: &mut Vec<DiagnosticBuilder<'analysis, ()>>,
    is_contract: bool,
) {
    crate_visitor.call_graph.add_croot(def_id);
    let mut active_calls_map: HashMap<DefId, u64> = HashMap::new();
    let type_cache = crate_visitor.type_cache.clone();
    let mut body_visitor = BodyVisitor::new(
        crate_visitor,
        def_id,
        diagnostics,
        &mut active_calls_map,
        type_cache,
    );
    let summary = body_visitor.visit_body(&[]);
    if is_contract {
        // Caches local "contract" "summaries".
        // Ref: <https://github.com/facebookexperimental/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/crate_visitor.rs#L184-L191>
        crate_visitor.summary_cache.set_summary_for(def_id, summary);
    }
}

/// Emit diagnostics for generated entry point (if necessary).
fn emit_diagnostics(
    diagnostics: Vec<DiagnosticBuilder<()>>,
    local_def_id: LocalDefId,
    tcx: TyCtxt,
    test_mod_spans: &FxHashSet<Span>,
) {
    let source_map = tcx.sess.source_map();
    let is_span_local = |mspan: &MultiSpan| {
        mspan
            .primary_span()
            .and_then(|span| source_map.span_to_location_info(span).0)
            .is_some_and(|source_file| source_file.cnum == LOCAL_CRATE)
    };
    let entry_point_span = tcx.source_span(local_def_id);
    let is_span_in_entry_point = |mspan: &MultiSpan| {
        mspan
            .primary_spans()
            .iter()
            .any(|diag_span| entry_point_span.contains(diag_span.source_callsite()))
    };
    let is_span_in_cfg_test_mod = |mspan: &MultiSpan| {
        mspan.primary_spans().iter().any(|span| {
            test_mod_spans
                .iter()
                .any(|mod_span| mod_span.contains(span.source_callsite()))
        })
    };
    // Checks if diagnostic arises from FRAME and substrate "core" crates
    // (i.e. substrate primitive/`sp_*` libraries, `frame_support` and `frame_system` pallets,
    // and SCALE codec libraries.
    let is_span_in_frame_substrate_core = |mspan: &MultiSpan| {
        mspan
            .primary_span()
            .and_then(|span| source_map.span_to_location_info(span).0)
            .map(|source_file| {
                let source_def_id = source_file.cnum.as_def_id();
                tcx.def_path_str(source_def_id)
            })
            .is_some_and(|name| {
                name.starts_with("sp_")
                    || matches!(
                        name.as_str(),
                        "frame_support" | "frame_system" | "parity_scale_codec" | "scale_info"
                    )
            })
    };
    // Checks if diagnostic arises from `DispatchError` `From::from` conversion implementation via
    // the `#[pallet::error]` macro.
    let is_span_from_dispatch_error_from_impl = |mspan: &MultiSpan| {
        mspan.primary_span().is_some_and(|span| {
                // Handles local `#[pallet::error]` definitions.
                span.parent()
                    .and_then(|parent_local_def_id| {
                        tcx.opt_associated_item(parent_local_def_id.to_def_id())
                    })
                    .is_some_and(|assoc_item| {
                        let is_core_convert_from_impl = assoc_item.name.as_str() == "from"
                            && assoc_item.kind == AssocKind::Fn
                            && assoc_item
                                .trait_item_def_id
                                .is_some_and(|trait_item_def_id| {
                                    let trait_item_path = tcx.def_path_str(trait_item_def_id);
                                    matches!(trait_item_path.as_str(), "core::convert::From::from" | "std::convert::From::from")
                                });
                        let is_dispatch_error_impl =
                            assoc_item.impl_container(tcx).is_some_and(|impl_def_id| {
                                let impl_subject = tcx.impl_subject(impl_def_id).skip_binder();
                                if let rustc_middle::ty::ImplSubject::Trait(trait_ref) = impl_subject {
                                    trait_ref.self_ty().to_string() == "sp_runtime::DispatchError"
                                } else {
                                    false
                                }
                            });
                        is_core_convert_from_impl && is_dispatch_error_impl
                    })
                    // Handles foreign `#[pallet::error]` definitions.
                    || source_map.span_to_snippet(span).is_ok_and(|snippet| {
                        snippet == "error"
                            && source_map
                                .span_to_snippet(source_map.span_extend_to_line(span))
                                .is_ok_and(|line_snippet| line_snippet.contains("pallet::error"))
                    })
            })
    };

    for mut diagnostic in diagnostics {
        let is_missing_mir_or_incomplete_analysis = diagnostic
            .messages
            .first()
            .and_then(|(msg, _)| msg.as_str())
            .is_some_and(|msg| {
                let is_missing_mir = msg.contains("MIR body")
                    && (msg.contains("without") || msg.contains("did not resolve"));
                is_missing_mir || msg.contains("incomplete analysis")
            });
        if is_missing_mir_or_incomplete_analysis {
            // Ignores diagnostics about foreign functions with missing MIR bodies.
            // Ref: <https://github.com/facebookexperimental/MIRAI/blob/main/documentation/Overview.md#foreign-functions>
            diagnostic.cancel();
            continue;
        }

        // Ignores diagnostics that either have no relation to user-defined local item definitions,
        // or arise from FRAME and substrate "core" crates (i.e. substrate primitive/`sp_*` libraries,
        // `frame_support` and `frame_system` pallets, and SCALE codec libraries) or test-only code.
        let relevant_spans = std::iter::once(diagnostic.span.clone())
            .chain(
                diagnostic
                    .children
                    .iter()
                    .map(|sub_diag| sub_diag.span.clone()),
            )
            .skip_while(|span| !is_span_local(span) || is_span_in_entry_point(span))
            .collect::<Vec<_>>();
        if relevant_spans.is_empty()
            || relevant_spans.iter().any(|span| {
                is_span_in_frame_substrate_core(span)
                    || is_span_from_dispatch_error_from_impl(span)
                    || is_span_in_cfg_test_mod(span)
            })
        {
            diagnostic.cancel();
            continue;
        }

        // Updates diagnostic to only include relevant sub-diagnostics.
        if let Some((first_local_span, child_spans)) = relevant_spans.split_first() {
            if let Some(first_local_span) = first_local_span.primary_span() {
                diagnostic.replace_span_with(first_local_span, true);
                diagnostic.children = child_spans
                    .iter()
                    .map(|span| SubDiagnostic {
                        level: Level::Note,
                        messages: vec![("related location".into(), Style::NoStyle)],
                        span: span.clone(),
                    })
                    .collect();
            }
        }
        diagnostic.emit();
    }
}

/// Collects `fn` `LocalDefIds`.
struct ContractsVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    fns: FxHashSet<LocalDefId>,
}

impl<'tcx> ContractsVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            fns: FxHashSet::default(),
        }
    }
}

impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for ContractsVisitor<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_fn(
        &mut self,
        _: rustc_hir::intravisit::FnKind<'tcx>,
        _: &'tcx rustc_hir::FnDecl<'tcx>,
        _: rustc_hir::BodyId,
        _: Span,
        id: LocalDefId,
    ) {
        self.fns.insert(id);
    }
}
