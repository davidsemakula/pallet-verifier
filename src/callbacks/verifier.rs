//! `rustc` callbacks and utilities for analyzing FRAME pallet with MIRAI.

use rustc_driver::Compilation;
use rustc_errors::MultiSpan;
use rustc_hash::FxHashSet;
use rustc_interface::interface::Compiler;
use rustc_span::def_id::{DefId, CRATE_DEF_ID};

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use mirai::{
    body_visitor::BodyVisitor, call_graph::CallGraph, constant_domain::ConstantValueCache,
    crate_visitor::CrateVisitor, known_names::KnownNamesCache, summaries::PersistentSummaryCache,
    type_visitor::TypeCache,
};
use tempfile::TempDir;

use super::utils;
use crate::ENTRY_POINT_FN_PREFIX;

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
        let file_name = config.input.source_name().prefer_remapped().to_string();
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
        let max_time_crate =
            ((5 + self.entry_point_names.len()) * max_time_body as usize).max(600) as u64;
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
                .session()
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
                session: compiler.session(),
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

            // Retrieves local module spans.
            let crate_root_span = tcx.source_span(CRATE_DEF_ID);
            let mut local_mod_spans = FxHashSet::default();
            local_mod_spans.insert(crate_root_span);
            let hir = tcx.hir();
            hir.for_each_module(|mod_def_id| {
                if !mod_def_id.is_top_level_module() {
                    let (mod_data, ..) = hir.get_module(mod_def_id);
                    let mod_body_span = mod_data.spans.inner_span;
                    if !crate_root_span.contains(mod_body_span)
                        && !local_mod_spans
                            .iter()
                            .any(|span| span.contains(mod_body_span))
                    {
                        local_mod_spans.insert(mod_body_span);
                    }
                }
            });

            // Checks if a diagnostic's span is local.
            let is_diagnostic_span_local = |span: &MultiSpan| {
                span.primary_spans().iter().any(|diag_span| {
                    local_mod_spans
                        .iter()
                        .any(|mod_span| mod_span.contains(diag_span.source_callsite()))
                })
            };

            // Finds and analyzes the generated entry points.
            for local_def_id in hir.body_owners() {
                let entry_point_info = utils::def_name(local_def_id, tcx)
                    .filter(|def_name| self.entry_point_names.contains(def_name.as_str()));
                if let Some(entry_point_name) = entry_point_info {
                    println!(
                        "Analyzing dispatchable: `{}` ...",
                        entry_point_name.as_str().replace(ENTRY_POINT_FN_PREFIX, "")
                    );
                    // Analyzes entry point with MIRAI body visitor.
                    // Ref: <https://github.com/facebookexperimental/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/crate_visitor.rs#L171-L194>
                    let def_id = local_def_id.to_def_id();
                    let mut diagnostics = Vec::new();
                    let mut active_calls_map: HashMap<DefId, u64> = HashMap::new();
                    let type_cache = crate_visitor.type_cache.clone();
                    let mut body_visitor = BodyVisitor::new(
                        &mut crate_visitor,
                        def_id,
                        &mut diagnostics,
                        &mut active_calls_map,
                        type_cache,
                    );
                    body_visitor.visit_body(&[]);

                    // Emit diagnostics for generated entry point (if necessary).
                    let entry_point_span = tcx.source_span(local_def_id);
                    let is_diagnostic_span_in_entry_point = |span: &MultiSpan| {
                        span.primary_spans()
                            .iter()
                            .any(|diag_span| entry_point_span.contains(diag_span.source_callsite()))
                    };
                    for mut diagnostic in diagnostics {
                        let is_primary_span_in_entry_point =
                            is_diagnostic_span_in_entry_point(&diagnostic.span);
                        let is_primary_span_local = is_diagnostic_span_local(&diagnostic.span);
                        let has_related_non_entry_point_local_sub_diagnostics = || {
                            diagnostic.children.iter().any(|sub_diagnostic| {
                                !is_diagnostic_span_in_entry_point(&sub_diagnostic.span)
                                    && is_diagnostic_span_local(&sub_diagnostic.span)
                            })
                        };
                        if (is_primary_span_in_entry_point || !is_primary_span_local)
                            && !has_related_non_entry_point_local_sub_diagnostics()
                        {
                            // Ignores diagnostics that have no relation to the user-defined local item definitions.
                            diagnostic.cancel();
                            continue;
                        }

                        // Replaces primary (autogenerated) entry point or non-local span (if any),
                        // with the first sub-diagnostic span that points to a local item definition (if any).
                        if is_primary_span_in_entry_point || !is_primary_span_local {
                            let first_local_non_entry_point_span =
                                diagnostic.children.iter().find_map(|sub_diagnostic| {
                                    if !is_diagnostic_span_in_entry_point(&sub_diagnostic.span)
                                        && is_diagnostic_span_local(&sub_diagnostic.span)
                                    {
                                        sub_diagnostic.span.primary_span()
                                    } else {
                                        None
                                    }
                                });
                            let Some(first_local_span) = first_local_non_entry_point_span else {
                                // Ignores diagnostics that have no relation to the user-defined local item definitions.
                                diagnostic.cancel();
                                continue;
                            };
                            let orig_non_local_primary_span =
                                (!is_primary_span_in_entry_point).then(|| diagnostic.span.clone());
                            diagnostic.replace_span_with(first_local_span, true);
                            diagnostic.children.retain(|sub_diagnostic| {
                                let is_first_local_span = sub_diagnostic
                                    .span
                                    .primary_span()
                                    .is_some_and(|diag_span| diag_span == first_local_span);

                                !is_first_local_span
                                    && !is_diagnostic_span_in_entry_point(&sub_diagnostic.span)
                            });
                            if let Some(orig_span) = orig_non_local_primary_span {
                                diagnostic.span_note(orig_span, "related location");
                            }
                        } else {
                            // Removes (autogenerated) entry point spans.
                            diagnostic.children.retain(|sub_diagnostic| {
                                !is_diagnostic_span_in_entry_point(&sub_diagnostic.span)
                            });
                        }
                        diagnostic.emit();
                    }
                }
            }
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
