//! `rustc` callbacks and utilities for analyzing FRAME pallet with MIRAI.

use rustc_driver::Compilation;
use rustc_hash::FxHashMap;
use rustc_interface::interface::Compiler;
use rustc_span::def_id::DefId;

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use mirai::{
    body_visitor::BodyVisitor, call_graph::CallGraph, constant_domain::ConstantValueCache,
    crate_visitor::CrateVisitor, known_names::KnownNamesCache, summaries::PersistentSummaryCache,
    type_visitor::TypeCache,
};
use tempfile::TempDir;

use super::utils;

/// `rustc` callbacks for analyzing FRAME pallet with MIRAI.
pub struct VerifierCallbacks<'compilation> {
    // Map of generated entry point `fn` names to dispatchable function `DefId`s.
    entry_points_info: &'compilation FxHashMap<&'compilation str, DefId>,
    // MIRAI configuration.
    mirai_config: Option<MiraiConfig>,
}

impl<'compilation> VerifierCallbacks<'compilation> {
    pub fn new(entry_points_info: &'compilation FxHashMap<&'compilation str, DefId>) -> Self {
        Self {
            entry_points_info,
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
        let options = mirai::options::Options {
            diag_level: mirai::options::DiagLevel::Library,
            // These default to zero if not set, because they're `u64`.
            max_analysis_time_for_crate: 240,
            max_analysis_time_for_body: 30,
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
        _handler: &rustc_session::EarlyErrorHandler,
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

            for local_def_id in tcx.hir().body_owners() {
                let entry_point_info = utils::def_name(local_def_id, tcx).and_then(|def_name| {
                    self.entry_points_info
                        .iter()
                        .find_map(|(name, dispatchable_def_id)| {
                            (*name == def_name.as_str()).then_some((def_name, dispatchable_def_id))
                        })
                });
                if let Some((entry_point_name, dispatchable_def_id)) = entry_point_info {
                    let dispatchable_local_def_id = dispatchable_def_id
                        .as_local()
                        .expect("Expected local definition for dispatchable function");
                    println!(
                        "Analyzing dispatchable: `{}` ...",
                        utils::def_name(dispatchable_local_def_id, tcx).unwrap_or(entry_point_name)
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
                    //
                    // NOTE: Replaces primary (autogenerated) entry point span (if any),
                    // with the first sub-diagnostic span that points to the dispatchable function (if any).
                    // Also ignores/cancels diagnostics that *only* point to generated entry point locations,
                    // and have no relation to the user-defined target dispatchable function.
                    let entry_point_span = tcx.source_span(local_def_id);
                    let dispatchable_span = tcx.source_span(dispatchable_local_def_id);
                    for mut diagnostic in diagnostics {
                        let is_in_entry_point = diagnostic
                            .span
                            .primary_span()
                            .is_some_and(|span| entry_point_span.contains(span));
                        if is_in_entry_point {
                            let first_dispatchable_span =
                                diagnostic.children.iter().find_map(|child| {
                                    child.span.primary_span().filter(|span| {
                                        dispatchable_span.contains(span.source_callsite())
                                    })
                                });
                            let Some(first_dispatchable_span) = first_dispatchable_span else {
                                diagnostic.cancel();
                                continue;
                            };
                            diagnostic.replace_span_with(first_dispatchable_span, true);
                            diagnostic.children.retain(|child| {
                                !child.span.primary_span().is_some_and(|span| {
                                    span.source_callsite() == first_dispatchable_span
                                })
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
