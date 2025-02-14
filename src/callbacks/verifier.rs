//! `rustc` callbacks and utilities for analyzing FRAME pallet with MIRAI.

use rustc_driver::Compilation;
use rustc_errors::{Diag, DiagMessage, Level, MultiSpan, Style, Subdiag};
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_interface::interface::Compiler;
use rustc_middle::{
    query,
    ty::{AssocKind, GenericArg, ImplSubject, TyCtxt, TyKind},
};
use rustc_span::{
    def_id::{CrateNum, DefId, LocalDefId},
    ExpnData, ExpnKind, MacroKind, Span, Symbol,
};

use std::{cell::RefCell, collections::HashMap, process, rc::Rc};

use itertools::Itertools;
use mirai::{
    body_visitor::BodyVisitor, call_graph::CallGraph, constant_domain::ConstantValueCache,
    crate_visitor::CrateVisitor, known_names::KnownNamesCache, summaries::SummaryCache,
    type_visitor::TypeCache,
};
use owo_colors::OwoColorize;
use tempfile::TempDir;

use crate::{
    providers, utils, CallKind, EntrysPointInfo, CONTRACTS_MOD_NAME, ENTRY_POINT_FN_PREFIX,
};

/// `rustc` callbacks for analyzing FRAME pallet with MIRAI.
pub struct VerifierCallbacks<'compilation> {
    entry_points: &'compilation EntrysPointInfo,
    mirai_config: Option<MiraiConfig>,
    allow_hook_panics: Option<FxHashSet<String>>,
}

impl<'compilation> VerifierCallbacks<'compilation> {
    pub fn new(
        entry_points: &'compilation EntrysPointInfo,
        allow_hook_panics: Option<FxHashSet<String>>,
    ) -> Self {
        Self {
            entry_points,
            mirai_config: None,
            allow_hook_panics,
        }
    }
}

impl rustc_driver::Callbacks for VerifierCallbacks<'_> {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        // Overrides `optimized_mir` query.
        config.override_queries = Some(|_, providers| {
            providers.queries = query::Providers {
                optimized_mir: providers::optimized_mir,
                ..providers.queries
            };
        });

        // Initializes MIRAI config.
        // Ref: <https://github.com/endorlabs/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/callbacks.rs#L75-L92>
        // Ref: <https://github.com/endorlabs/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/callbacks.rs#L143-L149>
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
        // Ref: <https://github.com/endorlabs/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/options.rs#L14-L72>
        // Ref: <https://github.com/endorlabs/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/callbacks.rs#L143-L149>
        let max_time_body = 60;
        // Between 300 and 600 seconds.
        let max_time_crate = ((5 + self.entry_points.len()) * max_time_body as usize)
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

    fn after_analysis(&mut self, compiler: &Compiler, tcx: TyCtxt) -> Compilation {
        println!(
            "{} FRAME pallet with MIRAI ...",
            "Analyzing".style(utils::highlight_style())
        );
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

        // Creates MIRAI crate visitor.
        // Ref: <https://github.com/endorlabs/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/callbacks.rs#L130-L174>
        let call_graph_config = mirai_config.options.call_graph_config.to_owned();
        let mut crate_visitor = CrateVisitor {
            buffered_diagnostics: Vec::new(),
            constant_time_tag_cache: None,
            constant_time_tag_not_found: false,
            constant_value_cache: ConstantValueCache::default(),
            diagnostics_for: HashMap::new(),
            file_name: mirai_config.file_name.as_str(),
            known_names_cache: KnownNamesCache::create_cache(),
            options: &mirai_config.options,
            session: &compiler.sess,
            generic_args_cache: HashMap::new(),
            summary_cache: SummaryCache::new(mirai_config.summary_store_path.to_owned()),
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
            if tcx.item_name(mod_def_id.to_def_id()).as_str() == CONTRACTS_MOD_NAME {
                contracts_mod_def_id = Some(mod_def_id);
            } else {
                let (mod_data, mod_decl_span, mod_hir_id) = hir.get_module(mod_def_id);
                let mod_body_span = mod_data.spans.inner_span;
                if utils::has_cfg_test_attr(mod_hir_id, tcx)
                    && !test_mod_spans.iter().any(|span: &Span| {
                        span.contains(mod_decl_span) || span.contains(mod_body_span)
                    })
                {
                    test_mod_spans.insert(mod_body_span);
                }
            }
        });

        // Creates "summaries" for "contracts" (if any) with MIRAI.
        // Ref: <https://github.com/endorlabs/MIRAI/blob/main/documentation/Overview.md#summaries>
        if let Some(contracts_mod_def_id) = contracts_mod_def_id {
            println!(
                "{} summaries for FRAME and Substrate functions ...",
                "Creating".style(utils::highlight_style())
            );
            // Collect "contract" `fn` ids.
            let mut visitor = ContractsVisitor::new(tcx);
            hir.visit_item_likes_in_module(contracts_mod_def_id, &mut visitor);

            for contract_def_id in visitor.fns {
                // Analyzes "contract" with MIRAI and produces "summaries".
                let mut diagnostics = Vec::new();
                analyze(
                    contract_def_id.to_def_id(),
                    &mut crate_visitor,
                    &mut diagnostics,
                    true,
                    tcx,
                );

                // Ignores/cancels diagnostics from "contracts".
                diagnostics.into_iter().for_each(Diag::cancel);
            }
        }

        // Finds and analyzes the generated entry points.
        let mut dispatchable_entry_points = Vec::new();
        let mut hook_entry_points = Vec::new();
        let mut pub_assoc_fn_entry_points = Vec::new();
        let mut analyze_entry_points =
            |mut entry_points_info: Vec<(LocalDefId, LocalDefId, Symbol, Option<String>)>,
             call_kind: CallKind| {
                if entry_points_info.len() > 1 {
                    entry_points_info.sort_by_key(|(.., fn_name, trait_name)| {
                        (
                            trait_name.clone().unwrap_or_default(),
                            fn_name.to_ident_string(),
                        )
                    });
                }
                for (entry_point_def_id, callee_def_id, fn_name, trait_name) in entry_points_info {
                    println!(
                        "{} {call_kind}: `{}{fn_name}` ...",
                        "Analyzing".style(utils::highlight_style()),
                        trait_name
                            .map(|trait_name| format!("<Self as {trait_name}>::"))
                            .unwrap_or_default()
                    );

                    // Analyzes entry point with MIRAI and collects diagnostics.
                    let mut diagnostics = Vec::new();
                    analyze(
                        entry_point_def_id.to_def_id(),
                        &mut crate_visitor,
                        &mut diagnostics,
                        false,
                        tcx,
                    );

                    // Emit diagnostics for generated entry point (if necessary).
                    emit_diagnostics(
                        diagnostics,
                        entry_point_def_id,
                        callee_def_id,
                        tcx,
                        &test_mod_spans,
                        self.allow_hook_panics.as_ref(),
                    );
                }
            };
        for local_def_id in hir.body_owners() {
            let entry_point_info =
                tcx.opt_item_name(local_def_id.to_def_id())
                    .and_then(|def_name| {
                        self.entry_points
                            .iter()
                            .find_map(|(name, (target_hash, call_kind))| {
                                if name == def_name.as_str() {
                                    let Some(callee_def_id) =
                                        tcx.def_path_hash_to_def_id(*target_hash)
                                    else {
                                        let mut error = compiler.sess.dcx().struct_err(format!(
                                            "Couldn't find definition for {call_kind}: `{}`",
                                            def_name.as_str().replace(ENTRY_POINT_FN_PREFIX, "")
                                        ));
                                        error.note("This is most likely a bug in pallet-verifier.");
                                        error.help(
                                            "Please consider filling a bug report at \
                                        https://github.com/davidsemakula/pallet-verifier/issues",
                                        );
                                        error.emit();
                                        process::exit(rustc_driver::EXIT_FAILURE)
                                    };
                                    callee_def_id
                                        .as_local()
                                        .map(|callee_def_id| (callee_def_id, call_kind))
                                } else {
                                    None
                                }
                            })
                    });
            if let Some((callee_def_id, call_kind)) = entry_point_info {
                let fn_name = tcx.item_name(callee_def_id.to_def_id());
                let trait_name = utils::assoc_item_parent_trait(callee_def_id.to_def_id(), tcx)
                    .map(|trait_def_id| tcx.def_path_str(trait_def_id));
                let info = (local_def_id, callee_def_id, fn_name, trait_name);
                match call_kind {
                    CallKind::Dispatchable => dispatchable_entry_points.push(info),
                    CallKind::Hook => hook_entry_points.push(info),
                    CallKind::PubAssocFn => pub_assoc_fn_entry_points.push(info),
                }
            }
        }

        // Analyze dispatchables.
        if !dispatchable_entry_points.is_empty() {
            println!(
                "{} dispatchables ...",
                "Analyzing".style(utils::highlight_style())
            );
            analyze_entry_points(dispatchable_entry_points, CallKind::Dispatchable);
        }

        // Analyze hooks.
        if !hook_entry_points.is_empty() {
            println!("{} hooks ...", "Analyzing".style(utils::highlight_style()));
            analyze_entry_points(hook_entry_points, CallKind::Hook);
        }

        // Analyze pub assoc `fn`s.
        if !pub_assoc_fn_entry_points.is_empty() {
            println!(
                "{} pub assoc fns ...",
                "Analyzing".style(utils::highlight_style())
            );
            analyze_entry_points(pub_assoc_fn_entry_points, CallKind::PubAssocFn);
        }

        // Outputs call graph.
        crate_visitor.call_graph.output();

        // Continue compilation.
        Compilation::Continue
    }
}

/// MIRAI configuration.
/// Ref: <https://github.com/endorlabs/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/callbacks.rs#L29-L39>
struct MiraiConfig {
    // MIRAI options.
    // Ref: <https://github.com/endorlabs/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/options.rs#L74-L86>
    options: mirai::options::Options,
    /// The relative path of the file being analyzed.
    file_name: String,
    /// A path to the directory where the summary cache should be stored.
    // Ref: <https://github.com/endorlabs/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/callbacks.rs#L144-L149>
    summary_store_path: String,
}

// Analyzes `fn` `DefId` with MIRAI.
//
// i.e. Runs the abstract interpreter over the function body and produce a summary of its effects and collect any diagnostics.
//
// Ref: <https://github.com/endorlabs/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/crate_visitor.rs#L126-L127>
// Ref: <https://github.com/endorlabs/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/crate_visitor.rs#L171-L194>
fn analyze<'analysis, 'tcx>(
    def_id: DefId,
    crate_visitor: &mut CrateVisitor<'analysis, 'tcx>,
    diagnostics: &mut Vec<Diag<'analysis, ()>>,
    is_contract: bool,
    tcx: TyCtxt<'tcx>,
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
        // Ref: <https://github.com/endorlabs/MIRAI/blob/a94a8c77a453e1d2365b39aa638a4f5e6b1d4dc3/checker/src/crate_visitor.rs#L184-L191>
        crate_visitor
            .summary_cache
            .set_summary_for(def_id, tcx, summary);
    }
}

/// Emit diagnostics for generated entry point (if necessary).
fn emit_diagnostics(
    diagnostics: Vec<Diag<()>>,
    entry_point_def_id: LocalDefId,
    callee_def_id: LocalDefId,
    tcx: TyCtxt,
    test_mod_spans: &FxHashSet<Span>,
    allow_hook_panics: Option<&FxHashSet<String>>,
) {
    let source_map = tcx.sess.source_map();
    let is_span_local = |mspan: &MultiSpan| {
        mspan
            .primary_span()
            .and_then(|span| source_map.span_to_location_info(span.source_callsite()).0)
            .is_some_and(|source_file| source_file.cnum == LOCAL_CRATE)
    };
    let entry_point_span = tcx.source_span(entry_point_def_id);
    let is_span_in_entry_point = |mspan: &MultiSpan| {
        mspan
            .primary_spans()
            .iter()
            .any(|diag_span| entry_point_span.contains(diag_span.source_callsite()))
    };
    let is_span_from_expansion = |mspan: &MultiSpan| {
        mspan
            .primary_spans()
            .iter()
            .any(|span| span.from_expansion())
    };
    let is_span_in_cfg_test_mod = |mspan: &MultiSpan| {
        mspan.primary_spans().iter().any(|span| {
            test_mod_spans
                .iter()
                .any(|mod_span| mod_span.contains(span.source_callsite()))
        })
    };
    // Checks if diagnostic arises from FRAME, substrate and other "core" crates
    // (i.e. substrate primitive/`sp_*` libraries, `frame_support`, `frame_system`,
    // SCALE codec libraries e.t.c).
    let is_span_in_frame_substrate_core = |mspan: &MultiSpan| {
        let is_core_crate = |crate_num: CrateNum| {
            let crate_symbol = tcx.crate_name(crate_num);
            let crate_name = crate_symbol.as_str();
            crate_name.starts_with("sp_")
                || matches!(
                    crate_name,
                    "frame_support"
                        | "frame_system"
                        | "parity_scale_codec"
                        | "scale_info"
                        | "wasmi"
                )
                || crate_name.starts_with("frame_support_")
                || crate_name.starts_with("frame_system_")
                || crate_name.starts_with("parity_scale_codec_")
                || crate_name.starts_with("scale_info_")
                || crate_name.starts_with("wasmi_")
        };
        mspan.primary_span().is_some_and(|span| {
            if let (Some(source_file), ..) = source_map.span_to_location_info(span) {
                if is_core_crate(source_file.cnum) {
                    return true;
                }
            }
            if span.from_expansion() {
                if let Some(macro_def_id) = span.ctxt().outer_expn_data().macro_def_id {
                    return is_core_crate(macro_def_id.krate);
                }
            }
            false
        })
    };
    // Checks if diagnostic arises from `DispatchError` `From::from` conversion implementation via
    // the `#[pallet::error]` macro.
    let is_span_from_dispatch_error_from_impl = |mspan: &MultiSpan| {
        mspan.primary_span().is_some_and(|span| {
            // Handles local `#[pallet::error]` definitions.
            let is_in_local_pallet_error = span
                .parent()
                .and_then(|parent_local_def_id| {
                    tcx.opt_associated_item(parent_local_def_id.to_def_id())
                })
                .is_some_and(|assoc_item| {
                    let is_core_convert_from_impl = assoc_item.name.as_str() == "from"
                        && assoc_item.kind == AssocKind::Fn
                        && assoc_item
                            .trait_item_def_id
                            .is_some_and(|trait_item_def_id| {
                                let crate_name = tcx.crate_name(trait_item_def_id.krate);
                                let trait_def_id = tcx
                                    .trait_of_item(trait_item_def_id)
                                    .expect("Expected a trait `DefId`");
                                let trait_name = tcx.item_name(trait_def_id);
                                matches!(crate_name.as_str(), "core" | "std")
                                    && trait_name.as_str() == "From"
                            });
                    let is_dispatch_error_impl =
                        assoc_item.impl_container(tcx).is_some_and(|impl_def_id| {
                            let impl_subject = tcx.impl_subject(impl_def_id).skip_binder();
                            if let ImplSubject::Trait(trait_ref) = impl_subject {
                                trait_ref.self_ty().ty_adt_def().is_some_and(|adt_def| {
                                    let adt_def_id = adt_def.did();
                                    let crate_name = tcx.crate_name(adt_def_id.krate);
                                    let adt_name = tcx.item_name(adt_def_id);
                                    crate_name.as_str() == "sp_runtime"
                                        && adt_name.as_str() == "DispatchError"
                                })
                            } else {
                                false
                            }
                        });
                    is_core_convert_from_impl && is_dispatch_error_impl
                });
            // Handles foreign `#[pallet::error]` definitions.
            let is_in_foreign_pallet_error = || {
                source_map.span_to_snippet(span).is_ok_and(|snippet| {
                    snippet == "error"
                        && source_map
                            .span_to_snippet(source_map.span_extend_to_line(span))
                            .is_ok_and(|mut line_snippet| {
                                line_snippet.retain(|c| !c.is_whitespace());
                                line_snippet.contains("#[pallet::error")
                            })
                })
            };
            is_in_local_pallet_error || is_in_foreign_pallet_error()
        })
    };
    // Checks if diagnostic arises from FRAME storage definition.
    let is_span_from_frame_storage_def = |mspan: &MultiSpan| {
        mspan.primary_span().is_some_and(|span| {
            // Handles local `#[pallet::storage]` definitions.
            let is_in_local_pallet_storage = span.parent().is_some_and(|local_def_id| {
                tcx.impl_of_method(local_def_id.to_def_id())
                    .is_some_and(|impl_def_id| {
                        let impl_subject = tcx.impl_subject(impl_def_id).skip_binder();
                        let self_ty = match impl_subject {
                            ImplSubject::Trait(trait_ref) => {
                                let trait_def_id = trait_ref.def_id;
                                let is_frame_storage_trait =
                                    tcx.crate_name(trait_def_id.krate).as_str() == "frame_support"
                                        && tcx.item_name(trait_def_id).as_str().contains("Storage");
                                is_frame_storage_trait.then_some(trait_ref.self_ty())
                            }
                            ImplSubject::Inherent(self_ty) => Some(self_ty),
                        };
                        self_ty.is_some_and(|self_ty| {
                            if let TyKind::Adt(adt_def, gen_args) = self_ty.kind() {
                                if utils::is_storage_prefix(adt_def.did(), tcx) {
                                    return true;
                                }

                                let prefix_ty_arg =
                                    gen_args.iter().filter_map(GenericArg::as_type).next();
                                let prefix_adt_def = prefix_ty_arg
                                    .and_then(|prefix_ty_arg| prefix_ty_arg.ty_adt_def());
                                let is_storage_prefix = prefix_adt_def.is_some_and(|adt_def| {
                                    utils::is_storage_prefix(adt_def.did(), tcx)
                                });
                                return is_storage_prefix
                                    || utils::includes_query_type(gen_args, tcx);
                            };
                            false
                        })
                    })
            });
            // Handles foreign `#[pallet::storage]` definitions.
            let is_in_foreign_pallet_storage = || {
                source_map.span_to_snippet(span).is_ok_and(|snippet| {
                    snippet == "storage"
                        && source_map
                            .span_to_snippet(source_map.span_extend_to_line(span))
                            .is_ok_and(|mut line_snippet| {
                                line_snippet.retain(|c| !c.is_whitespace());
                                line_snippet.contains("#[pallet::storage")
                            })
                })
            };
            is_in_local_pallet_storage || is_in_foreign_pallet_storage()
        })
    };
    // Checks if diagnostic arises from generated code for `##[pallet::pallet]` annotated struct.
    let is_span_from_pallet_struct = |mspan: &MultiSpan| {
        mspan.primary_span().is_some_and(|span| {
            // Handles local `#[pallet::pallet]` definitions.
            let is_in_local_pallet_pallet = span.parent().is_some_and(|local_def_id| {
                tcx.impl_of_method(local_def_id.to_def_id())
                    .is_some_and(|impl_def_id| {
                        let impl_subject = tcx.impl_subject(impl_def_id).skip_binder();
                        if let ImplSubject::Trait(trait_ref) = impl_subject {
                            let trait_def_id = trait_ref.def_id;
                            let is_pallet_trait = tcx.crate_name(trait_def_id.krate).as_str()
                                == "frame_support"
                                && tcx.item_name(trait_def_id).as_str().contains("Pallet");
                            if is_pallet_trait {
                                let self_ty = trait_ref.self_ty();
                                if let Some(adt_def) = self_ty.ty_adt_def() {
                                    let adt_name = tcx.item_name(adt_def.did());
                                    return adt_name.as_str() == "Pallet";
                                }
                            }
                        }

                        false
                    })
            });
            // Handles foreign `#[pallet::pallet]` definitions.
            let is_in_foreign_pallet_pallet = || {
                source_map.span_to_snippet(span).is_ok_and(|snippet| {
                    snippet == "pallet"
                        && source_map
                            .span_to_snippet(source_map.span_extend_to_line(span))
                            .is_ok_and(|mut line_snippet| {
                                line_snippet.retain(|c| !c.is_whitespace());
                                line_snippet.contains("#[pallet::pallet")
                            })
                })
            };
            is_in_local_pallet_pallet || is_in_foreign_pallet_pallet()
        })
    };
    // Checks if the callee `DefId` is an assoc fn of the `frame_support::traits::Hooks` impl.
    let is_hooks_impl_callee = || {
        let impl_def_id = tcx.impl_of_method(callee_def_id.to_def_id());
        let trait_def_id = impl_def_id.and_then(|impl_def_id| tcx.trait_id_of_impl(impl_def_id));
        trait_def_id.is_some_and(|trait_def_id| {
            let crate_name = tcx.crate_name(trait_def_id.krate);
            let trait_name = tcx.item_name(trait_def_id);
            crate_name.as_str() == "frame_support" && trait_name.as_str() == "Hooks"
        })
    };
    let callee_name = tcx.item_name(callee_def_id.to_def_id());
    // Checks if span points to a panicking macro (expect `unimplemented!`).
    let is_panicking_macro_except_unimpl = |mspan: &MultiSpan| {
        mspan.primary_span().is_some_and(|span| {
            let macro_name = |expn_data: ExpnData| match expn_data.kind {
                ExpnKind::Macro(MacroKind::Bang, symbol) => Some(symbol),
                _ => None,
            };
            let is_unimplemented = span.macro_backtrace().any(|expn_data| {
                macro_name(expn_data).is_some_and(|name| name.as_str() == "unimplemented")
            });
            if is_unimplemented {
                return false;
            }
            span.macro_backtrace().any(|expn_data| {
                macro_name(expn_data).is_some_and(|name| {
                    matches!(
                        name.as_str(),
                        "panic" | "assert" | "assert_eq" | "assert_ne" | "unreachable"
                    ) || name.as_str().starts_with("$crate::panic::")
                })
            })
        })
    };
    // Checks if span points to an `Result::expect` or `Option::expect`.
    let is_result_or_opt_expect = |mspan: &MultiSpan| {
        mspan.primary_span().is_some_and(|span| {
            source_map.span_to_snippet(span).is_ok_and(|snippet| {
                if let (Some(source_file), ..) = source_map.span_to_location_info(span) {
                    let crate_name = tcx.crate_name(source_file.cnum);
                    let file_name = source_file.name.prefer_local().to_string();
                    if matches!(crate_name.as_str(), "core" | "std") {
                        // Handles `Option::expect`.
                        if file_name.ends_with("/option.rs")
                            && snippet.starts_with("expect_failed(")
                        {
                            return true;
                        }

                        // Handles `Result::expect`.
                        // NOTE: For both `Result::expect` and `Result::unwrap` call `unwrap_failed(..)`,
                        // however `Result::unwrap` passes in a string literal as the `msg` arg,
                        // while `Result::expect` passes a variable.
                        if file_name.ends_with("/result.rs")
                            && snippet.starts_with("unwrap_failed(")
                            && !snippet.starts_with("unwrap_failed(\"")
                        {
                            return true;
                        }
                    }
                }

                false
            })
        })
    };
    // Returns the crate name for the given span.
    let span_crate_name = |mspan: &MultiSpan| {
        mspan.primary_span().and_then(|span| {
            source_map
                .span_to_location_info(span)
                .0
                .map(|source_file| tcx.crate_name(source_file.cnum))
        })
    };
    // Checks if span points to the (slice) `iterator!` macro from the std/core crate.
    let is_span_from_std_iterator_macro = |mspan: &MultiSpan| {
        span_crate_name(mspan).is_some_and(|name| matches!(name.as_str(), "std" | "core"))
            && mspan.primary_span().is_some_and(|span| {
                span.macro_backtrace()
                    .any(|expn_data| match expn_data.kind {
                        ExpnKind::Macro(MacroKind::Bang, symbol) => symbol.as_str() == "iterator",
                        _ => false,
                    })
            })
    };

    for mut diagnostic in diagnostics {
        // Ignores direct calls to panicking macros (i.e. `panic!`, `assert!`, `unreachable!` e.t.c
        // - except `unimplemented!`) and `Option/Result::expect` calls for either the
        // `integrity_test` hook (default) or any hooks specified by the `allow_hook_panics` arg.
        let last_mspan = diagnostic
            .children
            .last()
            .map(|sub_diag| &sub_diag.span)
            .unwrap_or_else(|| &diagnostic.span);
        let is_hook_allowed_to_panic = allow_hook_panics
            .is_some_and(|hooks| hooks.contains(callee_name.as_str()))
            || (allow_hook_panics.is_none() && callee_name.as_str() == "integrity_test");
        let is_penultimate_span_local = || {
            if !diagnostic.children.is_empty() {
                let penultimate_mspan = diagnostic
                    .children
                    .get(diagnostic.children.len() - 2)
                    .map(|sub_diag| &sub_diag.span)
                    .unwrap_or_else(|| &diagnostic.span);
                return is_span_local(penultimate_mspan);
            }
            false
        };
        if is_hook_allowed_to_panic
            && is_hooks_impl_callee()
            && ((is_panicking_macro_except_unimpl(last_mspan) && is_span_local(last_mspan))
                || (is_result_or_opt_expect(last_mspan) && is_penultimate_span_local()))
        {
            diagnostic.cancel();
            continue;
        }

        // Ignores noisy diagnostics about foreign functions with missing MIR bodies, incomplete analysis e.t.c.
        // Also ignores `mirai_annotations::assume!` related diagnostics because those are likely
        // from our analysis code.
        // Ref: <https://github.com/endorlabs/MIRAI/blob/main/documentation/Overview.md#foreign-functions>
        // Ref: <https://github.com/endorlabs/MIRAI/blob/main/documentation/Overview.md#incomplete-analysis>
        let is_noisy = diagnostic
            .messages
            .first()
            .and_then(|(msg, _)| msg.as_str())
            .is_some_and(|msg| {
                let is_missing_mir = || {
                    msg.contains("MIR body")
                        && (msg.contains("without") || msg.contains("did not resolve"))
                };
                // `-Cdebug-assertions=no` doesn't remove debug asserts from pre-compiled crates.
                let is_debug_assert = || {
                    msg.contains("assert")
                        && diagnostic.span.primary_span().is_some_and(|span| {
                            source_map
                                .span_to_snippet(span.source_callsite())
                                .is_ok_and(|snippet| {
                                    snippet.contains("debug_assert!")
                                        || snippet.contains("debug_assert_eq!")
                                        || snippet.contains("debug_assert_ne!")
                                })
                        })
                };
                let is_truthy_assume = || {
                    msg.contains("assumption")
                        && (msg.contains("provably true") || msg.contains("provably false"))
                };
                let is_unreachable_assume = || {
                    msg.contains("unreachable")
                        && msg.contains("mark it")
                        && msg.contains("verify_unreachable!")
                };
                let is_pointer_alloc_issue = || {
                    msg.contains("pointer") && msg.contains("memory") && msg.contains("deallocated")
                };
                let is_from_std = || {
                    diagnostic.children.iter().any(|sub_diag| {
                        sub_diag.span.primary_span().is_some_and(|span| {
                            source_map
                                .span_to_location_info(span)
                                .0
                                .is_some_and(|source_file| {
                                    matches!(
                                        tcx.crate_name(source_file.cnum).as_str(),
                                        "std" | "core" | "alloc"
                                    )
                                })
                        })
                    })
                };
                let is_arg_validity_related = || {
                    let is_in_fn_like_macro = || {
                        diagnostic.span.primary_span().is_some_and(|span| {
                            source_map.span_to_snippet(span).is_ok_and(|snippet| {
                                snippet
                                    .splitn(2, "!(")
                                    .collect_tuple()
                                    .is_some_and(|(name, _)| {
                                        !name.chars().any(|c| !c.is_alphanumeric() && c != '_')
                                    })
                            })
                        })
                    };
                    (msg.contains("invalid args") || msg.contains("dummy argument"))
                        && (is_from_std() || is_in_fn_like_macro())
                };
                // More targeted replacement for disabled MIRAI unreachable! panic suppression.
                // Ref: <https://github.com/davidsemakula/MIRAI/commit/64d9f234a4be09f793d146594096b4d6377d969e>
                let is_std_internal_unreachable = || {
                    msg.contains("internal error:")
                        && msg.contains("entered unreachable")
                        && is_from_std()
                };
                is_missing_mir()
                    || msg.contains("incomplete analysis")
                    || is_debug_assert()
                    || is_truthy_assume()
                    || is_unreachable_assume()
                    || is_pointer_alloc_issue()
                    || is_arg_validity_related()
                    || is_std_internal_unreachable()
            });
        if is_noisy {
            diagnostic.cancel();
            continue;
        }

        // Ignores diagnostics that either have no relation to user-defined local item definitions,
        // or arise from FRAME and substrate "core" crates (i.e. substrate primitive/`sp_*` libraries,
        // `frame_support` and `frame_system` pallets, and SCALE codec libraries) or test-only code.
        let relevant_spans: Vec<_> = std::iter::once(diagnostic.span.clone())
            .chain(
                diagnostic
                    .children
                    .iter()
                    .map(|sub_diag| sub_diag.span.clone()),
            )
            .skip_while(|span| {
                !is_span_local(span)
                    || (is_span_from_expansion(span) && is_span_in_frame_substrate_core(span))
                    || is_span_in_entry_point(span)
            })
            .collect();
        if relevant_spans.is_empty()
            || relevant_spans.iter().any(|mspan| {
                is_span_from_dispatch_error_from_impl(mspan) || is_span_in_cfg_test_mod(mspan)
            })
            || relevant_spans
                .iter()
                .rev()
                .take_while_inclusive(|mspan| !is_span_local(mspan))
                .any(|mspan| {
                    is_span_in_frame_substrate_core(mspan)
                        || is_span_from_frame_storage_def(mspan)
                        || is_span_from_pallet_struct(mspan)
                })
        {
            diagnostic.cancel();
            continue;
        }

        // Ignores warnings about overflows rooted in the (slice) `iterator!` macro from std/core crate.
        let is_overflow_msg = diagnostic
            .messages
            .first()
            .and_then(|(msg, _)| msg.as_str())
            .is_some_and(|msg| msg.contains("overflow"));
        let is_rooted_in_iterator_macro = || {
            relevant_spans
                .iter()
                .rev()
                .take_while(|mspan| {
                    span_crate_name(mspan)
                        .is_some_and(|name| matches!(name.as_str(), "std" | "core" | "alloc"))
                })
                .any(is_span_from_std_iterator_macro)
        };
        if is_overflow_msg && is_rooted_in_iterator_macro() {
            diagnostic.cancel();
            continue;
        }

        // Sanitizes diagnostic messages and updates diagnostic to only include relevant sub-diagnostics.
        let sanitized_msgs = diagnostic
            .messages
            .iter()
            .map(|(msg, style)| {
                let new_msg = msg
                    .as_str()
                    .map(|text| {
                        let new_text = text
                            .strip_prefix("[MIRAI]")
                            .unwrap_or(text)
                            .trim()
                            .to_string();
                        DiagMessage::from(new_text)
                    })
                    .unwrap_or_else(|| msg.clone());
                (new_msg, *style)
            })
            .collect();
        diagnostic.messages = sanitized_msgs;
        if let Some((first_local_span, child_spans)) = relevant_spans.split_first() {
            if let Some(first_local_span) = first_local_span.primary_span() {
                diagnostic.replace_span_with(first_local_span, true);
                diagnostic.children = child_spans
                    .iter()
                    .map(|span| Subdiag {
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
