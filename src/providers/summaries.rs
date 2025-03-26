//! Common utilities and helpers for dynamically generating specialized "contracts"
//! used to "summarize" calls that require knowledge of the calling context.

use rustc_hash::FxHashSet;
use rustc_middle::ty::{GenericArgsRef, TyCtxt};
use rustc_span::def_id::DefId;

use crate::utils;

/// Env var for tracking target calls for specialized summaries.
pub const ENV_SUMMARY_TARGETS_PREFIX: &str = "PALLET_VERIFIER_SUMMARY_TARGETS";

/// Convenience type alias for string representations of a set of target calls
/// which require specialized summaries.
///
/// **NOTE:** Each element is a tuple of a callee's def hash
/// and a stringified representation of generic args.
pub type SummaryTargetInfo = FxHashSet<(String, String)>;

/// Adds specialized summary target call.
pub fn add_summary_target<'tcx>(
    caller_def_id: DefId,
    callee_def_id: DefId,
    callee_gen_args: GenericArgsRef<'tcx>,
    tcx: TyCtxt<'tcx>,
) {
    // Retrieves existing callee info for caller.
    let mut summary_target_info = find_summary_targets(caller_def_id, tcx).unwrap_or_default();

    // Adds new callee info.
    let caller_def_hash = utils::def_hash_str(caller_def_id, tcx);
    let callee_def_hash = utils::def_hash_str(callee_def_id, tcx);
    let callee_gen_args_key =
        mirai::utils::argument_types_key_str(tcx, Some(callee_gen_args)).to_string();
    summary_target_info.insert((callee_def_hash, callee_gen_args_key));
    let summary_target_info_json = serde_json::to_string(&summary_target_info)
        .expect("Expected serialized `SummaryTargetInfo`");
    // SAFETY: `pallet-verifier` is single-threaded.
    let env_key = summary_targets_env_key(&caller_def_hash);
    std::env::set_var(env_key, summary_target_info_json);
}

/// Retrieves specialized summary target calls (if any).
pub fn find_summary_targets(caller_def_id: DefId, tcx: TyCtxt) -> Option<SummaryTargetInfo> {
    // SAFETY: `pallet-verifier` is single-threaded.
    let caller_def_hash = utils::def_hash_str(caller_def_id, tcx);
    let env_key = summary_targets_env_key(&caller_def_hash);
    let summary_target_info_json = std::env::var(env_key).ok()?;
    let summary_target_info: SummaryTargetInfo =
        serde_json::from_str(&summary_target_info_json).ok()?;
    Some(summary_target_info)
}

/// Returns a env key for the given def hash.
fn summary_targets_env_key(def_hash: &str) -> String {
    format!("{ENV_SUMMARY_TARGETS_PREFIX}_{def_hash}")
}
