//! Common CLI utilities.

use std::{
    env,
    ffi::OsStr,
    path::Path,
    process::{exit, Command},
};

use itertools::Itertools;

/// CLI arg that sets the target pointer width.
/// Ref: <https://doc.rust-lang.org/reference/conditional-compilation.html#target_pointer_width>
pub const ARG_POINTER_WIDTH: &str = "--pointer-width";
/// CLI arg that tells `pallet-verifier` to compile the `mirai-annotations` crate.
pub const ARG_COMPILE_ANNOTATIONS: &str = "--compile-annotations";
/// CLI arg that tells `pallet-verifier` whether the `mirai-annotations` dependency was auto added.
pub const ARG_AUTO_ANNOTATIONS_DEP: &str = "--auto-annotations-dep";
/// CLI arg that tells `pallet-verifier` to compile a dependency with annotations.
pub const ARG_DEP_ANNOTATE: &str = "--dep-with-annotations";
/// CLI arg that tells `pallet-verifier` to compile a dependency with some unstable features enabled.
pub const ARG_DEP_FEATURES: &str = "--dep-with-lang-features";
/// CLI arg that tells `pallet-verifier` to allow local panics in specified list of pallet hooks.
pub const ARG_ALLOW_HOOK_PANICS: &str = "--allow-hook-panics";

/// Env var for tracking dependency renames from `Cargo.toml`.
pub const ENV_DEP_RENAMES: &str = "PALLET_VERIFIER_DEP_RENAMES";
/// Env var for tracking names of optional dependency from `Cargo.toml`.
pub const ENV_OPTIONAL_DEPS: &str = "PALLET_VERIFIER_OPTIONAL_DEPS";

/// Names of pallet hook functions.
/// Ref: <https://docs.rs/frame-support/latest/frame_support/traits/trait.Hooks.html>
pub const HOOKS: [&str; 7] = [
    "on_initialize",
    "on_finalize",
    "on_idle",
    "on_poll",
    "on_runtime_upgrade",
    "offchain_worker",
    "integrity_test",
];

/// Shows help and version messages (and exits, if necessary).
///
/// **NOTE:** We let `rustc` handle help and version messages
/// if `pallet-verifier` was called as `RUSTC_WRAPPER`.
pub fn handle_meta_args(command: &str) {
    let call_wrapped_rustc = || {
        // Setting `RUSTC_WRAPPER` causes cargo to pass 'rustc' as the first argument.
        call_rustc(env::args().nth(1), env::args().skip(2));
    };
    if env::args().any(|arg| arg == "--help" || arg == "-h") {
        if is_rustc_wrapper_mode() {
            call_wrapped_rustc();
        } else {
            help(command);
        }
        exit(0);
    } else if env::args().any(|arg| arg == "--version" || arg == "-V") {
        if is_rustc_wrapper_mode() {
            call_wrapped_rustc();
        } else {
            let version_info = rustc_tools_util::get_version_info!();
            println!("{version_info}");
        }
        exit(0);
    } else if env::args().any(|arg| arg == "-vV") {
        if is_rustc_wrapper_mode() {
            call_wrapped_rustc();
        } else {
            call_rustc(None, env::args());
        }
        exit(0);
    }
}

/// Calls `rustc` (exits on failure).
pub fn call_rustc<I, S>(path: Option<String>, args: I)
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let mut cmd = rustc(path, args);
    exec_cmd(&mut cmd);
}

/// Builds `rustc` command.
pub fn rustc<I, S>(path: Option<String>, args: I) -> Command
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let mut cmd = Command::new(
        path.or_else(|| env::var("RUSTC").ok())
            .unwrap_or_else(|| "rustc".to_string()),
    );
    cmd.args(args);
    cmd
}

/// Executes command (exits on failure).
pub fn exec_cmd(cmd: &mut Command) {
    let exit_status = cmd
        .spawn()
        .expect("Failed to run cmd")
        .wait()
        .expect("Failed to wait for cmd");
    if !exit_status.success() {
        exit(exit_status.code().unwrap_or(-1));
    }
}

/// Checks if the argument is a `rustc` path.
pub fn is_rustc_path(arg: &str) -> bool {
    Path::new(arg)
        .file_stem()
        .is_some_and(|name| name == "rustc")
}

/// Returns true if the command line argument is present.
#[allow(dead_code)] // False positive.
pub fn has_arg(name: &str) -> bool {
    env::args().any(|arg| arg == name || arg.starts_with(&format!("{name}=")))
}

/// Returns a command line argument value (if any).
/// i.e. `value` in `--name value` or `--name=value`.
pub fn arg_value(name: &str) -> Option<String> {
    let mut args =
        env::args().skip_while(|arg| arg != name && !arg.starts_with(&format!("{name}=")));
    if let Some((_, value)) = args
        .next()
        .as_ref()
        .and_then(|arg| arg.splitn(2, '=').collect_tuple())
    {
        return (!value.is_empty()).then_some(value.to_string());
    }
    args.next().filter(|val| !val.is_empty())
}

/// Returns true is the CLI arg with given name is enabled
/// (i.e. set to "true", "yes", "y" or "1").
#[allow(dead_code)] // False positive.
pub fn is_arg_enabled(name: &str) -> bool {
    arg_value(name)
        .as_deref()
        .is_some_and(|val| matches!(val, "true" | "yes" | "y" | "1"))
}

/// Returns true if the `mirai-annotations` crate is already included as a dependency
/// in the original CLI args.
#[allow(dead_code)] // False positive.
pub fn has_mirai_annotations_dep() -> bool {
    env::args().enumerate().any(|(idx, arg)| {
        arg.starts_with("mirai_annotations")
            && env::args()
                .nth(idx - 1)
                .is_some_and(|arg| arg == "--extern")
    })
}

/// Returns true if the crate requires unstable features to be enabled.
pub fn requires_unstable_features(crate_name: &str) -> bool {
    matches!(
        crate_name,
        "parity_scale_codec" | "sp_panic_handler" | "sp_trie" | "sp_core" | "sp_consensus_beefy"
    )
}

/// Checks if a `rustc` path is the first CLI argument.
fn is_rustc_wrapper_mode() -> bool {
    env::args().nth(1).as_deref().is_some_and(is_rustc_path)
}

/// Shows help message.
fn help(command: &str) {
    println!(
        r#"A tool for detecting common security vulnerabilities and insecure patterns in FRAME pallets using static program analysis techniques.

Usage: {command}

Options:
    -h, --help                   Print help
    -V, --version                Print version
    --pointer-width <32|64>      The pointer width for the target execution environment
    --allow-hook-panics <list>   The hooks in which no warnings should be reported for local panics.
                                     Accepts a comma separated list from: {}
"#,
        HOOKS.map(|name| format!("`{name}`")).join(",")
    );
}
