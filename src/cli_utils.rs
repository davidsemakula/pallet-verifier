//! Common CLI utilities.

use std::{
    env,
    ffi::OsStr,
    path::Path,
    process::{self, Command},
};

use itertools::Itertools;

/// Env var for tracking dependency renames from `Cargo.toml`.
pub const ENV_DEP_RENAMES: &str = "PALLET_VERIFIER_DEP_RENAMES";

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
        process::exit(0);
    } else if env::args().any(|arg| arg == "--version" || arg == "-V") {
        if is_rustc_wrapper_mode() {
            call_wrapped_rustc();
        } else {
            let version_info = rustc_tools_util::get_version_info!();
            println!("{version_info}");
        }
        process::exit(0);
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
        process::exit(exit_status.code().unwrap_or(-1));
    }
}

/// Checks if the argument is a `rustc` path.
pub fn is_rustc_path(arg: &str) -> bool {
    Path::new(arg)
        .file_stem()
        .is_some_and(|name| name == "rustc")
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
        return Some(value.to_string());
    }
    args.next()
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
    -h, --help     Print help
    -V, --version  Print version
"#
    );
}
