use std::{env, process};

/// Shows help and version messages (and exits, if necessary).
pub fn handle_meta_args(command: &str) {
    if env::args().any(|arg| arg == "--help" || arg == "-h") {
        help(command);
        process::exit(0);
    } else if env::args().any(|arg| arg == "--version" || arg == "-V") {
        let version_info = rustc_tools_util::get_version_info!();
        println!("{version_info}");
        process::exit(0);
    }
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
