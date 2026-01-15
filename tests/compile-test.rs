//! Test runner for [UI tests](https://rustc-dev-guide.rust-lang.org/tests/ui.html).

extern crate mirai_annotations;

use std::{
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
};

use ui_test::{Args, Config, Format, OutputConflictHandling, status_emitter::Text};

/// Runs all ui tests.
fn main() -> ui_test::color_eyre::Result<()> {
    ui_driver()?;
    ui_cargo("tests/ui/cargo")?;
    ui_cargo("tests/ui/sdk")
}

/// Runs ui tests for direct calls to the rustc driver binary (i.e. without cargo).
fn ui_driver() -> ui_test::color_eyre::Result<()> {
    let mut config = Config::rustc("tests/ui/driver");
    generic_config(&mut config, "pallet-verifier", true);
    ui_test::run_tests(config)
}

/// Runs ui tests with cargo subcommand (i.e. `cargo verify-pallet`).
fn ui_cargo(dir: &str) -> ui_test::color_eyre::Result<()> {
    let mut config = Config::cargo(dir);
    let sub_cmd = OsString::from("verify-pallet");
    match config.program.args.first_mut() {
        Some(arg) => *arg = sub_cmd,
        None => config.program.args.push(sub_cmd),
    }
    generic_config(&mut config, "cargo-verify-pallet", false);
    ui_test::run_tests_generic(
        vec![config],
        |path, config| {
            path.file_name()
                .is_some_and(|name| name == "Cargo.toml")
                .then(|| ui_test::default_any_file_filter(path, config))
        },
        |_, _| {},
        Text::from(Format::Pretty),
    )
}

/// Sets low-level options and flags shared across test suites.
fn generic_config(config: &mut Config, cmd: &str, is_rustc_wrapper: bool) {
    // Fails on mismatches.
    config.output_conflict_handling = OutputConflictHandling::Error;
    // Sets command to pallet-verifier.
    let exec_path = env::current_exe().expect("Expected valid compiletest executable path");
    let deps_path = exec_path
        .parent()
        .expect("Expected valid parent for compiletest executable");
    let target_path = deps_path.parent().expect("Expected valid target path");
    let mut path = target_path.join(cmd);
    if cfg!(target_os = "windows") {
        path.set_extension("exe");
    }
    config.program.program = path;
    // Sets UI test friendly rustc args.
    let flags = [
        "-Zui-testing",
        "-Aunused",
        "-Adeprecated",
        "-Anonstandard_style",
    ];
    if is_rustc_wrapper {
        config.program.args.extend(flags.map(OsString::from));
        let mut exec_dep_info_path = exec_path.clone();
        exec_dep_info_path.set_extension("d");
        let exec_dep_info =
            fs::read_to_string(&exec_dep_info_path).expect("Expected test dependencies info");
        let mirai_annotations_path = exec_dep_info.lines().find_map(|line| {
            if !line.starts_with(char::is_whitespace) && !line.is_empty() {
                let path_str = line.strip_suffix(':')?;
                let path = Path::new(path_str);
                let filename = path.file_stem()?.to_str()?;
                let ext = path.extension()?;
                if filename.starts_with("libmirai_annotations") && ext == "rlib" {
                    return Some(path);
                }
            }
            None
        });
        if let Some(mirai_annotations_path) = mirai_annotations_path {
            config.program.args.extend([
                "--extern".into(),
                format!("mirai_annotations={}", mirai_annotations_path.display()).into(),
            ]);
        }
    } else {
        config
            .program
            .envs
            .push(("RUSTFLAGS".into(), Some(flags.join(" ").into())));
        config
            .fill_host_and_target()
            .expect("Expected valid host and target triples");
    }
    // Sets output directory.
    let out_dir = env::var("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            env::current_dir()
                .expect("Expected valid current dir")
                .join("target")
        })
        .join("ui_test");
    config.out_dir = out_dir;
    // Sets UI test to simply compare stderr to output files.
    config.comment_defaults.base().require_annotations = None.into();
    config.comment_defaults.base().exit_status = None.into();
    // Sets bless arg/config based on env var.
    let mut args = Args::test().unwrap();
    args.bless |= env::var("PALLET_VERIFIER_BLESS")
        .is_ok_and(|val| matches!(val.as_str(), "true" | "yes" | "y" | "1"));
    // Disable color for `pallet-verifier` output.
    config
        .program
        .envs
        .push(("PALLET_VERIFIER_NO_COLOR".into(), Some("true".into())));
    config.with_args(&args);
}
