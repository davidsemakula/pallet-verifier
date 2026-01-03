//! Compiler runner implementation.

use rustc_driver::{
    args, diagnostics_registry, handle_options, Callbacks, Compilation, DEFAULT_LOCALE_RESOURCES,
    USING_INTERNAL_FEATURES,
};
use rustc_interface::{create_and_enter_global_ctxt, interface, passes, Linker};
use rustc_session::{
    config::{self, ErrorOutputType, Input, OutFileName, OutputType},
    getopts, EarlyDiagCtxt,
};
use rustc_span::{source_map::FileLoader, FileName};

use std::{
    env,
    io::{self, Read},
    path::PathBuf,
};

/// Invokes `rustc` and returns the exit code.
///
/// # Note
///
/// Analog to [`rustc_driver::run_compiler`] but accepts a custom [`FileLoader`] and returns a status code.
pub fn run_compiler(
    at_args: &[String],
    callbacks: &mut (dyn Callbacks + Send),
    file_loader: Option<Box<dyn FileLoader + Send + Sync>>,
) -> i32 {
    rustc_driver::catch_with_exit_code(|| {
        invoke_rustc(at_args, callbacks, file_loader);
    })
}

/// Invokes `rustc`.
///
/// # Note
///
/// Mostly a copy of [`rustc_driver::run_compiler`] that allows us to set a custom [`FileLoader`],
/// and skips a few unnecessary steps for our use-case.
fn invoke_rustc(
    at_args: &[String],
    callbacks: &mut (dyn Callbacks + Send),
    file_loader: Option<Box<dyn FileLoader + Send + Sync>>,
) {
    let mut default_early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());

    // Throw away the first argument, the name of the binary.
    // In case of at_args being empty, as might be the case by
    // passing empty argument array to execve under some platforms,
    // just use an empty slice.
    //
    // This situation was possible before due to arg_expand_all being
    // called before removing the argument, enabling a crash by calling
    // the compiler with @empty_file as argv[0] and no more arguments.
    let at_args = at_args.get(1..).unwrap_or_default();

    let args = args::arg_expand_all(&default_early_dcx, at_args);

    let Some(matches) = handle_options(&default_early_dcx, &args) else {
        return;
    };

    let sopts = config::build_session_options(&mut default_early_dcx, &matches);
    let input = make_input(&default_early_dcx, &matches.free);
    let has_input = input.is_some();
    let (odir, ofile) = make_output(&matches);

    drop(default_early_dcx);

    let mut config = interface::Config {
        opts: sopts,
        crate_cfg: matches.opt_strs("cfg"),
        crate_check_cfg: matches.opt_strs("check-cfg"),
        input: input.unwrap_or(Input::File(PathBuf::new())),
        output_file: ofile,
        output_dir: odir,
        ice_file: None,
        file_loader,
        locale_resources: DEFAULT_LOCALE_RESOURCES.to_vec(),
        lint_caps: Default::default(),
        psess_created: None,
        hash_untracked_state: None,
        register_lints: None,
        override_queries: None,
        extra_symbols: Vec::new(),
        make_codegen_backend: None,
        registry: diagnostics_registry(),
        using_internal_features: &USING_INTERNAL_FEATURES,
        expanded_args: args,
    };

    callbacks.config(&mut config);

    interface::run_compiler(config, |compiler| {
        let sess = &compiler.sess;
        let codegen_backend = &*compiler.codegen_backend;

        // This is used for early exits unrelated to errors. E.g. when just
        // printing some information without compiling, or exiting immediately
        // after parsing, etc.
        let early_exit = || {
            sess.dcx().abort_if_errors();
        };

        if !has_input {
            #[allow(rustc::diagnostic_outside_of_impl)]
            sess.dcx().fatal("no input filename given"); // this is fatal
        }

        // Parse the crate root source code (doesn't parse submodules yet)
        // Everything else is parsed during macro expansion.
        let mut krate = passes::parse(sess);

        if callbacks.after_crate_root_parsing(compiler, &mut krate) == Compilation::Stop {
            return early_exit();
        }

        if sess.opts.unstable_opts.parse_crate_root_only {
            return early_exit();
        }

        let linker = create_and_enter_global_ctxt(compiler, krate, |tcx| {
            let early_exit = || {
                sess.dcx().abort_if_errors();
                None
            };

            // Make sure name resolution and macro expansion is run.
            let _ = tcx.resolver_for_lowering();

            if callbacks.after_expansion(compiler, tcx) == Compilation::Stop {
                return early_exit();
            }

            passes::write_dep_info(tcx);

            passes::write_interface(tcx);

            if sess.opts.output_types.contains_key(&OutputType::DepInfo)
                && sess.opts.output_types.len() == 1
            {
                return early_exit();
            }

            if sess.opts.unstable_opts.no_analysis {
                return early_exit();
            }

            tcx.ensure_ok().analysis(());

            if callbacks.after_analysis(compiler, tcx) == Compilation::Stop {
                return early_exit();
            }

            Some(Linker::codegen_and_build_linker(
                tcx,
                &*compiler.codegen_backend,
            ))
        });

        // Linking is done outside the `compiler.enter()` so that the
        // `GlobalCtxt` within `Queries` can be freed as early as possible.
        if let Some(linker) = linker {
            linker.link(sess, codegen_backend);
        }
    })
}

/// Extract input (string or file and optional path) from matches.
/// This handles reading from stdin if `-` is provided.
///
/// # Note
///
/// Copied as is from `rustc_driver_impl`.
#[allow(clippy::from_str_radix_10, clippy::uninlined_format_args)] // Keeps copied code unchanged.
fn make_input(early_dcx: &EarlyDiagCtxt, free_matches: &[String]) -> Option<Input> {
    match free_matches {
        [] => None, // no input: we will exit early,
        [ifile] if ifile == "-" => {
            // read from stdin as `Input::Str`
            let mut input = String::new();
            if io::stdin().read_to_string(&mut input).is_err() {
                // Immediately stop compilation if there was an issue reading
                // the input (for example if the input stream is not UTF-8).
                early_dcx
                    .early_fatal("couldn't read from stdin, as it did not contain valid UTF-8");
            }

            let name = match env::var("UNSTABLE_RUSTDOC_TEST_PATH") {
                Ok(path) => {
                    let line = env::var("UNSTABLE_RUSTDOC_TEST_LINE").expect(
                        "when UNSTABLE_RUSTDOC_TEST_PATH is set \
                                    UNSTABLE_RUSTDOC_TEST_LINE also needs to be set",
                    );
                    let line = isize::from_str_radix(&line, 10)
                        .expect("UNSTABLE_RUSTDOC_TEST_LINE needs to be an number");
                    FileName::doc_test_source_code(PathBuf::from(path), line)
                }
                Err(_) => FileName::anon_source_code(&input),
            };

            Some(Input::Str { name, input })
        }
        [ifile] => Some(Input::File(PathBuf::from(ifile))),
        [ifile1, ifile2, ..] => early_dcx.early_fatal(format!(
            "multiple input filenames provided (first two filenames are `{}` and `{}`)",
            ifile1, ifile2
        )),
    }
}

/// Extract output directory and file from matches.
///
/// # Note
///
/// Copied as is from `rustc_driver_impl`.
fn make_output(matches: &getopts::Matches) -> (Option<PathBuf>, Option<OutFileName>) {
    let odir = matches.opt_str("out-dir").map(|o| PathBuf::from(&o));
    let ofile = matches.opt_str("o").map(|o| match o.as_str() {
        "-" => OutFileName::Stdout,
        path => OutFileName::Real(PathBuf::from(path)),
    });
    (odir, ofile)
}
