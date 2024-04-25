//! `rustc` callbacks and utilities for analyzing FRAME pallet with MIRAI.

/// `rustc` callbacks for analyzing FRAME pallet with MIRAI.
pub struct VerifierCallbacks(mirai::callbacks::MiraiCallbacks);

impl Default for VerifierCallbacks {
    fn default() -> Self {
        let options = mirai::options::Options {
            diag_level: mirai::options::DiagLevel::Library,
            // These default to zero if not set, because they're `u64`
            max_analysis_time_for_crate: 240,
            max_analysis_time_for_body: 30,
            ..mirai::options::Options::default()
        };
        let callbacks = mirai::callbacks::MiraiCallbacks::new(options);
        Self(callbacks)
    }
}

impl rustc_driver::Callbacks for VerifierCallbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        self.0.config(config)
    }

    fn after_analysis<'tcx>(
        &mut self,
        handler: &rustc_session::EarlyErrorHandler,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        println!("Analyzing FRAME pallet with MIRAI ...");
        self.0.after_analysis(handler, compiler, queries)
    }
}
