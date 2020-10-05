#![feature(rustc_private)]

extern crate rustc;
extern crate rustc_codegen_ssa;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_session;
extern crate getopts;
extern crate rustc_errors;
extern crate rustc_target;
extern crate rustc_ast;

extern crate mir_json;

use mir_json::analyz;
use rustc_driver::Compilation;
use rustc_interface::interface::Compiler;
use rustc_interface::Queries;

struct MirJsonCallbacks;

impl rustc_driver::Callbacks for MirJsonCallbacks {
    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        analyz::inject_attrs(queries);
        Compilation::Continue
    }

    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        analyz::gather_match_spans(queries);
        Compilation::Continue
    }

    /// Called after analysis. Return value instructs the compiler whether to
    /// continue the compilation afterwards (defaults to `Compilation::Continue`)
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        analyz::analyze(compiler.session(), queries).unwrap();
        Compilation::Continue
    }
}

fn go() {
    let args: Vec<String> = std::env::args().collect();

    rustc_driver::run_compiler(
        &args, // args: &[String]
        &mut MirJsonCallbacks,
        None,
        None,
    ).unwrap();
}

fn main() {
    go();
}
