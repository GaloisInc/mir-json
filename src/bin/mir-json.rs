#![feature(rustc_private)]

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
use rustc_interface::Queries;
use rustc_interface::interface::Compiler;
use std::env;

struct MirJsonCallbacks {
    export_style: analyz::ExportStyle,
}

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
        analyz::analyze(compiler.session(), queries, self.export_style).unwrap();
        Compilation::Continue
    }
}

fn go() {
    let args: Vec<String> = std::env::args().collect();

    let export_style = if env::var("EXPORT_ALL").is_ok() {
        analyz::ExportStyle::ExportAll
    } else {
        analyz::ExportStyle::ExportCruxTests
    };

    rustc_driver::RunCompiler::new(&args, &mut MirJsonCallbacks { export_style }).run().unwrap();
}

fn main() {
    go();
}
