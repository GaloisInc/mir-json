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
extern crate rustc_middle;

extern crate mir_json;

use mir_json::analyz;
use rustc_ast::Crate;
use rustc_driver::Compilation;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use std::env;

extern crate log;
extern crate env_logger;

struct MirJsonCallbacks {
    export_style: analyz::ExportStyle,
}

impl rustc_driver::Callbacks for MirJsonCallbacks {
    fn after_crate_root_parsing(
        &mut self,
        _compiler: &Compiler,
        krate: &mut Crate,
    ) -> Compilation {
        analyz::inject_attrs(krate);
        Compilation::Continue
    }

    /// Called after analysis. Return value instructs the compiler whether to
    /// continue the compilation afterwards (defaults to `Compilation::Continue`)
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        tcx: TyCtxt<'tcx>
    ) -> Compilation {
        analyz::analyze(tcx, self.export_style).unwrap();
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

    rustc_driver::run_compiler(&args, &mut MirJsonCallbacks { export_style });
}

fn main() {
    env_logger::init();
    go();
}
