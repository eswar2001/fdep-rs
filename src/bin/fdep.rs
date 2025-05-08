#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate fdep;

use fdep::{analyze, compile_time_sysroot};
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_interface::Queries;
use std::path::PathBuf;

struct CallgraphCallbacks {
    output_dir: Option<PathBuf>,
}

impl Callbacks for CallgraphCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(|tcx| {
            analyze(&tcx);
        });

        Compilation::Stop
    }
}

fn main() {
    let mut args: Vec<_> = std::env::args().collect();

    // Make sure we use the right default sysroot. The default sysroot is wrong,
    // because `get_or_default_sysroot` in `librustc_session` bases that on `current_exe`.
    //
    // Make sure we always call `compile_time_sysroot` as that also does some sanity-checks
    // of the environment we were built in.
    // FIXME: Ideally we'd turn a bad build env into a compile-time error via CTFE or so.
    if let Some(sysroot) = compile_time_sysroot() {
        let sysroot_flag = "--sysroot";
        if !args.iter().any(|e| e == sysroot_flag) {
            // We need to overwrite the default that librustc_session would compute.
            args.push(sysroot_flag.to_owned());
            args.push(sysroot);
        }
    }

    // Determine output directory from command-line arguments
    let output_dir = get_output_dir(&args);

    let mut calls = CallgraphCallbacks { output_dir };

    let run_compiler = rustc_driver::RunCompiler::new(&args, &mut calls);
    run_compiler.run();
}

// Helper function to determine output directory from command-line arguments
fn get_output_dir(args: &[String]) -> Option<PathBuf> {
    for (i, arg) in args.iter().enumerate() {
        if arg == "--output" || arg == "-o" {
            if i + 1 < args.len() {
                return Some(PathBuf::from(&args[i + 1]));
            }
        }

        if arg.starts_with("--output=") {
            let path = arg.split('=').nth(1)?;
            return Some(PathBuf::from(path));
        }
    }
    None
}
