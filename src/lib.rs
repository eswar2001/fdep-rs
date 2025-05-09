#![feature(rustc_private)]

extern crate cargo_metadata;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_version;
extern crate serde;
extern crate serde_json;

use rustc_middle::ty::TyCtxt;
use std::env;
use std::fs;
use std::path::PathBuf;

mod visitor;

/// Returns the "default sysroot" that Callgraph will use if no `--sysroot` flag is set.
/// Should be a compile-time constant.
pub fn compile_time_sysroot() -> Option<String> {
    // option_env! is replaced to a constant at compile time
    if option_env!("RUSTC_STAGE").is_some() {
        // This is being built as part of rustc, and gets shipped with rustup.
        // We can rely on the sysroot computation in librustc.
        return None;
    }

    // For builds outside rustc, we need to ensure that we got a sysroot
    // that gets used as a default. The sysroot computation in librustc would
    // end up somewhere in the build dir.
    // Taken from PR <https://github.com/Manishearth/rust-clippy/pull/911>.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    Some(match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect(
                "To build Callgraph without rustup, set the `RUST_SYSROOT` env var at build time",
            )
            .to_owned(),
    })
}

pub fn analyze<'tcx>(tcx: &TyCtxt<'tcx>) {
    // Try to determine output directory from command-line arguments
    let output_dir = get_output_dir().unwrap_or_else(|| PathBuf::from("fdep_output"));

    // Create output directory if it doesn't exist
    fs::create_dir_all(&output_dir).expect("Failed to create output directory");

    // Initialize visitor with output directory
    let mut visitor = visitor::CallgraphVisitor::with_output_dir(&tcx, output_dir);

    // Visit all items in the crate
    tcx.hir().visit_all_item_likes_in_crate(&mut visitor);

    // Dump collected data
    visitor.dump();

}

// Helper function to determine output directory from command-line arguments
fn get_output_dir() -> Option<PathBuf> {
    let args: Vec<String> = env::args().collect();
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
