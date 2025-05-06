#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate serde;
extern crate serde_json;
// extern crate walkdir;
// extern crate anyhow;
extern crate thiserror;

use crate::rustc_span::Pos;
use anyhow::{Context, Result};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::Res;
use rustc_hir::intravisit::{self, walk_expr, walk_item, Visitor};
use rustc_hir::{BodyId, Expr, ExprKind, HirId, Item, ItemKind, Pat, PatKind, QPath};
use rustc_interface::{interface, Config};
use rustc_middle::ty::*;
use rustc_span::Span;
use serde::Serialize;
use std::collections::{HashMap, HashSet};
use std::ffi::OsStr;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, process};
use thiserror::Error;
use walkdir::WalkDir;

mod analysis;
use analysis::*;

// Helper function to find the sysroot
fn find_sysroot() -> Result<String, Box<dyn std::error::Error>> {
    let rustc = env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let output = Command::new(rustc).arg("--print=sysroot").output()?;

    if !output.status.success() {
        return Err("Failed to find sysroot".into());
    }

    let sysroot = String::from_utf8(output.stdout)?.trim().to_string();

    Ok(sysroot)
}

struct FunctionAnalyzer {
    output_dir: PathBuf,
}

impl Callbacks for FunctionAnalyzer {
    fn config(&mut self, config: &mut Config) {
        // Configure the compiler to stop after analysis
        // Modern rustc API configuration
        config.opts.cg.codegen_units = Some(0); // This disables codegen
    }
    // fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
    //     // Iterate over the top-level items in the crate, looking for the main function.
    //     for id in tcx.hir_free_items() {
    //         let item = &tcx.hir_item(id);
    //         // Use pattern-matching to find a specific node inside the main function.
    //         if let rustc_hir::ItemKind::Fn { body, .. } = item.kind {
    //             let expr = &tcx.hir_body(body).value;
    //             if let rustc_hir::ExprKind::Block(block, _) = expr.kind {
    //                 if let rustc_hir::StmtKind::Let(let_stmt) = block.stmts[0].kind {
    //                     if let Some(expr) = let_stmt.init {
    //                         let hir_id = expr.hir_id; // hir_id identifies the string "Hello, world!"
    //                         let def_id = item.hir_id().owner.def_id; // def_id identifies the main function
    //                         let ty = tcx.typeck(def_id).node_type(hir_id);
    //                         println!("{expr:#?}: {ty:?}");
    //                     }
    //                 }
    //             }
    //         }
    //     }

    //     Compilation::Stop
    // }
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'_>,
    ) -> Compilation {
        // Access the compiler object and run our analysis
        // let result = compiler.global_ctxt().unwrap().take();
        // result.enter(|tcx| {
        let mut collector = Collector::new(tcx);

        // Visit all crates and their items
        for item_id in tcx.hir_free_items() {
            collector.analyze_item(tcx.hir_item(item_id));
        }

        // Group functions by source file
        let mut file_to_functions: HashMap<String, Vec<Function>> = HashMap::new();

        for function in &collector.functions {
            // Extract file path from src_location (assumes format like "path/to/file.rs:line:col-line:col")
            if let Some(file_path) = function.src_location.split(':').next() {
                file_to_functions
                    .entry(file_path.to_string())
                    .or_default()
                    .push(function.clone());
            }
        }

        // Create output directories mirroring the project structure
        for (file_path, functions) in &file_to_functions {
            // Create output path that mirrors the source file structure
            let path = PathBuf::from(file_path);
            let file_name = path.file_name().unwrap_or_default().to_string_lossy();
            let parent_path = path.parent().unwrap_or_else(|| std::path::Path::new(""));

            // Create the output directory structure
            let output_file_dir = self.output_dir.join(parent_path);
            fs::create_dir_all(&output_file_dir)
                .expect("Could not create output directory structure");

            // Write JSON for this file
            let json_name = format!("{}.json", file_name.replace(".rs", ""));
            let json_path = output_file_dir.join(json_name);

            let json = serde_json::to_string_pretty(&functions).unwrap();
            fs::write(&json_path, json)
                .expect(&format!("Could not write JSON for file {}", file_path));

            println!("Created: {}", json_path.display());
        }

        // Also write the complete functions list
        let all_json_path = self.output_dir.join("all_functions.json");
        let all_json = serde_json::to_string_pretty(&collector.functions).unwrap();
        fs::write(&all_json_path, all_json).expect("Could not write complete functions JSON");
        // });

        Compilation::Stop
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: <path_to_rust_project>");
        process::exit(1);
    }

    let file_path = &args[1];
    // let path = Path::new(project_path);

    // if !path.is_dir() {
    //     eprintln!("Error: The specified path is not a directory.");
    //     process::exit(1);
    // }

    // Create an output directory if it doesn't exist
    let output_dir = PathBuf::from("function_analysis");
    fs::create_dir_all(&output_dir)?;

    // Collect all .rs files in the directory tree
    // let mut rust_files = Vec::new();
    // for entry in WalkDir::new(path).into_iter().filter_map(|e| e.ok()) {
    //     let entry_path = entry.path();
    //     if entry_path.extension() == Some(OsStr::new("rs")) {
    //         rust_files.push(entry_path.to_path_buf());
    //     }
    // }

    // if rust_files.is_empty() {
    //     eprintln!("No Rust files found in the specified directory.");
    //     process::exit(1);
    // }

    // Get the sysroot for rustc
    let sysroot = find_sysroot()?;
    println!("{:#?}",sysroot);
    // for file in rust_files {
    //     let file_path = file.to_string_lossy().to_string();
    //     println!("Analyzing file: {}", file_path);

        // Prepare arguments for each file
        let compiler_args = vec![
            "fdep-rust".to_string(),
            file_path.clone(),
            // "--sysroot".to_string(),
            // sysroot.clone(),
        ];

        // Add any additional rustc arguments you need
        // compiler_args.push("-Zunpretty=expanded".to_string()); // Example to expand macros

        // Run the compiler with custom callbacks for each file
        rustc_driver::run_compiler(
            &compiler_args,
            &mut FunctionAnalyzer {
                output_dir: output_dir.clone(),
            },
        );
    // }

    println!(
        "Analysis complete! Output saved to: {}",
        output_dir.display()
    );
    Ok(())
}
