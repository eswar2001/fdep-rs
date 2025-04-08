#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_hir::{intravisit, ItemKind};
use rustc_interface::Queries;
use rustc_span::Pos;
use std::env;

struct AstPrinter;

impl Callbacks for AstPrinter {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        println!("Traversing and printing the AST...");
        
        // Use borrow() instead of take()
        queries.global_ctxt().unwrap().borrow().enter(|tcx| {
            // Get the HIR (High-level IR)
            let hir = tcx.hir();
            let krate = hir.root_module();
            
            // Create visitor
            let mut visitor = PrintVisitor { tcx };
            
            // Visit the root module (instead of walk_crate)
            intravisit::walk_mod(&mut visitor, krate, hir.local_def_id_to_hir_id(rustc_hir::def_id::CRATE_DEF_ID));
        });
        
        Compilation::Continue
    }
}

struct PrintVisitor<'tcx> {
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
}

impl<'tcx> intravisit::Visitor<'tcx> for PrintVisitor<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> rustc_middle::hir::map::Map<'tcx> {
        self.tcx.hir()
    }
    
    fn visit_item(&mut self, item: &'tcx rustc_hir::Item<'tcx>) {
        // Print item information
        println!("Item: {} (kind: {:?})", item.ident, item.kind.descr());
        
        let def_id = item.owner_id.def_id.to_def_id();
        println!("  DefId: {:?}", def_id);
        println!("  Path: {}", self.tcx.def_path_str(def_id));
        
        // If it's a function, print its type
        if let ItemKind::Fn(..) = item.kind {
            // Get the function type
            let fn_type = self.tcx.type_of(def_id).instantiate_identity();
            println!("  Type: {:?}", fn_type);
            
            // Skip getting typeck results for main function
            if item.ident.as_str() == "main" {
                println!("  Type-checked information:");
                println!("    Return type: <skipped for main function to avoid ICE>");
            } else {
                // Try to safely print type-checked info for non-main functions
                println!("  Type-checked information:");
                
                // Get typeck results without calling node_type() directly
                // let typeck = self.tcx.typeck(item.owner_id.def_id);
                
                // For return type, infer it from the fn_type instead of using node_type
                if let rustc_middle::ty::TyKind::FnDef(_, _) = fn_type.kind() {
                    let fn_sig = fn_type.fn_sig(self.tcx);
                    let return_ty = fn_sig.output();
                    println!("    Return type: {:?}", return_ty);
                } else {
                    println!("    Return type: <cannot determine from type>");
                }
            }
        }
        
        // Get source location
        let source_map = self.tcx.sess.source_map();
        let span = item.span;
        if !span.is_dummy() {
            let loc = source_map.lookup_char_pos(span.lo());
            let end_loc = source_map.lookup_char_pos(span.hi());
            println!("  Location: {:?}:{}:{}-{}:{}",
                     loc.file.name,
                     loc.line,
                     loc.col.to_usize(),
                     end_loc.line,
                     end_loc.col.to_usize());
        }
        
        println!();
        
        // Continue visiting the item's contents
        intravisit::walk_item(self, item);
    }
    
    fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
        // Print expression information
        println!("Expression (kind: {:?})", expr.kind);
        
        // Check if we're in the main function to avoid ICE
        let owner_id = self.tcx.hir().enclosing_body_owner(expr.hir_id);
        let owner_hir_id = self.tcx.hir().local_def_id_to_hir_id(owner_id);
        
        // Safely check owner item without assuming it's always an item
        let in_main_function = if let Some(owner_node) = self.tcx.hir().find(owner_hir_id) {
            match owner_node {
                rustc_hir::Node::Item(item) => item.ident.as_str() == "main",
                _ => false
            }
        } else {
            false
        };
        
        // Skip detailed type checking for expressions in main function
        if in_main_function {
            println!("  <skipping type information for expressions in main function>");
            intravisit::walk_expr(self, expr);
            return;
        }
        
        // For non-main functions, we can safely use typeck_body
        let typeck_body_id = self.tcx.hir().body_owned_by(owner_id);
        
        // Use a match to handle potential errors safely
        let typeck = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.tcx.typeck_body(typeck_body_id)
        })) {
            Ok(typeck) => typeck,
            Err(_) => {
                println!("  Could not get type information for this expression");
                // Continue visiting the expression even if we can't get type info
                intravisit::walk_expr(self, expr);
                return;
            }
        };
        
        // If it's a function call, print more details
        match &expr.kind {
            rustc_hir::ExprKind::Call(func, args) => {
                println!("  Function call with {} arguments", args.len());
                
                // Try to resolve the called function
                if let Some(def_id) = typeck.type_dependent_def_id(func.hir_id) {
                    println!("  Called function: {}", self.tcx.def_path_str(def_id));
                    println!("  Function type: {:?}", self.tcx.type_of(def_id).instantiate_identity());
                }
            },
            rustc_hir::ExprKind::MethodCall(path_segment, receiver, args, _) => {
                println!("  Method call: {} with {} arguments", path_segment.ident, args.len());
                
                // Get receiver type safely
                match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    typeck.expr_ty(receiver)
                })) {
                    Ok(receiver_ty) => println!("  Receiver type: {:?}", receiver_ty),
                    Err(_) => println!("  Receiver type: <unavailable>")
                }
                
                // Try to resolve the method
                if let Some(def_id) = typeck.type_dependent_def_id(expr.hir_id) {
                    println!("  Method: {}", self.tcx.def_path_str(def_id));
                    println!("  Method type: {:?}", self.tcx.type_of(def_id).instantiate_identity());
                }
            },
            _ => {}
        }
        
        // Get expression type safely
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            typeck.expr_ty(expr)
        })) {
            Ok(expr_ty) => println!("  Expression type: {:?}", expr_ty),
            Err(_) => println!("  Expression type: <unavailable>")
        }
        
        // Continue visiting the expression
        intravisit::walk_expr(self, expr);
    }
}

fn main() {
    // Get command line arguments
    let args: Vec<String> = env::args().collect();
    
    // Add required arguments for the compiler
    let mut rustc_args = args.clone();
    
    // Add sysroot if not present
    if !rustc_args.iter().any(|arg| arg == "--sysroot") {
        // Try to get sysroot from rustc
        let sysroot = std::process::Command::new("rustc")
            .arg("--print")
            .arg("sysroot")
            .output()
            .ok()
            .and_then(|output| String::from_utf8(output.stdout).ok())
            .map(|s| s.trim().to_string());
        
        if let Some(sysroot) = sysroot {
            rustc_args.push("--sysroot".to_string());
            rustc_args.push(sysroot);
        }
    }
    
    // Set the RUSTC_BOOTSTRAP environment variable to use unstable features
    env::set_var("RUSTC_BOOTSTRAP", "1");
    
    println!("Running Rust compiler with arguments: {:?}", rustc_args);
    
    // Create our callback
    let mut callback = AstPrinter;
    
    // Run the compiler with our callbacks
    let compiler = RunCompiler::new(&rustc_args, &mut callback);
    match compiler.run() {
        Ok(_) => println!("AST traversal complete"),
        Err(e) => eprintln!("Compiler error: {:?}", e),
    }
}