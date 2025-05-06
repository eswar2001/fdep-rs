#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_session;
extern crate serde;

use crate::rustc_span::Pos;
use rustc_hir::intravisit;
use rustc_ast as ast;
use rustc_ast::TyKind::Infer;
use rustc_hir::def::Res;
use rustc_hir::intravisit::*;
use rustc_hir::AmbigArg;
use rustc_hir::{BodyId, Expr, ExprKind, HirId, Item, ItemKind, Pat, PatKind, QPath};
use rustc_middle::ty::*;
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use serde::Serialize;

#[derive(Debug, Serialize, Clone, PartialEq, Eq, Hash)]
pub struct TypeOriginInfo {
    pub type_name: String,
    pub crate_name: String,
    pub module_path: String,
    pub generic_args: Vec<TypeOriginInfo>,
    pub is_generic_param: bool,
    pub src_location: String,
}

#[derive(Debug, Serialize, Clone)]
pub struct LiteralInfo {
    pub value: String,
    pub literal_type: String,
    pub span: String,
    pub line_number: usize,
    pub column_number: usize,
}

#[derive(Debug, Serialize, Clone)]
pub struct CalledFunctionInfo {
    pub name: String,
    pub fully_qualified_path: String,
    pub is_method: bool,
    pub receiver_type: Option<TypeOriginInfo>,
    pub input_types: Vec<TypeOriginInfo>,
    pub output_types: Vec<TypeOriginInfo>,
    pub src_location: String,
    pub line_number: usize,
    pub column_number: usize,
    pub origin_crate: String,
    pub origin_module: String,
    pub call_type: String, // "function", "method", "macro", etc.
}

#[derive(Debug, Serialize, Clone)]
pub struct Function {
    pub name: String,
    pub fully_qualified_path: String,
    pub is_method: bool,
    pub self_type: Option<TypeOriginInfo>,
    pub input_types: Vec<TypeOriginInfo>,
    pub output_types: Vec<TypeOriginInfo>,
    pub types_used: Vec<TypeOriginInfo>,
    pub literals_used: Vec<LiteralInfo>,
    pub functions_called: Vec<CalledFunctionInfo>,
    pub methods_called: Vec<CalledFunctionInfo>,
    pub where_functions: HashMap<String, Function>,
    pub src_location: String,
    pub src_code: String,
    pub line_number_start: usize,
    pub line_number_end: usize,
    pub crate_name: String,
    pub module_path: String,
    pub visibility: String,
    pub doc_comments: String,
    pub attributes: Vec<String>,
}

pub struct Collector<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub functions: Vec<Function>,
    pub curr_module_path: Vec<String>,
}

impl<'tcx> Collector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            functions: vec![],
            curr_module_path: vec![],
        }
    }

    pub fn push_module(&mut self, name: String) {
        self.curr_module_path.push(name);
    }

    pub fn pop_module(&mut self) {
        self.curr_module_path.pop();
    }

    pub fn current_module_path(&self) -> String {
        self.curr_module_path.join("::")
    }

    pub fn get_attrs_string(&self, hir_id: HirId) -> Vec<String> {
        let attrs = self
            .tcx
            .get_attrs(hir_id.owner.to_def_id(), rustc_span::sym::TyCtxt);
        attrs.map(|attr| format!("{:?}", attr)).collect()
    }

    pub fn extract_doc_comments(&self, hir_id: HirId) -> String {
        let attrs = self
            .tcx
            .get_attrs(hir_id.owner.to_def_id(), rustc_span::sym::TyCtxt);
        let mut doc_comments = String::new();

        for attr in attrs {
            if attr.has_name(rustc_span::Symbol::intern("doc")) {
                if let Some(doc) = attr.value_str() {
                    if !doc_comments.is_empty() {
                        doc_comments.push('\n');
                    }
                    doc_comments.push_str(&doc.to_string());
                }
            }
        }
        doc_comments
    }

    pub fn extract_visibility(&self, owner_id: rustc_hir::OwnerId) -> String {
        // In newer Rust versions, visibility is accessed differently
        match self.tcx.visibility(owner_id.to_def_id()) {
            Visibility::Public => "pub".to_string(),
            Visibility::Restricted(def_id) => {
                let path = self.tcx.def_path_str(def_id);
                format!("pub({})", path)
            }
        }
    }

    pub fn format_span(&self, span: Span) -> String {
        let lo = self.tcx.sess.source_map().lookup_char_pos(span.lo());
        let hi = self.tcx.sess.source_map().lookup_char_pos(span.hi());
        format!(
            "{}:{}:{}-{}:{}",
            format!("{:?}", lo.file.name),
            lo.line,
            lo.col.to_usize(),
            hi.line,
            hi.col.to_usize()
        )
    }

    pub fn get_line_number(&self, span: Span) -> usize {
        self.tcx.sess.source_map().lookup_char_pos(span.lo()).line
    }

    pub fn get_column_number(&self, span: Span) -> usize {
        self.tcx
            .sess
            .source_map()
            .lookup_char_pos(span.lo())
            .col
            .to_usize()
    }
    // &'tcx Item<'tcx>
    pub fn analyze_item(&mut self, item: &'tcx Item<'tcx>) {
        match &item.kind {
            ItemKind::Fn {
                ident,
                sig,
                generics,
                body,
                has_body,
            } => {
                self.process_function(item, sig, *body);
            }
            ItemKind::Mod(_, module) => {
                let def_id = item.owner_id.to_def_id();
                let module_name = self.tcx.item_name(def_id).to_string();
                self.push_module(module_name);
                // Process items in the module
                for item_id in module.item_ids {
                    let child_item = self.tcx.hir_item(*item_id);
                    self.analyze_item(child_item);
                }

                self.pop_module();
            }
            ItemKind::Impl(impl_) => {
                // Process impl methods
                for impl_item_ref in impl_.items {
                    // Fix: Use the correct method to access impl items
                    if let rustc_hir::ImplItemKind::Fn(sig, body_id) =
                        &self.tcx.hir_impl_item(impl_item_ref.id).kind
                    {
                        let impl_item = self.tcx.hir_impl_item(impl_item_ref.id);
                        self.process_impl_method(impl_item, sig, *body_id, impl_.self_ty);
                    }
                }
            }
            _ => {}
        }
    }

    pub fn process_function(
        &mut self,
        item: &rustc_hir::Item<'tcx>,
        sig: &rustc_hir::FnSig<'tcx>,
        body_id: BodyId,
    ) {
        let def_id = item.owner_id.to_def_id();
        let fn_name = self.tcx.item_name(def_id).to_string();
        let crate_name = self.tcx.crate_name(def_id.krate).to_string();
        let module_path = self.current_module_path();
        let fully_qualified_path = if module_path.is_empty() {
            format!("{}::{}", crate_name, fn_name)
        } else {
            format!("{}::{}::{}", crate_name, module_path, fn_name)
        };

        let span = item.span;
        let src_loc = self.format_span(span);
        let src_code = self
            .tcx
            .sess
            .source_map()
            .span_to_snippet(span)
            .unwrap_or_else(|_| "<<source unavailable>>".to_string());

        let line_start = self.get_line_number(span);
        let line_end = self.tcx.sess.source_map().lookup_char_pos(span.hi()).line;

        // Determine if this is a method (has self parameter)
        let is_method = false; // Functions defined directly in modules are not methods
        let self_type = None;

        // Extract function inputs
        let mut input_types = Vec::new();
        for param in sig.decl.inputs.iter() {
            if let Some(type_info) = self.extract_type_origin_info(param) {
                input_types.push(type_info);
            }
        }

        // Extract function outputs
        let mut output_types = Vec::new();
        if let rustc_hir::FnRetTy::Return(ty) = &sig.decl.output {
            if let Some(type_info) = self.extract_type_origin_info(ty) {
                output_types.push(type_info);
            }
        } else {
            // Add unit type for default return
            output_types.push(TypeOriginInfo {
                type_name: "()".to_string(),
                crate_name: "core".to_string(),
                module_path: "primitive".to_string(),
                generic_args: Vec::new(),
                is_generic_param: false,
                src_location: "".to_string(),
            });
        }
        // self.tcx.get_attrs(hir_id.owner.to_def_id(),rustc_span::sym::TyCtxt)
        let body = self.tcx.hir_body(body_id);

        // Collect function calls, method calls, literals, and types used
        let (functions_called, methods_called, types_used, literals_used, where_functions) =
            self.analyze_body(body);

        // Extract visibility, doc comments, and attributes
        let visibility = self.extract_visibility(item.owner_id);
        let doc_comments = self.extract_doc_comments(item.hir_id());
        let attributes = self.get_attrs_string(item.hir_id());

        // Build function info
        let function_info = Function {
            name: fn_name,
            fully_qualified_path,
            is_method,
            self_type,
            input_types,
            output_types,
            types_used,
            literals_used,
            functions_called,
            methods_called,
            where_functions,
            src_location: src_loc,
            src_code,
            line_number_start: line_start,
            line_number_end: line_end,
            crate_name,
            module_path,
            visibility,
            doc_comments,
            attributes,
        };

        self.functions.push(function_info);
    }

    pub fn process_impl_method(
        &mut self,
        impl_item: &'tcx rustc_hir::ImplItem<'tcx>,
        sig: &rustc_hir::FnSig<'tcx>,
        body_id: BodyId,
        self_ty: &'tcx rustc_hir::Ty<'tcx>,
    ) {
        let def_id = impl_item.owner_id.to_def_id();
        let fn_name = impl_item.ident.to_string();
        let crate_name = self.tcx.crate_name(def_id.krate).to_string();
        let module_path = self.current_module_path();

        // Extract the self type info
        let self_type_info = self.extract_type_origin_info(self_ty);

        let self_type_name = if let Some(ref type_info) = self_type_info {
            type_info.type_name.clone()
        } else {
            "Unknown".to_string()
        };

        let fully_qualified_path = if module_path.is_empty() {
            format!("{}::{}::{}", crate_name, self_type_name, fn_name)
        } else {
            format!(
                "{}::{}::{}::{}",
                crate_name, module_path, self_type_name, fn_name
            )
        };

        let span = impl_item.span;
        let src_loc = self.format_span(span);
        let src_code = self
            .tcx
            .sess
            .source_map()
            .span_to_snippet(span)
            .unwrap_or_else(|_| "<<source unavailable>>".to_string());

        let line_start = self.get_line_number(span);
        let line_end = self.tcx.sess.source_map().lookup_char_pos(span.hi()).line;

        // Determine if this is a method by checking for a self parameter
        let is_method = sig.decl.inputs.len() > 0
            && {
                let body = self.tcx.hir_body(body_id);
                let first_param = &body.params[0];
                matches!(first_param.pat.kind, PatKind::Binding(_, _, ident, _) if ident.name.to_string() == "self")
            };

        // Extract function inputs (skip self for methods when collecting input_types)
        let mut input_types = Vec::new();
        let inputs_to_process = if is_method {
            sig.decl.inputs.iter().skip(1).collect::<Vec<_>>()
        } else {
            sig.decl.inputs.iter().collect::<Vec<_>>()
        };

        for param in inputs_to_process {
            if let Some(type_info) = self.extract_type_origin_info(param) {
                input_types.push(type_info);
            }
        }

        // Extract function outputs
        let mut output_types = Vec::new();
        if let rustc_hir::FnRetTy::Return(ty) = &sig.decl.output {
            if let Some(type_info) = self.extract_type_origin_info(ty) {
                output_types.push(type_info);
            }
        } else {
            // Add unit type for default return
            output_types.push(TypeOriginInfo {
                type_name: "()".to_string(),
                crate_name: "core".to_string(),
                module_path: "primitive".to_string(),
                generic_args: Vec::new(),
                is_generic_param: false,
                src_location: "".to_string(),
            });
        }

        let body = self.tcx.hir_body(body_id);

        // Collect function calls, method calls, literals, and types used
        let (functions_called, methods_called, types_used, literals_used, where_functions) =
            self.analyze_body(body);

        // Extract visibility, doc comments, and attributes
        let visibility = self.extract_visibility(impl_item.owner_id);
        let doc_comments = self.extract_doc_comments(impl_item.hir_id());
        let attributes = self.get_attrs_string(impl_item.hir_id());

        // Build function info
        let function_info = Function {
            name: fn_name,
            fully_qualified_path,
            is_method,
            self_type: self_type_info,
            input_types,
            output_types,
            types_used,
            literals_used,
            functions_called,
            methods_called,
            where_functions,
            src_location: src_loc,
            src_code,
            line_number_start: line_start,
            line_number_end: line_end,
            crate_name,
            module_path,
            visibility,
            doc_comments,
            attributes,
        };

        self.functions.push(function_info);
    }

    pub fn analyze_body(
        &self,
        body: &'tcx rustc_hir::Body<'tcx>,
    ) -> (
        Vec<CalledFunctionInfo>,
        Vec<CalledFunctionInfo>,
        Vec<TypeOriginInfo>,
        Vec<LiteralInfo>,
        HashMap<String, Function>,
    ) {
        struct BodyCollector<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            functions_called: Vec<CalledFunctionInfo>,
            methods_called: Vec<CalledFunctionInfo>,
            types_used: HashSet<TypeOriginInfo>,
            literals_used: Vec<LiteralInfo>,
            where_functions: HashMap<String, Function>,
            closure_count: usize,
            parent_collector: &'a Collector<'tcx>,
        }

        impl<'a, 'tcx> Visitor<'tcx> for BodyCollector<'a, 'tcx> {
            fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
                let def_id = expr.hir_id.owner.to_def_id();
                // let typeck = self.tcx.typeck(def_id);
                let typeck = if def_id.is_local() {
                    // Convert to LocalDefId for typeck
                    self.tcx.typeck(def_id.as_local().unwrap())
                } else {
                    // For non-local definitions, you might need to handle differently
                    panic!("Cannot perform type checking on non-local definitions")
                    // Or find an alternative approach for non-local defs
                };
                let expr_ty = typeck.expr_ty(expr);

                // Add the expression type to types_used
                if let Some(type_info) = self
                    .parent_collector
                    .extract_type_origin_info_from_ty(expr_ty)
                {
                    self.types_used.insert(type_info);
                }

                match &expr.kind {
                    // Function calls
                    ExprKind::Call(func, args) => {
                        if let ExprKind::Path(qpath) = &func.kind {
                            let res = typeck.qpath_res(qpath, func.hir_id);

                            if let Some(def_id) = res.opt_def_id() {
                                let fn_name = self.tcx.def_path_str(def_id);
                                let span = func.span;

                                // Extract origin information
                                let crate_name = self.tcx.crate_name(def_id.krate).to_string();
                                let def_path = self.tcx.def_path(def_id);
                                let module_path = def_path
                                    .data
                                    .iter()
                                    .take(def_path.data.len().saturating_sub(1))
                                    .map(|x| x.data.to_string())
                                    .collect::<Vec<_>>()
                                    .join("::");

                                // Get function inputs/outputs
                                let mut input_types = Vec::new();
                                let mut output_types = Vec::new();

                                let fn_ty = self.tcx.type_of(def_id).skip_binder();
                                if let TyKind::FnDef(_, _) = fn_ty.kind() {
                                    let fn_sig = self.tcx.fn_sig(def_id);
                                    let sig = fn_sig.skip_binder();

                                    // Get input types
                                    for arg_ty in sig.inputs().iter() {
                                        if let Some(type_info) = self
                                            .parent_collector
                                            .extract_type_origin_info_from_ty(*arg_ty.skip_binder())
                                        {
                                            input_types.push(type_info);
                                        }
                                    }

                                    // Get output type
                                    if let Some(output_info) =
                                        self.parent_collector.extract_type_origin_info_from_ty(
                                            sig.output().skip_binder(),
                                        )
                                    {
                                        output_types.push(output_info);
                                    }
                                }

                                let name =
                                    fn_name.split("::").last().unwrap_or(&fn_name).to_string();

                                self.functions_called.push(CalledFunctionInfo {
                                    name,
                                    fully_qualified_path: fn_name,
                                    is_method: false,
                                    receiver_type: None,
                                    input_types,
                                    output_types,
                                    src_location: self.parent_collector.format_span(span),
                                    line_number: self.parent_collector.get_line_number(span),
                                    column_number: self.parent_collector.get_column_number(span),
                                    origin_crate: crate_name,
                                    origin_module: module_path,
                                    call_type: "function".to_string(),
                                });
                            }
                        }
                    }

                    // Method calls
                    ExprKind::MethodCall(path, receiver, args, span) => {
                        let method_name = path.ident.to_string();
                        let span = path.ident.span;

                        // Get receiver type
                        let receiver_ty = typeck.expr_ty(receiver);
                        let receiver_type = self
                            .parent_collector
                            .extract_type_origin_info_from_ty(receiver_ty);

                        // Get method definition
                        if let Some(def_id) = typeck.type_dependent_def_id(expr.hir_id) {
                            let method_full_name = self.tcx.def_path_str(def_id);

                            // Extract origin information
                            let crate_name = self.tcx.crate_name(def_id.krate).to_string();
                            let def_path = self.tcx.def_path(def_id);
                            let module_path = def_path
                                .data
                                .iter()
                                .take(def_path.data.len().saturating_sub(1))
                                .map(|x| x.data.to_string())
                                .collect::<Vec<_>>()
                                .join("::");

                            // Get method inputs/outputs
                            let mut input_types = Vec::new();
                            let mut output_types = Vec::new();

                            let fn_ty = self.tcx.type_of(def_id).skip_binder();
                            if let TyKind::FnDef(_, _) = fn_ty.kind() {
                                let fn_sig = self.tcx.fn_sig(def_id);
                                let sig = fn_sig.skip_binder();

                                // Skip the first input (self)
                                for arg_ty in sig.inputs().iter().skip(1) {
                                    if let Some(type_info) = self
                                        .parent_collector
                                        .extract_type_origin_info_from_ty(*arg_ty.skip_binder())
                                    {
                                        input_types.push(type_info);
                                    }
                                }

                                // Get output type
                                if let Some(output_info) = self
                                    .parent_collector
                                    .extract_type_origin_info_from_ty(sig.output().skip_binder())
                                {
                                    output_types.push(output_info);
                                }
                            }

                            self.methods_called.push(CalledFunctionInfo {
                                name: method_name,
                                fully_qualified_path: method_full_name,
                                is_method: true,
                                receiver_type,
                                input_types,
                                output_types,
                                src_location: self.parent_collector.format_span(span),
                                line_number: self.parent_collector.get_line_number(span),
                                column_number: self.parent_collector.get_column_number(span),
                                origin_crate: crate_name,
                                origin_module: module_path,
                                call_type: "method".to_string(),
                            });
                        }
                    }

                    // Literals
                    ExprKind::Lit(lit) => {
                        let span = lit.span;
                        let lit_value = self
                            .tcx
                            .sess
                            .source_map()
                            .span_to_snippet(span)
                            .unwrap_or_else(|_| "<<literal value unavailable>>".to_string());

                        let lit_type = match expr_ty.kind() {
                            TyKind::Int(_) => "integer".to_string(),
                            TyKind::Uint(_) => "unsigned integer".to_string(),
                            TyKind::Float(_) => "float".to_string(),
                            TyKind::Bool => "boolean".to_string(),
                            TyKind::Char => "char".to_string(),
                            TyKind::Str => "string".to_string(),
                            _ => format!("{:?}", expr_ty.kind()),
                        };

                        self.literals_used.push(LiteralInfo {
                            value: lit_value,
                            literal_type: lit_type,
                            span: self.parent_collector.format_span(span),
                            line_number: self.parent_collector.get_line_number(span),
                            column_number: self.parent_collector.get_column_number(span),
                        });
                    }

                    // Closures
                    ExprKind::Closure(&rustc_hir::Closure { body, .. }) => {
                        self.closure_count += 1;
                        let closure_name = format!("closure_{}", self.closure_count);

                        let body = self.tcx.hir_body(body);
                        let closure_ty = typeck.expr_ty(expr);

                        let mut child_collector = BodyCollector {
                            tcx: self.tcx,
                            functions_called: Vec::new(),
                            methods_called: Vec::new(),
                            types_used: HashSet::new(),
                            literals_used: Vec::new(),
                            where_functions: HashMap::new(),
                            closure_count: 0,
                            parent_collector: self.parent_collector,
                        };

                        child_collector.visit_expr(&body.value);

                        // Build inputs/outputs
                        let mut input_types = Vec::new();
                        let mut output_types = Vec::new();

                        if let TyKind::Closure(def_id, substs) = closure_ty.kind() {
                            let closure_sig = substs.as_closure().sig();
                            let sig = closure_sig.skip_binder();

                            // Get input types
                            for arg_ty in sig.inputs().iter() {
                                if let Some(type_info) = self
                                    .parent_collector
                                    .extract_type_origin_info_from_ty(*arg_ty)
                                {
                                    input_types.push(type_info);
                                }
                            }

                            // Get output type
                            if let Some(output_info) = self
                                .parent_collector
                                .extract_type_origin_info_from_ty(sig.output())
                            {
                                output_types.push(output_info);
                            }
                        }

                        let span = expr.span;
                        let closure_src = self
                            .tcx
                            .sess
                            .source_map()
                            .span_to_snippet(span)
                            .unwrap_or_else(|_| "<<closure source unavailable>>".to_string());

                        let line_start = self.parent_collector.get_line_number(span);
                        let line_end = self.tcx.sess.source_map().lookup_char_pos(span.hi()).line;

                        let closure_info = Function {
                            name: closure_name.clone(),
                            fully_qualified_path: closure_name.clone(),
                            is_method: false,
                            self_type: None,
                            input_types,
                            output_types,
                            types_used: child_collector.types_used.into_iter().collect(),
                            literals_used: child_collector.literals_used,
                            functions_called: child_collector.functions_called,
                            methods_called: child_collector.methods_called,
                            where_functions: child_collector.where_functions,
                            src_location: self.parent_collector.format_span(span),
                            src_code: closure_src,
                            line_number_start: line_start,
                            line_number_end: line_end,
                            crate_name: "local".to_string(),
                            module_path: "closure".to_string(),
                            visibility: "private".to_string(),
                            doc_comments: "".to_string(),
                            attributes: Vec::new(),
                        };

                        self.where_functions.insert(closure_name, closure_info);
                    }

                    _ => {}
                }

                // Recursively visit child expressions
                walk_expr(self, expr);
            }
        }

        let mut collector = BodyCollector {
            tcx: self.tcx,
            functions_called: Vec::new(),
            methods_called: Vec::new(),
            types_used: HashSet::new(),
            literals_used: Vec::new(),
            where_functions: HashMap::new(),
            closure_count: 0,
            parent_collector: self,
        };

        collector.visit_expr(&body.value);

        (
            collector.functions_called,
            collector.methods_called,
            collector.types_used.into_iter().collect(),
            collector.literals_used,
            collector.where_functions,
        )
    }

    pub fn extract_type_origin_info(&self, hir_ty: &rustc_hir::Ty<'_>) -> Option<TypeOriginInfo> {
        match &hir_ty.kind {
            rustc_hir::TyKind::Path(qpath) => self.extract_type_from_qpath(qpath, hir_ty.span),
            rustc_hir::TyKind::Ref(lifetime, mutty) => {
                let mut base_type = self.extract_type_origin_info(mutty.ty)?;
                base_type.type_name = format!(
                    "&{}{}",
                    if mutty.mutbl.is_mut() { "mut " } else { "" },
                    base_type.type_name
                );
                Some(base_type)
            }
            rustc_hir::TyKind::Slice(ty) => {
                let element_type = self.extract_type_origin_info(ty)?;
                Some(TypeOriginInfo {
                    type_name: format!("[{}]", element_type.type_name),
                    crate_name: "core".to_string(),
                    module_path: "slice".to_string(),
                    generic_args: vec![element_type],
                    is_generic_param: false,
                    src_location: self.format_span(hir_ty.span),
                })
            }
            rustc_hir::TyKind::Array(ty, len) => {
                let element_type = self.extract_type_origin_info(ty)?;
                Some(TypeOriginInfo {
                    type_name: format!("[{}; {:?}]", element_type.type_name, len),
                    crate_name: "core".to_string(),
                    module_path: "array".to_string(),
                    generic_args: vec![element_type],
                    is_generic_param: false,
                    src_location: self.format_span(hir_ty.span),
                })
            }
            rustc_hir::TyKind::Tup(tys) => {
                let mut tuple_elements = Vec::new();
                for ty in tys.iter() {
                    if let Some(element_type) = self.extract_type_origin_info(ty) {
                        tuple_elements.push(element_type);
                    }
                }

                let tuple_type_name = if tuple_elements.is_empty() {
                    "()".to_string()
                } else {
                    let element_names: Vec<String> =
                        tuple_elements.iter().map(|e| e.type_name.clone()).collect();
                    format!("({})", element_names.join(", "))
                };

                Some(TypeOriginInfo {
                    type_name: tuple_type_name,
                    crate_name: "core".to_string(),
                    module_path: "tuple".to_string(),
                    generic_args: tuple_elements,
                    is_generic_param: false,
                    src_location: self.format_span(hir_ty.span),
                })
            }
            rustc_hir::TyKind::BareFn(fn_decl) => {
                let mut param_types = Vec::new();
                for param in fn_decl.decl.inputs.iter() {
                    if let Some(param_type) = self.extract_type_origin_info(param) {
                        param_types.push(param_type);
                    }
                }

                let mut return_type = None;
                if let rustc_hir::FnRetTy::Return(ret_ty) = &fn_decl.decl.output {
                    return_type = self.extract_type_origin_info(ret_ty);
                }

                let fn_type_name = format!(
                    "fn({}) -> {}",
                    param_types
                        .iter()
                        .map(|p| p.type_name.clone())
                        .collect::<Vec<_>>()
                        .join(", "),
                    return_type
                        .as_ref()
                        .map_or("()".to_string(), |t| t.type_name.clone())
                );

                let mut generic_args = param_types;
                if let Some(ret) = return_type {
                    generic_args.push(ret);
                }

                Some(TypeOriginInfo {
                    type_name: fn_type_name,
                    crate_name: "core".to_string(),
                    module_path: "primitive".to_string(),
                    generic_args,
                    is_generic_param: false,
                    src_location: self.format_span(hir_ty.span),
                })
            }
            rustc_hir::TyKind::Never => Some(TypeOriginInfo {
                type_name: "!".to_string(),
                crate_name: "core".to_string(),
                module_path: "never".to_string(),
                generic_args: Vec::new(),
                is_generic_param: false,
                src_location: self.format_span(hir_ty.span),
            }),
            rustc_hir::TyKind::Infer(_) => Some(TypeOriginInfo {
                type_name: "_".to_string(),
                crate_name: "".to_string(),
                module_path: "".to_string(),
                generic_args: Vec::new(),
                is_generic_param: false,
                src_location: self.format_span(hir_ty.span),
            }),
            _ => Some(TypeOriginInfo {
                type_name: format!("{:?}", hir_ty.kind),
                crate_name: "unknown".to_string(),
                module_path: "unknown".to_string(),
                generic_args: Vec::new(),
                is_generic_param: false,
                src_location: self.format_span(hir_ty.span),
            }),
        }
    }

    pub fn extract_type_from_qpath(
        &self,
        qpath: &rustc_hir::QPath<'_>,
        span: Span,
    ) -> Option<TypeOriginInfo> {
        match qpath {
            rustc_hir::QPath::Resolved(_, path) => {
                match path.res {
                    rustc_hir::def::Res::Def(_, def_id) => {
                        let type_name = path
                            .segments
                            .last()
                            .map(|seg| seg.ident.to_string())
                            .unwrap_or_else(|| "unknown".to_string());

                        // Get crate and module info
                        let crate_name = self.tcx.crate_name(def_id.krate).to_string();
                        let def_path = self.tcx.def_path(def_id);

                        // Extract module path
                        let module_path = def_path
                            .data
                            .iter()
                            .take(def_path.data.len().saturating_sub(1)) // Exclude the type name itself
                            .map(|elem| elem.data.to_string())
                            .collect::<Vec<_>>()
                            .join("::");

                        // Handle generic arguments if present
                        let mut generic_args = Vec::new();
                        if let Some(args) = path.segments.last().and_then(|seg| seg.args) {
                            for arg in args.args.iter() {
                                match arg {
                                    rustc_hir::GenericArg::Type(ty) => {
                                        // if let Some(type_info) = self.extract_type_origin_info(ty) {
                                        //     generic_args.push(type_info);
                                        // }
                                    }
                                    rustc_hir::GenericArg::Lifetime(lt) => {
                                        generic_args.push(TypeOriginInfo {
                                            type_name: format!("'{}", lt.ident.to_string()),
                                            crate_name: "".to_string(),
                                            module_path: "".to_string(),
                                            generic_args: Vec::new(),
                                            is_generic_param: true,
                                            src_location: self.format_span(lt.ident.span),
                                        });
                                    }
                                    rustc_hir::GenericArg::Const(c) => {
                                        // Add const generic arguments
                                        generic_args.push(TypeOriginInfo {
                                            type_name: format!("{:?}", c),
                                            crate_name: "".to_string(),
                                            module_path: "".to_string(),
                                            generic_args: Vec::new(),
                                            is_generic_param: true,
                                            src_location: self.format_span(c.span()),
                                        });
                                    }
                                    _ => {}
                                }
                            }
                        }

                        // Format the type name with generic arguments if present
                        let full_type_name = if !generic_args.is_empty() {
                            let generic_names: Vec<String> =
                                generic_args.iter().map(|g| g.type_name.clone()).collect();
                            format!("{}<{}>", type_name, generic_names.join(", "))
                        } else {
                            type_name.clone()
                        };

                        Some(TypeOriginInfo {
                            type_name: full_type_name,
                            crate_name,
                            module_path,
                            generic_args,
                            is_generic_param: false,
                            src_location: self.format_span(span),
                        })
                    }
                    rustc_hir::def::Res::PrimTy(prim_ty) => {
                        // Handle primitive types
                        Some(TypeOriginInfo {
                            type_name: format!("{:?}", prim_ty).to_lowercase(),
                            crate_name: "core".to_string(),
                            module_path: "primitive".to_string(),
                            generic_args: Vec::new(),
                            is_generic_param: false,
                            src_location: self.format_span(span),
                        })
                    }
                    rustc_hir::def::Res::SelfTyParam { .. } => {
                        // Handle Self type parameter
                        Some(TypeOriginInfo {
                            type_name: "Self".to_string(),
                            crate_name: "".to_string(),
                            module_path: "".to_string(),
                            generic_args: Vec::new(),
                            is_generic_param: true,
                            src_location: self.format_span(span),
                        })
                    }
                    _ => None,
                }
            }
            rustc_hir::QPath::TypeRelative(base, segment) => {
                // Handle associated types like T::Item
                if let Some(base_type) = self.extract_type_origin_info(base) {
                    let assoc_type_name =
                        format!("{}::{}", base_type.type_name, segment.ident.to_string());

                    let mut generic_args = Vec::new();
                    generic_args.push(base_type);

                    // Add generic args from the segment if any
                    // if let Some(args) = segment.args {
                    //     for arg in args.args.iter() {
                    //         if let rustc_hir::GenericArg::Type(ty) = arg {
                    //             if let Some(type_info) = self.extract_type_origin_info(ty) {
                    //                 generic_args.push(type_info);
                    //             }
                    //         }
                    //     }
                    // }

                    Some(TypeOriginInfo {
                        type_name: assoc_type_name,
                        crate_name: "".to_string(), // Can't determine crate for associated type directly
                        module_path: "".to_string(),
                        generic_args,
                        is_generic_param: false,
                        src_location: self.format_span(segment.ident.span),
                    })
                } else {
                    None
                }
            }
            rustc_hir::QPath::LangItem(lang_item, span) => {
                // Handle lang items
                Some(TypeOriginInfo {
                    type_name: format!("<lang_item:{:?}>", lang_item),
                    crate_name: "core".to_string(),
                    module_path: "lang_items".to_string(),
                    generic_args: Vec::new(),
                    is_generic_param: false,
                    src_location: self.format_span(*span),
                })
            }
            _ => None,
        }
    }

    pub fn extract_type_origin_info_from_ty(
        &self,
        ty: rustc_middle::ty::Ty<'_>,
    ) -> Option<TypeOriginInfo> {
        match ty.kind() {
            TyKind::Bool => Some(TypeOriginInfo {
                type_name: "bool".to_string(),
                crate_name: "core".to_string(),
                module_path: "primitive".to_string(),
                generic_args: Vec::new(),
                is_generic_param: false,
                src_location: "".to_string(),
            }),
            TyKind::Char => Some(TypeOriginInfo {
                type_name: "char".to_string(),
                crate_name: "core".to_string(),
                module_path: "primitive".to_string(),
                generic_args: Vec::new(),
                is_generic_param: false,
                src_location: "".to_string(),
            }),
            TyKind::Int(int_ty) => Some(TypeOriginInfo {
                type_name: format!("{:?}", int_ty).to_lowercase(),
                crate_name: "core".to_string(),
                module_path: "primitive".to_string(),
                generic_args: Vec::new(),
                is_generic_param: false,
                src_location: "".to_string(),
            }),
            TyKind::Uint(uint_ty) => Some(TypeOriginInfo {
                type_name: format!("{:?}", uint_ty).to_lowercase(),
                crate_name: "core".to_string(),
                module_path: "primitive".to_string(),
                generic_args: Vec::new(),
                is_generic_param: false,
                src_location: "".to_string(),
            }),
            TyKind::Float(float_ty) => Some(TypeOriginInfo {
                type_name: format!("{:?}", float_ty).to_lowercase(),
                crate_name: "core".to_string(),
                module_path: "primitive".to_string(),
                generic_args: Vec::new(),
                is_generic_param: false,
                src_location: "".to_string(),
            }),
            TyKind::Adt(adt_def, substs) => {
                let def_id = adt_def.did();
                let crate_name = self.tcx.crate_name(def_id.krate).to_string();
                let def_path = self.tcx.def_path(def_id);

                let mut path_segments = Vec::new();
                for data in &def_path.data {
                    path_segments.push(data.data.to_string());
                }

                let type_name = path_segments
                    .last()
                    .cloned()
                    .unwrap_or_else(|| "unknown".to_string());
                let module_path = path_segments
                    .iter()
                    .take(path_segments.len().saturating_sub(1))
                    .cloned()
                    .collect::<Vec<_>>()
                    .join("::");

                let mut generic_args = Vec::new();
                for subst in substs.iter() {
                    if let GenericArgKind::Type(ty) = subst.unpack() {
                        if let Some(arg_info) = self.extract_type_origin_info_from_ty(ty) {
                            generic_args.push(arg_info);
                        }
                    }
                }

                let full_type_name = if !generic_args.is_empty() {
                    let generic_names: Vec<String> =
                        generic_args.iter().map(|g| g.type_name.clone()).collect();
                    format!("{}<{}>", type_name, generic_names.join(", "))
                } else {
                    type_name.clone()
                };

                Some(TypeOriginInfo {
                    type_name: full_type_name,
                    crate_name,
                    module_path,
                    generic_args,
                    is_generic_param: false,
                    src_location: "".to_string(),
                })
            }
            TyKind::Foreign(def_id) => {
                let crate_name = self.tcx.crate_name(def_id.krate).to_string();
                let def_path = self.tcx.def_path(*def_id);

                let mut path_segments = Vec::new();
                for data in &def_path.data {
                    path_segments.push(data.data.to_string());
                }

                let type_name = path_segments
                    .last()
                    .cloned()
                    .unwrap_or_else(|| "unknown".to_string());
                let module_path = path_segments
                    .iter()
                    .take(path_segments.len().saturating_sub(1))
                    .cloned()
                    .collect::<Vec<_>>()
                    .join("::");

                Some(TypeOriginInfo {
                    type_name,
                    crate_name,
                    module_path,
                    generic_args: Vec::new(),
                    is_generic_param: false,
                    src_location: "".to_string(),
                })
            }
            TyKind::Str => Some(TypeOriginInfo {
                type_name: "str".to_string(),
                crate_name: "core".to_string(),
                module_path: "primitive".to_string(),
                generic_args: Vec::new(),
                is_generic_param: false,
                src_location: "".to_string(),
            }),
            TyKind::Array(element_ty, len) => {
                if let Some(element_info) = self.extract_type_origin_info_from_ty(*element_ty) {
                    let array_len = match len.kind() {
                        ConstKind::Value(val) => format!("{:?}", val),
                        _ => "?".to_string(),
                    };

                    Some(TypeOriginInfo {
                        type_name: format!("[{}; {}]", element_info.type_name, array_len),
                        crate_name: "core".to_string(),
                        module_path: "array".to_string(),
                        generic_args: vec![element_info],
                        is_generic_param: false,
                        src_location: "".to_string(),
                    })
                } else {
                    None
                }
            }
            TyKind::Slice(element_ty) => {
                if let Some(element_info) = self.extract_type_origin_info_from_ty(*element_ty) {
                    Some(TypeOriginInfo {
                        type_name: format!("[{}]", element_info.type_name),
                        crate_name: "core".to_string(),
                        module_path: "slice".to_string(),
                        generic_args: vec![element_info],
                        is_generic_param: false,
                        src_location: "".to_string(),
                    })
                } else {
                    None
                }
            }
            TyKind::RawPtr(ty_and_mut, _) => {
                if let Some(pointee_info) = self.extract_type_origin_info_from_ty(*ty_and_mut) {
                    let mutability = if ty_and_mut.is_adt() { "mut" } else { "const" };
                    Some(TypeOriginInfo {
                        type_name: format!("*{} {}", mutability, pointee_info.type_name),
                        crate_name: "core".to_string(),
                        module_path: "primitive".to_string(),
                        generic_args: vec![pointee_info],
                        is_generic_param: false,
                        src_location: "".to_string(),
                    })
                } else {
                    None
                }
            }
            TyKind::Ref(region, ty, mutbl) => {
                if let Some(referenced_info) = self.extract_type_origin_info_from_ty(*ty) {
                    let mutability = if mutbl.is_mut() { "mut" } else { "" };
                    let lifetime = match region.kind() {
                        RegionKind::ReStatic => "'static",
                        _ => "'_",
                    };

                    Some(TypeOriginInfo {
                        type_name: format!(
                            "&{} {}{}{}",
                            lifetime,
                            if !mutability.is_empty() {
                                mutability
                            } else {
                                ""
                            },
                            if !mutability.is_empty() { " " } else { "" },
                            referenced_info.type_name
                        ),
                        crate_name: "core".to_string(),
                        module_path: "primitive".to_string(),
                        generic_args: vec![referenced_info],
                        is_generic_param: false,
                        src_location: "".to_string(),
                    })
                } else {
                    None
                }
            }
            TyKind::FnDef(def_id, substs) => {
                let crate_name = self.tcx.crate_name(def_id.krate).to_string();
                let def_path = self.tcx.def_path(*def_id);

                let mut path_segments = Vec::new();
                for data in &def_path.data {
                    path_segments.push(data.data.to_string());
                }

                let fn_name = path_segments
                    .last()
                    .cloned()
                    .unwrap_or_else(|| "unknown".to_string());
                let module_path = path_segments
                    .iter()
                    .take(path_segments.len().saturating_sub(1))
                    .cloned()
                    .collect::<Vec<_>>()
                    .join("::");

                let fn_sig = self.tcx.fn_sig(*def_id);
                let sig = fn_sig.skip_binder();

                let mut param_types = Vec::new();
                for param_ty in sig.inputs().iter() {
                    if let Some(param_info) =
                        self.extract_type_origin_info_from_ty(*param_ty.skip_binder())
                    {
                        param_types.push(param_info);
                    }
                }

                let mut return_type = None;
                if let Some(ret_info) =
                    self.extract_type_origin_info_from_ty(sig.output().skip_binder())
                {
                    return_type = Some(ret_info);
                }

                let fn_type_name = format!(
                    "fn({}) -> {}",
                    param_types
                        .iter()
                        .map(|p| p.type_name.clone())
                        .collect::<Vec<_>>()
                        .join(", "),
                    return_type
                        .as_ref()
                        .map_or("()".to_string(), |t| t.type_name.clone())
                );

                let mut generic_args = param_types;
                if let Some(ret) = return_type {
                    generic_args.push(ret);
                }

                Some(TypeOriginInfo {
                    type_name: fn_type_name,
                    crate_name,
                    module_path,
                    generic_args,
                    is_generic_param: false,
                    src_location: "".to_string(),
                })
            }
            TyKind::FnPtr(poly_fn_sig, _) => {
                let fn_sig = poly_fn_sig.skip_binder();

                let mut param_types = Vec::new();
                for param_ty in fn_sig.inputs().iter() {
                    if let Some(param_info) = self.extract_type_origin_info_from_ty(*param_ty) {
                        param_types.push(param_info);
                    }
                }

                let mut return_type = None;
                if let Some(ret_info) = self.extract_type_origin_info_from_ty(fn_sig.output()) {
                    return_type = Some(ret_info);
                }

                let fn_type_name = format!(
                    "fn({}) -> {}",
                    param_types
                        .iter()
                        .map(|p| p.type_name.clone())
                        .collect::<Vec<_>>()
                        .join(", "),
                    return_type
                        .as_ref()
                        .map_or("()".to_string(), |t| t.type_name.clone())
                );

                let mut generic_args = param_types;
                if let Some(ret) = return_type {
                    generic_args.push(ret);
                }

                Some(TypeOriginInfo {
                    type_name: fn_type_name,
                    crate_name: "core".to_string(),
                    module_path: "primitive".to_string(),
                    generic_args,
                    is_generic_param: false,
                    src_location: "".to_string(),
                })
            }
            TyKind::Closure(def_id, substs) => {
                // In Rust 1.88, closure signature access might have changed
                let closure_sig = substs.as_closure().sig();
                let sig = closure_sig.skip_binder();

                let mut param_types = Vec::new();
                for param_ty in sig.inputs().iter() {
                    if let Some(param_info) = self.extract_type_origin_info_from_ty(*param_ty) {
                        param_types.push(param_info);
                    }
                }

                let mut return_type = None;
                if let Some(ret_info) = self.extract_type_origin_info_from_ty(sig.output()) {
                    return_type = Some(ret_info);
                }

                let path_str = self.tcx.def_path_str(*def_id);

                let closure_type_name = format!(
                    "Closure<({}) -> {}>",
                    param_types
                        .iter()
                        .map(|p| p.type_name.clone())
                        .collect::<Vec<_>>()
                        .join(", "),
                    return_type
                        .as_ref()
                        .map_or("()".to_string(), |t| t.type_name.clone())
                );

                let mut generic_args = param_types;
                if let Some(ret) = return_type {
                    generic_args.push(ret);
                }

                Some(TypeOriginInfo {
                    type_name: closure_type_name,
                    crate_name: self.tcx.crate_name(def_id.krate).to_string(),
                    module_path: path_str,
                    generic_args,
                    is_generic_param: false,
                    src_location: "".to_string(),
                })
            }
            TyKind::Tuple(tys) => {
                let mut tuple_elements = Vec::new();
                for ty in tys.iter() {
                    if let Some(element_info) = self.extract_type_origin_info_from_ty(ty) {
                        tuple_elements.push(element_info);
                    }
                }

                let tuple_type_name = if tuple_elements.is_empty() {
                    "()".to_string()
                } else {
                    let element_names: Vec<String> =
                        tuple_elements.iter().map(|e| e.type_name.clone()).collect();
                    format!("({})", element_names.join(", "))
                };

                Some(TypeOriginInfo {
                    type_name: tuple_type_name,
                    crate_name: "core".to_string(),
                    module_path: "primitive".to_string(),
                    generic_args: tuple_elements,
                    is_generic_param: false,
                    src_location: "".to_string(),
                })
            }
            TyKind::Param(param_ty) => Some(TypeOriginInfo {
                type_name: param_ty.name.to_string(),
                crate_name: "".to_string(),
                module_path: "".to_string(),
                generic_args: Vec::new(),
                is_generic_param: true,
                src_location: "".to_string(),
            }),
            _ => Some(TypeOriginInfo {
                type_name: format!("{:?}", ty),
                crate_name: "unknown".to_string(),
                module_path: "unknown".to_string(),
                generic_args: Vec::new(),
                is_generic_param: false,
                src_location: "".to_string(),
            }),
        }
    }
}
