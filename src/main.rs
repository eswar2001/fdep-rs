#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate serde;
extern crate serde_json;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::Res;
use rustc_hir::intravisit::{self, walk_expr, walk_item, Visitor};
use rustc_hir::QPath::Resolved;
use rustc_hir::{BodyId, Expr, ExprKind, HirId, Item, ItemKind, QPath};
use rustc_interface::{interface, Queries};
use rustc_middle::ty::{self, TyCtxt, TyKind};
use rustc_span::Span;
use serde::Serialize;
use std::collections::HashMap;
use std::env;
use std::fmt::format;
use rustc_middle::ty::GenericArgKind;

#[derive(Debug, Serialize, Clone)]
struct TypeOriginInfo {
    type_name: String,
    crate_name: String,
    module_path: String,
    generic_args: Vec<TypeOriginInfo>,
    is_generic_param: bool,
}

#[derive(Debug, Serialize, Default)]
struct FunctionCalled {
    module_name: Option<String>,
    name: Option<String>,
    package_name: Option<String>,
    src_loc: Option<String>,
    #[serde(rename = "type_enum")]
    type_enum: String,
    id: Option<String>,
    function_signature: Option<TypeOriginInfo>
    // type_info: Option<TypeOriginInfo>,
    // argument_types: Option<Vec<TypeOriginInfo>>,
    // return_type: Option<TypeOriginInfo>,
}

#[derive(Debug, Serialize)]
struct WhereFunction {
    module_name: String,
    function_name: String,
    id: Option<String>,
    function_signature: Option<TypeOriginInfo>,
    src_loc: Option<String>,
    raw_string: Option<String>,
    #[serde(rename = "type_enum")]
    type_enum: String,
    // type_info: Option<TypeOriginInfo>,
    functions_called: Vec<FunctionCalled>,
    where_functions: HashMap<String, Function>,
}

#[derive(Debug, Serialize)]
struct Function {
    module_name: String,
    function_name: String,
    id: Option<String>,
    function_signature: Vec<TypeOriginInfo>,
    src_loc: Option<String>,
    raw_string: Option<String>,
    #[serde(rename = "type_enum")]
    type_enum: String,
    line_number_start: usize,
    line_number_end: usize,
    // function_input: Option<Vec<TypeOriginInfo>>,
    // function_output: Option<Vec<TypeOriginInfo>>,
    // type_info: Vec<TypeOriginInfo>,
    functions_called: Vec<FunctionCalled>,
    where_functions: HashMap<String, Function>,
}

struct Collector<'tcx> {
    tcx: TyCtxt<'tcx>,
    functions: Vec<Function>,
}

impl<'tcx> Collector<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            functions: vec![],
        }
    }
}

impl<'tcx> Visitor<'tcx> for Collector<'tcx> {
    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        if let ItemKind::Fn(sig, _, body_id) = item.kind {
            let def_id = item.owner_id.def_id.to_def_id();
            let fn_name = self.tcx.def_path_str(def_id);
            let body = self.tcx.hir().body(body_id);
            let span = item.span;
            let loc = self.tcx.sess.source_map().lookup_char_pos(span.lo());
            let end_loc = self.tcx.sess.source_map().lookup_char_pos(span.hi());

            let mut functions_called = vec![];
            let mut where_functions = HashMap::new();
            let mut closure_count = 0;

            struct ExprVisitor<'a, 'tcx> {
                tcx: TyCtxt<'tcx>,
                calls: &'a mut Vec<FunctionCalled>,
                where_functions: &'a mut HashMap<String, Function>,
                parent_fn: String,
                module: String,
                closure_count: &'a mut usize,
            }

            impl<'tcx> Visitor<'tcx> for ExprVisitor<'_, 'tcx> {
                fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
                    let typeck = self.tcx.typeck(expr.hir_id.owner.def_id);
                    let expr_ty = typeck.expr_ty(expr);

                    match &expr.kind {
                        ExprKind::Call(fn_expr, args) => {
                            if let ExprKind::Path(qpath) = &fn_expr.kind {
                                let res = typeck.qpath_res(qpath, fn_expr.hir_id);

                                if let Some(def_id) = res.opt_def_id() {
                                    let name = self.tcx.def_path_str(def_id);
                                    let fn_ty = self.tcx.type_of(def_id);

                                    // Extract function type info
                                    let type_info = extract_type_info(self.tcx, fn_ty.skip_binder());

                                    // Extract argument types
                                    let mut arg_types = Vec::new();
                                    for arg in args.iter() {
                                        let arg_ty = typeck.expr_ty(arg);
                                        if let Some(arg_info) = extract_type_info(self.tcx, arg_ty)
                                        {
                                            arg_types.push(arg_info);
                                        }
                                    }

                                    // Extract return type
                                    let ret_type = extract_type_info(self.tcx, expr_ty);

                                    let loc = self
                                        .tcx
                                        .sess
                                        .source_map()
                                        .span_to_embeddable_string(fn_expr.span);
                                    let crate_name = self.tcx.crate_name(def_id.krate).to_string();

                                    self.calls.push(FunctionCalled {
                                        module_name: Some(name.clone()),
                                        name: Some(name.clone()),
                                        package_name: Some(crate_name),
                                        src_loc: Some(loc),
                                        type_enum: "function_call".to_string(),
                                        id: Some(name.clone()),
                                        function_signature: type_info,
                                        // type_info,
                                        // argument_types: Some(arg_types),
                                        // return_type: ret_type,
                                    });
                                }
                            }
                        }
                        ExprKind::Closure(closure) => {
                            let body = self.tcx.hir().body(closure.body);
                            let mut inner_calls = vec![];
                            let mut inner_where_functions = HashMap::new();
                            *self.closure_count += 1;
                            let closure_name =
                                format!("{}$closure${}", self.parent_fn, self.closure_count);
                            // let loc = self
                                // .tcx
                                // .sess
                                // .source_map()
                                // .span_to_embeddable_string(expr.span);
                            let end_loc = self.tcx.sess.source_map().lookup_char_pos(expr.span.hi());
                            let loc = self.tcx.sess.source_map().lookup_char_pos(expr.span.lo());
                            // Extract closure type with detailed info
                            let closure_ty = typeck.expr_ty(expr);
                            let type_info_some = extract_type_info(self.tcx, closure_ty);
                            let type_info = match type_info_some {
                                Some(x) => vec![x],
                                None => Vec::new()
                            };
                            // let closure_ty = typeck.expr_ty(expr);
                            // let type_info = extract_type_info(self.tcx, closure_ty);
                            // let type_info = extract_type_origins(self.tcx, &closure.decl);

                            let mut inner_visitor = ExprVisitor {
                                tcx: self.tcx,
                                calls: &mut inner_calls,
                                where_functions: &mut inner_where_functions,
                                parent_fn: closure_name.clone(),
                                module: self.module.clone(),
                                closure_count: self.closure_count,
                            };

                            inner_visitor.visit_expr(&body.value);

                            let wf = Function {
                                module_name: self.module.clone(),
                                function_name: closure_name.clone(),
                                id: Some(format!("{}:{}", self.module, closure_name)),
                                function_signature: type_info,
                                src_loc: Some(format!("{}", span_to_str(expr.span, self.tcx))),
                                raw_string: None,
                                type_enum: "where_function".to_string(),
                                functions_called: inner_calls,
                                where_functions: inner_where_functions,
                                line_number_start:loc.line,
                                line_number_end: end_loc.line,
                            };
                            self.where_functions.insert(closure_name.clone(), wf);
                        }
                        ExprKind::Path(Resolved(_, path)) => {
                            // Path resolution (kept from original code)
                            let unique_name = match path.res {
                                Res::Def(_, def_id) => {
                                    let crate_name = self.tcx.crate_name(def_id.krate).to_string();
                                    let path = self.tcx.def_path_str(def_id);
                                    format!("{}::{}", crate_name, path)
                                }
                                Res::PrimTy(prim_ty) => format!("primitive::{:?}", prim_ty),
                                Res::SelfTyParam { trait_ } => {
                                    let crate_name = self.tcx.crate_name(trait_.krate).to_string();
                                    let path = self.tcx.def_path_str(trait_);
                                    format!("{}::{}::SelfTyParam", crate_name, path)
                                }
                                Res::SelfTyAlias { alias_to, .. } => {
                                    let crate_name =
                                        self.tcx.crate_name(alias_to.krate).to_string();
                                    let path = self.tcx.def_path_str(alias_to);
                                    format!("{}::{}::SelfTyAlias", crate_name, path)
                                }
                                Res::SelfCtor(impl_def_id) => {
                                    let crate_name =
                                        self.tcx.crate_name(impl_def_id.krate).to_string();
                                    let path = self.tcx.def_path_str(impl_def_id);
                                    format!("{}::{}::SelfCtor", crate_name, path)
                                }
                                Res::Local(hir_id) => {
                                    let owner = hir_id.owner.to_def_id();
                                    let owner_path = self.tcx.def_path_str(owner);
                                    format!("local::{}::{}", owner_path, hir_id.local_id.index())
                                }
                                Res::ToolMod => "tool_mod".to_string(),
                                Res::NonMacroAttr(kind) => {
                                    let kind_str = format!("{:?}",kind);
                                    format!("attribute::{}", kind_str)
                                }
                                Res::Err => "error".to_string(),
                            };
                        }
                        _ => {}
                    }

                    walk_expr(self, expr);
                }
            }

            let mut expr_visitor = ExprVisitor {
                tcx: self.tcx,
                calls: &mut functions_called,
                where_functions: &mut where_functions,
                parent_fn: fn_name.clone(),
                module: self.tcx.crate_name(def_id.krate).to_string(),
                closure_count: &mut closure_count,
            };

            expr_visitor.visit_expr(&body.value);

            // Extract type information for the function
            let type_info = extract_type_origins(self.tcx, &sig.decl);

            // Create function inputs and outputs from type_info
            let mut function_input = Vec::new();
            let mut function_output = Vec::new();

            if !type_info.is_empty() {
                for v in type_info.clone() {
                    function_input.push(v);
                }

                // Return type is the last element
                if let Some(ret_type) = type_info.last().cloned() {
                    function_output.push(ret_type);
                }
            }

            let function = Function {
                module_name: expr_visitor.module,
                function_name: fn_name.clone(),
                id: Some(fn_name.clone()),
                function_signature: type_info,
                src_loc: Some(format!("{}", span_to_str(span, self.tcx))),
                raw_string: None,
                type_enum: "function".to_string(),
                line_number_start: loc.line,
                line_number_end: end_loc.line,
                // function_input: Some(function_input),
                // function_output: Some(function_output),
                // type_info,
                functions_called,
                where_functions,
            };

            self.functions.push(function);
        }

        walk_item(self, item);
    }
}

fn extract_type_origins<'tcx>(
    tcx: TyCtxt<'tcx>,
    decl: &rustc_hir::FnDecl<'_>,
) -> Vec<TypeOriginInfo> {
    let mut type_origins = Vec::new();

    // Process input parameters
    for input in decl.inputs.iter() {
        let type_info = extract_type_from_hir_ty(tcx, input);
        if let Some(info) = type_info {
            type_origins.push(info);
        }
    }

    // Process return type
    if let rustc_hir::FnRetTy::Return(ty) = &decl.output {
        let type_info = extract_type_from_hir_ty(tcx, ty);
        if let Some(info) = type_info {
            type_origins.push(info);
        }
    } else {
        // Add unit type for default return
        type_origins.push(TypeOriginInfo {
            type_name: "()".to_string(),
            crate_name: "core".to_string(),
            module_path: "primitive".to_string(),
            generic_args: Vec::new(),
            is_generic_param: false,
        });
    }

    type_origins
}

fn extract_type_from_hir_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: &rustc_hir::Ty<'_>,
) -> Option<TypeOriginInfo> {
    match &ty.kind {
        rustc_hir::TyKind::Path(qpath) => extract_type_from_qpath(tcx, qpath),
        rustc_hir::TyKind::Ref(lifetime, mutty) => {
            let mut base_type = extract_type_from_hir_ty(tcx, mutty.ty)?;
            base_type.type_name = format!(
                "&{}{}",
                if mutty.mutbl.is_mut() { "mut " } else { "" },
                base_type.type_name
            );
            Some(base_type)
        }
        rustc_hir::TyKind::Slice(ty) => {
            let element_type = extract_type_from_hir_ty(tcx, ty)?;
            Some(TypeOriginInfo {
                type_name: format!("[{}]", element_type.type_name),
                crate_name: "core".to_string(),
                module_path: "slice".to_string(),
                generic_args: vec![element_type],
                is_generic_param: false,
            })
        }
        rustc_hir::TyKind::Array(ty, len) => {
            let element_type = extract_type_from_hir_ty(tcx, ty)?;
            Some(TypeOriginInfo {
                type_name: format!("[{}; {:?}]", element_type.type_name, len),
                crate_name: "core".to_string(),
                module_path: "array".to_string(),
                generic_args: vec![element_type],
                is_generic_param: false,
            })
        }
        rustc_hir::TyKind::Tup(tys) => {
            let mut tuple_elements = Vec::new();
            for ty in tys.iter() {
                if let Some(element_type) = extract_type_from_hir_ty(tcx, ty) {
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
            })
        }
        rustc_hir::TyKind::BareFn(fn_decl) => {
            let mut param_types = Vec::new();
            for param in fn_decl.decl.inputs.iter() {
                if let Some(param_type) = extract_type_from_hir_ty(tcx, param) {
                    param_types.push(param_type);
                }
            }

            let mut return_type = None;
            if let rustc_hir::FnRetTy::Return(ret_ty) = &fn_decl.decl.output {
                return_type = extract_type_from_hir_ty(tcx, ret_ty);
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
            })
        }
        rustc_hir::TyKind::Never => Some(TypeOriginInfo {
            type_name: "!".to_string(),
            crate_name: "core".to_string(),
            module_path: "never".to_string(),
            generic_args: Vec::new(),
            is_generic_param: false,
        }),
        rustc_hir::TyKind::Infer => Some(TypeOriginInfo {
            type_name: "_".to_string(),
            crate_name: "".to_string(),
            module_path: "".to_string(),
            generic_args: Vec::new(),
            is_generic_param: false,
        }),
        _ => None,
    }
}

fn extract_type_from_qpath<'tcx>(
    tcx: TyCtxt<'tcx>,
    qpath: &rustc_hir::QPath<'_>,
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
                    let crate_name = tcx.crate_name(def_id.krate).to_string();
                    let def_path = tcx.def_path(def_id);

                    // Extract module path
                    let module_path = def_path
                        .data
                        .iter()
                        .take(def_path.data.len() - 1) // Exclude the type name itself
                        .map(|elem| elem.data.to_string())
                        .collect::<Vec<_>>()
                        .join("::");

                    // Handle generic arguments if present
                    let mut generic_args = Vec::new();
                    if let Some(args) = path.segments.last().and_then(|seg| seg.args) {
                        for arg in args.args.iter() {
                            match arg {
                                rustc_hir::GenericArg::Type(ty) => {
                                    if let Some(type_info) = extract_type_from_hir_ty(tcx, ty) {
                                        generic_args.push(type_info);
                                    }
                                }
                                rustc_hir::GenericArg::Lifetime(lt) => {
                                    generic_args.push(TypeOriginInfo {
                                        type_name: format!("'{}", lt.ident.to_string()),
                                        crate_name: "".to_string(),
                                        module_path: "".to_string(),
                                        generic_args: Vec::new(),
                                        is_generic_param: true,
                                    });
                                }
                                rustc_hir::GenericArg::Const(c) => {
                                    // Add const generic arguments
                                    generic_args.push(TypeOriginInfo {
                                        type_name: format!("{:?}", c.value.body),
                                        crate_name: "".to_string(),
                                        module_path: "".to_string(),
                                        generic_args: Vec::new(),
                                        is_generic_param: true,
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
                    })
                }
                _ => None,
            }
        }
        rustc_hir::QPath::TypeRelative(base, segment) => {
            // Handle associated types like T::Item
            if let Some(base_type) = extract_type_from_hir_ty(tcx, base) {
                let assoc_type_name =
                    format!("{}::{}", base_type.type_name, segment.ident.to_string());

                let mut generic_args = Vec::new();
                generic_args.push(base_type);

                // Add generic args from the segment if any
                if let Some(args) = segment.args {
                    for arg in args.args.iter() {
                        if let rustc_hir::GenericArg::Type(ty) = arg {
                            if let Some(type_info) = extract_type_from_hir_ty(tcx, ty) {
                                generic_args.push(type_info);
                            }
                        }
                    }
                }

                Some(TypeOriginInfo {
                    type_name: assoc_type_name,
                    crate_name: "".to_string(), // Can't determine crate for associated type directly
                    module_path: "".to_string(),
                    generic_args,
                    is_generic_param: false,
                })
            } else {
                None
            }
        }
        rustc_hir::QPath::LangItem(lang_item, _, _) => {
            // Handle lang items
            Some(TypeOriginInfo {
                type_name: format!("<lang_item:{:?}>", lang_item),
                crate_name: "core".to_string(),
                module_path: "lang_items".to_string(),
                generic_args: Vec::new(),
                is_generic_param: false,
            })
        }
        _ => None,
    }
}

fn extract_type_info<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<TypeOriginInfo> {
    match ty.kind() {
        TyKind::Bool => Some(TypeOriginInfo {
            type_name: "bool".to_string(),
            crate_name: "core".to_string(),
            module_path: "primitive".to_string(),
            generic_args: Vec::new(),
            is_generic_param: false,
        }),
        TyKind::Char => Some(TypeOriginInfo {
            type_name: "char".to_string(),
            crate_name: "core".to_string(),
            module_path: "primitive".to_string(),
            generic_args: Vec::new(),
            is_generic_param: false,
        }),
        TyKind::Int(int_ty) => Some(TypeOriginInfo {
            type_name: format!("{:?}", int_ty).to_lowercase(),
            crate_name: "core".to_string(),
            module_path: "primitive".to_string(),
            generic_args: Vec::new(),
            is_generic_param: false,
        }),
        TyKind::Uint(uint_ty) => Some(TypeOriginInfo {
            type_name: format!("{:?}", uint_ty).to_lowercase(),
            crate_name: "core".to_string(),
            module_path: "primitive".to_string(),
            generic_args: Vec::new(),
            is_generic_param: false,
        }),
        TyKind::Float(float_ty) => Some(TypeOriginInfo {
            type_name: format!("{:?}", float_ty).to_lowercase(),
            crate_name: "core".to_string(),
            module_path: "primitive".to_string(),
            generic_args: Vec::new(),
            is_generic_param: false,
        }),
        TyKind::Adt(adt_def, substs) => {
            let def_id = adt_def.did();
            let crate_name = tcx.crate_name(def_id.krate).to_string();
            let def_path = tcx.def_path(def_id);

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
                    if let Some(arg_info) = extract_type_info(tcx, ty) {
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
            })
        }
        TyKind::Foreign(def_id) => {
            let crate_name = tcx.crate_name(def_id.krate).to_string();
            let def_path = tcx.def_path(*def_id);

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
            })
        }
        TyKind::Str => Some(TypeOriginInfo {
            type_name: "str".to_string(),
            crate_name: "core".to_string(),
            module_path: "primitive".to_string(),
            generic_args: Vec::new(),
            is_generic_param: false,
        }),
        TyKind::Array(element_ty, len) => {
            if let Some(element_info) = extract_type_info(tcx, *element_ty) {
                let array_len = match len.kind() {
                    ty::ConstKind::Value(val) => {
                        // if let rustc_middle::mir::interpret::ConstValue::Scalar(scalar) = val {
                        //     format!("{}", scalar.to_bits(scalar.size()).unwrap_or(0))
                        // } else {
                            "?".to_string()
                        // }
                    }
                    _ => "?".to_string(),
                };

                Some(TypeOriginInfo {
                    type_name: format!("[{}; {}]", element_info.type_name, array_len),
                    crate_name: "core".to_string(),
                    module_path: "array".to_string(),
                    generic_args: vec![element_info],
                    is_generic_param: false,
                })
            } else {
                None
            }
        }
        TyKind::Slice(element_ty) => {
            if let Some(element_info) = extract_type_info(tcx, *element_ty) {
                Some(TypeOriginInfo {
                    type_name: format!("[{}]", element_info.type_name),
                    crate_name: "core".to_string(),
                    module_path: "slice".to_string(),
                    generic_args: vec![element_info],
                    is_generic_param: false,
                })
            } else {
                None
            }
        }
        TyKind::RawPtr(ty_and_mut) => {
            if let Some(pointee_info) = extract_type_info(tcx, ty_and_mut.ty) {
                let mutability = if ty_and_mut.mutbl.is_mut() {
                    "mut"
                } else {
                    "const"
                };
                Some(TypeOriginInfo {
                    type_name: format!("*{} {}", mutability, pointee_info.type_name),
                    crate_name: "core".to_string(),
                    module_path: "primitive".to_string(),
                    generic_args: vec![pointee_info],
                    is_generic_param: false,
                })
            } else {
                None
            }
        }
        TyKind::Ref(region, ty, mutbl) => {
            if let Some(referenced_info) = extract_type_info(tcx, *ty) {
                let mutability = if mutbl.is_mut() { "mut" } else { "" };
                let lifetime = match region.kind() {
                    ty::RegionKind::ReStatic => "'static",
                    _ => "'_",
                };

                Some(TypeOriginInfo {
                    type_name: format!(
                        "&{} {}{}",
                        lifetime,
                        mutability,
                        if !mutability.is_empty() { " " } else { "" },
                        // referenced_info.type_name
                    ),
                    crate_name: "core".to_string(),
                    module_path: "primitive".to_string(),
                    generic_args: vec![referenced_info],
                    is_generic_param: false,
                })
            } else {
                None
            }
        }
        TyKind::FnDef(def_id, substs) => {
            let crate_name = tcx.crate_name(def_id.krate).to_string();
            let def_path = tcx.def_path(*def_id);

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

            let fn_sig = tcx.fn_sig(*def_id);
            let sig = fn_sig.skip_binder();

            let mut param_types = Vec::new();
            for param_ty in sig.inputs().iter() {
                if let Some(param_info) = extract_type_info(tcx, *(param_ty.skip_binder())) {
                    param_types.push(param_info);
                }
            }

            let mut return_type = None;
            if let Some(ret_info) = extract_type_info(tcx, sig.output().skip_binder()) {
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
            })
        }
        TyKind::FnPtr(poly_fn_sig) => {
            let fn_sig = poly_fn_sig.skip_binder();

            let mut param_types = Vec::new();
            for param_ty in fn_sig.inputs().iter() {
                if let Some(param_info) = extract_type_info(tcx, *param_ty) {
                    param_types.push(param_info);
                }
            }

            let mut return_type = None;
            if let Some(ret_info) = extract_type_info(tcx, fn_sig.output()) {
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
            })
        }
        TyKind::Closure(def_id, substs) => {
            let closure_sig = substs.as_closure().sig();
            let sig = closure_sig.skip_binder();

            let mut param_types = Vec::new();
            for param_ty in sig.inputs().iter() {
                if let Some(param_info) = extract_type_info(tcx, *param_ty) {
                    param_types.push(param_info);
                }
            }

            let mut return_type = None;
            if let Some(ret_info) = extract_type_info(tcx, sig.output()) {
                return_type = Some(ret_info);
            }

            let path_str = tcx.def_path_str(*def_id);

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
                crate_name: tcx.crate_name(def_id.krate).to_string(),
                module_path: path_str,
                generic_args,
                is_generic_param: false,
            })
        }
        TyKind::Tuple(tys) => {
            let mut tuple_elements = Vec::new();
            for ty in tys.iter() {
                if let Some(element_info) = extract_type_info(tcx, ty) {
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
            })
        }
        TyKind::Param(param_ty) => Some(TypeOriginInfo {
            type_name: param_ty.name.to_string(),
            crate_name: "".to_string(),
            module_path: "".to_string(),
            generic_args: Vec::new(),
            is_generic_param: true,
        }),
        _ => Some(TypeOriginInfo {
            type_name: ty.to_string(),
            crate_name: "unknown".to_string(),
            module_path: "unknown".to_string(),
            generic_args: Vec::new(),
            is_generic_param: false,
        }),
    }
}

fn span_to_str(span: Span, tcx: TyCtxt<'_>) -> String {
    tcx.sess.source_map().span_to_embeddable_string(span)
}

struct Analyzer;

impl Callbacks for Analyzer {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(|tcx| {
            let mut collector = Collector::new(tcx);
            for item_id in tcx.hir().items() {
                collector.visit_item(tcx.hir().item(item_id));
            }

            let json = serde_json::to_string_pretty(&collector.functions).unwrap();
            std::fs::write("functions.json", json).expect("Could not write output");
        });

        Compilation::Stop
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    rustc_driver::RunCompiler::new(&args, &mut Analyzer)
        .run()
        .unwrap();
}
