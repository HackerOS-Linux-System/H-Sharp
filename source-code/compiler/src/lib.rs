pub mod ast;
pub mod codegen;
pub mod typechecker;
pub mod types;

use crate::ast::*;
use crate::codegen::{compile_expr, CompilerState, is_block_terminated};
use crate::typechecker::FuncSig;
use crate::types::{StructOrUnion, HTypeExt};
use anyhow::{Context, Result};
use cranelift::prelude::*;
use cranelift::prelude::isa::CallConv;
use cranelift::prelude::types as cl_types;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataId, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::HashMap;
use std::fs;

// --- Monomorphization Utilities ---
fn mangle_name(name: &str, args: &[HType]) -> String {
    if args.is_empty() {
        return name.to_string();
    }
    let mut mangled = format!("{}_", name);
    for arg in args {
        match arg {
            HType::I32 => mangled.push_str("_I32"),
            HType::I64 => mangled.push_str("_I64"),
            HType::F64 => mangled.push_str("_F64"),
            HType::Bool => mangled.push_str("_Bool"),
            HType::Struct(n, sub) => mangled.push_str(&format!("_{}{}", n, if !sub.is_empty() { "_M" } else { "" })),
            HType::Pointer(_) => mangled.push_str("_Ptr"),
            _ => mangled.push_str("_T"),
        }
    }
    mangled
}

fn substitute_type(ty: &HType, mapping: &HashMap<String, HType>) -> HType {
    match ty {
        HType::Generic(name) => mapping.get(name)
        .cloned()
        .unwrap_or_else(|| panic!("Compiler Error: Unbound generic type parameter '{}' during monomorphization. The type was not inferred or provided.", name)),
        HType::Pointer(inner) => HType::Pointer(Box::new(substitute_type(inner, mapping))),
        HType::Array(inner, s) => HType::Array(Box::new(substitute_type(inner, mapping)), *s),
        HType::Slice(inner) => HType::Slice(Box::new(substitute_type(inner, mapping))),
        HType::Struct(name, args) => {
            let new_args = args.iter().map(|a| substitute_type(a, mapping)).collect();
            HType::Struct(name.clone(), new_args)
        }
        _ => ty.clone()
    }
}

fn normalize_struct_fields(
    fields: &[(String, HType)],
                           generic_params: &[String]
) -> Vec<(String, HType)> {
    fields.iter().map(|(n, ty)| (n.clone(), normalize_type(ty, generic_params))).collect()
}

fn normalize_type(ty: &HType, params: &[String]) -> HType {
    match ty {
        HType::Struct(name, args) if args.is_empty() => {
            if params.contains(name) {
                HType::Generic(name.clone())
            } else {
                ty.clone()
            }
        },
        HType::Pointer(inner) => HType::Pointer(Box::new(normalize_type(inner, params))),
        HType::Array(inner, s) => HType::Array(Box::new(normalize_type(inner, params)), *s),
        HType::Slice(inner) => HType::Slice(Box::new(normalize_type(inner, params))),
        HType::Struct(name, args) => {
            let new_args = args.iter().map(|a| normalize_type(a, params)).collect();
            HType::Struct(name.clone(), new_args)
        }
        _ => ty.clone()
    }
}

fn instantiate_struct(
    ty: &HType,
    templates: &HashMap<String, (Vec<String>, Vec<(String, HType)>)>,
                      type_map: &mut HashMap<String, StructOrUnion>
) -> HType {
    match ty {
        HType::Struct(name, args) if !args.is_empty() => {
            if let Some((params, fields)) = templates.get(name) {
                let concrete_args: Vec<HType> = args.iter().map(|a| instantiate_struct(a, templates, type_map)).collect();
                let mangled = mangle_name(name, &concrete_args);
                if !type_map.contains_key(&mangled) {
                    if params.len() != concrete_args.len() {
                        panic!("Generic argument count mismatch for struct '{}': expected {}, got {}", name, params.len(), concrete_args.len());
                    }
                    let mapping: HashMap<String, HType> = params.iter().zip(concrete_args.iter()).map(|(k, v)| (k.clone(), v.clone())).collect();
                    let concrete_fields: Vec<(String, HType)> = fields.iter().map(|(fname, fty)| {
                        (fname.clone(), substitute_type(fty, &mapping))
                    }).collect();
                    let final_fields: Vec<(String, HType)> = concrete_fields.iter().map(|(fnm, fty)| {
                        (fnm.clone(), instantiate_struct(fty, templates, type_map))
                    }).collect();
                    type_map.insert(mangled.clone(), StructOrUnion::Struct(final_fields));
                }
                return HType::Struct(mangled, vec![]);
            }
            ty.clone()
        },
        HType::Pointer(inner) => HType::Pointer(Box::new(instantiate_struct(inner, templates, type_map))),
        HType::Array(inner, s) => HType::Array(Box::new(instantiate_struct(inner, templates, type_map)), *s),
        HType::Slice(inner) => HType::Slice(Box::new(instantiate_struct(inner, templates, type_map))),
        _ => ty.clone()
    }
}

fn scan_and_instantiate_stmts(
    stmts: &mut [HSharpStmt],
    templates: &HashMap<String, (Vec<String>, Vec<(String, HType)>)>,
                              type_map: &mut HashMap<String, StructOrUnion>
) {
    for stmt in stmts {
        match stmt {
            HSharpStmt::Let(_, ty_opt, expr) => {
                if let Some(ty) = ty_opt {
                    *ty = instantiate_struct(ty, templates, type_map);
                }
                scan_and_instantiate_expr(expr, templates, type_map);
            },
            HSharpStmt::Expr(e) => scan_and_instantiate_expr(e, templates, type_map),
            HSharpStmt::FunctionDef(_, params, ret, body_opt, _) => {
                for (_, pty) in params {
                    *pty = instantiate_struct(pty, templates, type_map);
                }
                *ret = instantiate_struct(ret, templates, type_map);
                if let Some(body) = body_opt {
                    scan_and_instantiate_expr(body, templates, type_map);
                }
            },
            _ => {}
        }
    }
}

fn scan_and_instantiate_expr(
    expr: &mut HSharpExpr,
    templates: &HashMap<String, (Vec<String>, Vec<(String, HType)>)>,
                             type_map: &mut HashMap<String, StructOrUnion>
) {
    match expr {
        HSharpExpr::Block(stmts) => scan_and_instantiate_stmts(stmts, templates, type_map),
        HSharpExpr::Alloc(e) | HSharpExpr::Dealloc(e) |
        HSharpExpr::Write(e) | HSharpExpr::Return(e) | HSharpExpr::Direct(e) => scan_and_instantiate_expr(e, templates, type_map),
        HSharpExpr::Unary(_, e) => scan_and_instantiate_expr(e, templates, type_map),
        HSharpExpr::Assign(l, r) | HSharpExpr::BinOp(_, l, r) | HSharpExpr::While(l, r) => {
            scan_and_instantiate_expr(l, templates, type_map);
            scan_and_instantiate_expr(r, templates, type_map);
        },
        HSharpExpr::If(c, t, e_opt) => {
            scan_and_instantiate_expr(c, templates, type_map);
            scan_and_instantiate_expr(t, templates, type_map);
            if let Some(e) = e_opt { scan_and_instantiate_expr(e, templates, type_map); }
        },
        HSharpExpr::For(_, s, e, b) => {
            scan_and_instantiate_expr(s, templates, type_map);
            scan_and_instantiate_expr(e, templates, type_map);
            scan_and_instantiate_expr(b, templates, type_map);
        },
        HSharpExpr::Cast(ty, e) => {
            *ty = instantiate_struct(ty, templates, type_map);
            scan_and_instantiate_expr(e, templates, type_map);
        },
        HSharpExpr::Call(_, args) | HSharpExpr::MethodCall(_, _, args) | HSharpExpr::ArrayLit(args) => {
            for a in args { scan_and_instantiate_expr(a, templates, type_map); }
        },
        HSharpExpr::StructLit(_name, args) => {
            for a in args { scan_and_instantiate_expr(a, templates, type_map); }
        },
        _ => {}
    }
}

// --- Optimizer ---

fn lit_int(val: i64) -> HSharpExpr {
    HSharpExpr::Literal(HSharpLiteral::Int(val as i32))
}

fn lit_bool(val: bool) -> HSharpExpr {
    HSharpExpr::Literal(HSharpLiteral::Bool(val))
}

fn expr_unit() -> HSharpExpr {
    HSharpExpr::Block(vec![])
}

pub fn optimize_expr(expr: HSharpExpr) -> HSharpExpr {
    match expr {
        HSharpExpr::BinOp(op, l, r) => {
            let l = optimize_expr(*l);
            let r = optimize_expr(*r);
            match (&l, &r) {
                (HSharpExpr::Literal(HSharpLiteral::Int(a)), HSharpExpr::Literal(HSharpLiteral::Int(b))) => {
                    let a = *a as i64;
                    let b = *b as i64;
                    match op {
                        HSharpOp::Add => lit_int(a + b),
                        HSharpOp::Sub => lit_int(a - b),
                        HSharpOp::Mul => lit_int(a * b),
                        HSharpOp::Div => if b != 0 { lit_int(a / b) } else { HSharpExpr::BinOp(op, Box::new(l), Box::new(r)) },
                        HSharpOp::Mod => if b != 0 { lit_int(a % b) } else { HSharpExpr::BinOp(op, Box::new(l), Box::new(r)) },
                        HSharpOp::Eq => lit_bool(a == b),
                        HSharpOp::Ne => lit_bool(a != b),
                        HSharpOp::Lt => lit_bool(a < b),
                        HSharpOp::Gt => lit_bool(a > b),
                        HSharpOp::Le => lit_bool(a <= b),
                        HSharpOp::Ge => lit_bool(a >= b),
                        _ => HSharpExpr::BinOp(op, Box::new(l), Box::new(r))
                    }
                },
                (HSharpExpr::Literal(HSharpLiteral::Bool(false)), _) if op == HSharpOp::And => lit_bool(false),
                (HSharpExpr::Literal(HSharpLiteral::Bool(true)), _) if op == HSharpOp::And => r,
                (_, HSharpExpr::Literal(HSharpLiteral::Bool(false))) if op == HSharpOp::And => lit_bool(false),
                (_, HSharpExpr::Literal(HSharpLiteral::Bool(true))) if op == HSharpOp::And => l,
                (HSharpExpr::Literal(HSharpLiteral::Bool(true)), _) if op == HSharpOp::Or => lit_bool(true),
                (HSharpExpr::Literal(HSharpLiteral::Bool(false)), _) if op == HSharpOp::Or => r,
                (_, HSharpExpr::Literal(HSharpLiteral::Bool(true))) if op == HSharpOp::Or => lit_bool(true),
                (_, HSharpExpr::Literal(HSharpLiteral::Bool(false))) if op == HSharpOp::Or => l,
                (_, HSharpExpr::Literal(HSharpLiteral::Int(0))) if op == HSharpOp::Mul => lit_int(0),
                (HSharpExpr::Literal(HSharpLiteral::Int(0)), _) if op == HSharpOp::Mul => lit_int(0),
                (_, HSharpExpr::Literal(HSharpLiteral::Int(1))) if op == HSharpOp::Mul => l,
                (HSharpExpr::Literal(HSharpLiteral::Int(1)), _) if op == HSharpOp::Mul => r,
                (_, HSharpExpr::Literal(HSharpLiteral::Int(0))) if op == HSharpOp::Add => l,
                (HSharpExpr::Literal(HSharpLiteral::Int(0)), _) if op == HSharpOp::Add => r,
                (_, HSharpExpr::Literal(HSharpLiteral::Int(0))) if op == HSharpOp::Sub => l,
                _ => HSharpExpr::BinOp(op, Box::new(l), Box::new(r))
            }
        },
        HSharpExpr::Block(stmts) => {
            let stmts = optimize_stmts(stmts);
            if stmts.len() == 1 {
                if let Some(HSharpStmt::Expr(_)) = stmts.first() {
                    if let HSharpStmt::Expr(e) = stmts.into_iter().next().unwrap() {
                        e
                    } else {
                        unreachable!()
                    }
                } else {
                    HSharpExpr::Block(stmts)
                }
            } else {
                HSharpExpr::Block(stmts)
            }
        },
        HSharpExpr::If(cond, then, els) => {
            let cond = optimize_expr(*cond);
            let then = optimize_expr(*then);
            let els = els.map(|e| Box::new(optimize_expr(*e)));
            match cond {
                HSharpExpr::Literal(HSharpLiteral::Bool(true)) => then,
                HSharpExpr::Literal(HSharpLiteral::Bool(false)) => els.map(|e| *e).unwrap_or_else(expr_unit),
                _ => HSharpExpr::If(Box::new(cond), Box::new(then), els)
            }
        },
        HSharpExpr::While(cond, body) => {
            let cond = optimize_expr(*cond);
            let body = optimize_expr(*body);
            match cond {
                HSharpExpr::Literal(HSharpLiteral::Bool(false)) => expr_unit(),
                _ => HSharpExpr::While(Box::new(cond), Box::new(body))
            }
        },
        HSharpExpr::For(name, start, end, body) => {
            let start = optimize_expr(*start);
            let end = optimize_expr(*end);
            let body = optimize_expr(*body);
            HSharpExpr::For(name, Box::new(start), Box::new(end), Box::new(body))
        },
        HSharpExpr::Assign(l, r) => {
            let l = optimize_expr(*l);
            let r = optimize_expr(*r);
            HSharpExpr::Assign(Box::new(l), Box::new(r))
        },
        HSharpExpr::Call(name, args) => {
            let args = args.into_iter().map(optimize_expr).collect();
            HSharpExpr::Call(name, args)
        },
        HSharpExpr::MethodCall(recv, method, args) => {
            let recv = optimize_expr(*recv);
            let args = args.into_iter().map(optimize_expr).collect();
            HSharpExpr::MethodCall(Box::new(recv), method, args)
        },
        HSharpExpr::ArrayLit(args) => {
            let args = args.into_iter().map(optimize_expr).collect();
            HSharpExpr::ArrayLit(args)
        },
        HSharpExpr::StructLit(name, args) => {
            let args = args.into_iter().map(optimize_expr).collect();
            HSharpExpr::StructLit(name, args)
        },
        HSharpExpr::Cast(ty, e) => {
            let e = optimize_expr(*e);
            HSharpExpr::Cast(ty, Box::new(e))
        },
        HSharpExpr::Unary(op, e) => HSharpExpr::Unary(op, Box::new(optimize_expr(*e))),
        HSharpExpr::Alloc(e) => HSharpExpr::Alloc(Box::new(optimize_expr(*e))),
        HSharpExpr::Dealloc(e) => HSharpExpr::Dealloc(Box::new(optimize_expr(*e))),
        HSharpExpr::Write(e) => HSharpExpr::Write(Box::new(optimize_expr(*e))),
        HSharpExpr::Return(e) => HSharpExpr::Return(Box::new(optimize_expr(*e))),
        HSharpExpr::Direct(e) => HSharpExpr::Direct(Box::new(optimize_expr(*e))),
        other => other,
    }
}

fn optimize_stmt(stmt: HSharpStmt) -> HSharpStmt {
    match stmt {
        HSharpStmt::Let(name, ty_opt, expr) => HSharpStmt::Let(name, ty_opt, optimize_expr(expr)),
        HSharpStmt::Expr(e) => HSharpStmt::Expr(optimize_expr(e)),
        HSharpStmt::FunctionDef(name, params, ret, body_opt, is_pub) =>
        HSharpStmt::FunctionDef(name, params, ret, body_opt.map(|b| Box::new(optimize_expr(*b))), is_pub),
        other => other,
    }
}

fn optimize_stmts(stmts: Vec<HSharpStmt>) -> Vec<HSharpStmt> {
    stmts.into_iter().map(optimize_stmt).collect()
}

pub fn compile_program(
    program: &HSharpProgram,
    output_path: &str,
) -> Result<()> {
    let mut type_map: HashMap<String, StructOrUnion> = HashMap::new();
    let mut generic_templates: HashMap<String, (Vec<String>, Vec<(String, HType)>)> = HashMap::new();

    type_map.insert("String".to_string(), StructOrUnion::Struct(vec![
        ("ptr".to_string(), HType::Pointer(Box::new(HType::I8))),
                                                                ("len".to_string(), HType::I64),
    ]));

    for stmt in &program.stmts {
        match stmt {
            HSharpStmt::StructDef(name, generics, fields) => {
                if generics.is_empty() {
                    type_map.insert(name.clone(), StructOrUnion::Struct(fields.clone()));
                } else {
                    let normalized_fields = normalize_struct_fields(fields, generics);
                    generic_templates.insert(name.clone(), (generics.clone(), normalized_fields));
                }
            }
            HSharpStmt::UnionDef(name, fields) => { type_map.insert(name.clone(), StructOrUnion::Union(fields.clone())); }
            _ => {}
        }
    }

    let mut modified_stmts = program.stmts.clone();
    scan_and_instantiate_stmts(&mut modified_stmts, &generic_templates, &mut type_map);
    modified_stmts = optimize_stmts(modified_stmts);

    let mut flag_builder = settings::builder();
    flag_builder.set("opt_level", "speed_and_size").unwrap();
    flag_builder.set("enable_simd", "true").unwrap();
    flag_builder.set("enable_verifier", "false").unwrap();
    flag_builder.set("regalloc_checker", "false").unwrap();
    flag_builder.set("is_pic", "false").unwrap();
    let flags = settings::Flags::new(flag_builder);
    let isa_builder = cranelift_native::builder()
    .map_err(|msg| anyhow::anyhow!("{}", msg))
    .context("Failed to build ISA")?;
    let isa = isa_builder.finish(flags).context("Failed to finalize ISA")?;
    let builder = ObjectBuilder::new(
        isa,
        "hsharp_module",
        cranelift_module::default_libcall_names(),
    )?;
    let mut module = ObjectModule::new(builder);

    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(cl_types::I64)); sig.returns.push(AbiParam::new(cl_types::I64));
    let malloc_id = module.declare_function("malloc", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(cl_types::I64));
    let free_id = module.declare_function("free", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(cl_types::I32));
    let write_int_id = module.declare_function("write_int", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(cl_types::I64));
    let write_str_id = module.declare_function("write_str", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(cl_types::F64));
    let write_float_id = module.declare_function("write_float", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(cl_types::I64)); sig.returns.push(AbiParam::new(cl_types::I64));
    let arena_new_id = module.declare_function("arena_new", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(cl_types::I64)); sig.params.push(AbiParam::new(cl_types::I64)); sig.returns.push(AbiParam::new(cl_types::I64));
    let arena_alloc_id = module.declare_function("arena_alloc", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(cl_types::I64));
    let arena_free_id = module.declare_function("arena_free", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(cl_types::I64)); sig.params.push(AbiParam::new(cl_types::I64)); sig.params.push(AbiParam::new(cl_types::I64));
    let memcpy_id = module.declare_function("memcpy", Linkage::Import, &sig)?;
    let mut string_constants: HashMap<String, DataId> = HashMap::new();
    let mut func_ids: HashMap<String, FuncId> = HashMap::new();

    let mut func_types: HashMap<String, FuncSig> = HashMap::new();
    let mut func_sigs: HashMap<String, Signature> = HashMap::new();

    func_types.insert("write_int".to_string(), FuncSig {
        params: vec![("i".to_string(), HType::I32)],
                      ret: HType::Unit,
                      is_async: false,
                      is_extern: true,
                      variadic: false,
    });
    func_ids.insert("write_int".to_string(), write_int_id);

    func_types.insert("write_float".to_string(), FuncSig {
        params: vec![("f".to_string(), HType::F64)],
                      ret: HType::Unit,
                      is_async: false,
                      is_extern: true,
                      variadic: false,
    });
    func_ids.insert("write_float".to_string(), write_float_id);

    func_types.insert("write_str".to_string(), FuncSig {
        params: vec![("s".to_string(), HType::Struct("String".to_string(), vec![]))],
                      ret: HType::Unit,
                      is_async: false,
                      is_extern: true,
                      variadic: false,
    });
    func_ids.insert("write_str".to_string(), write_str_id);

    let mut flattened_stmts = Vec::new();
    for stmt in &modified_stmts {
        match stmt {
            HSharpStmt::Impl(struct_name, methods) => {
                for m in methods {
                    if let HSharpStmt::FunctionDef(fn_name, params, ret, body_opt, _) = m {
                        let mangled = format!("{}_{}", struct_name, fn_name);
                        flattened_stmts.push(HSharpStmt::FunctionDef(mangled, params.clone(), ret.clone(), body_opt.clone(), false));
                    }
                }
            },
            _ => flattened_stmts.push(stmt.clone())
        }
    }

    for stmt in &flattened_stmts {
        if let HSharpStmt::FunctionDef(name, params, ret, body_opt, _) = stmt {
            let param_tys: Vec<HType> = params.iter().map(|(_, t)| t.clone()).collect();

            func_types.insert(name.clone(), FuncSig {
                params: params.clone(),
                              ret: ret.clone(),
                              is_async: false,
                              is_extern: body_opt.is_none(),
                              variadic: false,
            });

            let mut sig = module.make_signature();
            for pty in &param_tys {
                let cl_ty = pty.param_type();
                if cl_ty != cl_types::INVALID {
                    sig.params.push(AbiParam::new(cl_ty));
                }
            }
            if ret.param_type() != cl_types::INVALID {
                sig.returns.push(AbiParam::new(ret.param_type()));
            }
            let linkage = if name == "main" {
                Linkage::Export
            } else if body_opt.is_none() {
                Linkage::Import
            } else {
                Linkage::Local
            };
            let func_id = module.declare_function(name, linkage, &sig)?;
            func_ids.insert(name.clone(), func_id);
            func_sigs.insert(name.clone(), sig);
        }
    }

    for stmt in &flattened_stmts {
        if let HSharpStmt::FunctionDef(name, params, ret, body_opt, _) = stmt {
            if let Some(body) = body_opt {
                let mut codegen_ctx = cranelift::codegen::Context::new();
                codegen_ctx.func.signature = func_sigs.get(name).unwrap().clone();
                let mut builder_ctx = FunctionBuilderContext::new();
                let mut builder = FunctionBuilder::new(&mut codegen_ctx.func, &mut builder_ctx);
                let entry_block = builder.create_block();
                builder.append_block_params_for_function_params(entry_block);
                builder.switch_to_block(entry_block);
                builder.seal_block(entry_block);
                let mut vars: Vec<HashMap<String, Value>> = vec![HashMap::new()];
                let mut type_env: Vec<HashMap<String, HType>> = vec![HashMap::new()];
                for (i, (pname, pty)) in params.iter().enumerate() {
                    let cl_ty_param = pty.param_type();
                    if cl_ty_param == cl_types::INVALID { continue; }
                    let param_repr = builder.block_params(entry_block)[i];
                    let is_aggregate = !pty.is_value_type() || matches!(pty, HType::Slice(_));
                    let size = pty.size(&type_map);
                    let align = pty.alignment(&type_map);
                    let slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, align.ilog2() as u8));
                    let addr = builder.ins().stack_addr(cl_types::I64, slot, 0);
                    if !is_aggregate {
                        builder.ins().store(MemFlags::trusted(), param_repr, addr, 0);
                    } else {
                        let sz = builder.ins().iconst(cl_types::I64, size as i64);
                        let memcpy = module.declare_func_in_func(memcpy_id, builder.func);
                        builder.ins().call(memcpy, &[addr, param_repr, sz]);
                    }
                    vars.last_mut().unwrap().insert(pname.clone(), addr);
                    type_env.last_mut().unwrap().insert(pname.clone(), pty.clone());
                }
                let capacity = builder.ins().iconst(cl_types::I64, 1_048_576);
                let new_call = module.declare_func_in_func(arena_new_id, builder.func);
                let call_inst = builder.ins().call(new_call, &[capacity]);
                let arena = builder.inst_results(call_inst)[0];
                let mut state = CompilerState {
                    malloc_id, free_id, write_int_id, write_str_id, write_float_id,
                    arena_new_id, arena_alloc_id, arena_free_id, memcpy_id,
                    vars: &mut vars, type_env: &mut type_env,
                    string_constants: &mut string_constants,
                    func_ids: &func_ids, func_types: &func_types, type_map: &type_map,
                    arena, in_direct: false,
                };
                let val = compile_expr(&mut builder, &mut module, &mut state, body, None)?;
                if !is_block_terminated(&builder) {
                    let free_call = module.declare_func_in_func(arena_free_id, builder.func);
                    builder.ins().call(free_call, &[arena]);
                    let ret_ty = ret.param_type();
                    if ret_ty != cl_types::INVALID {
                        let val_ty = builder.func.dfg.value_type(val);
                        let final_val = if val_ty == cl_types::I32 && ret_ty == cl_types::I64 {
                            builder.ins().sextend(cl_types::I64, val)
                        } else if val_ty == cl_types::I64 && ret_ty == cl_types::I32 {
                            builder.ins().ireduce(cl_types::I32, val)
                        } else {
                            val
                        };
                        builder.ins().return_(&[final_val]);
                    } else {
                        builder.ins().return_(&[]);
                    }
                }
                builder.finalize();
                module.define_function(func_ids[name], &mut codegen_ctx)?;
            }
        }
    }
    let product = module.finish();
    let bytes = product.emit()?;
    fs::write(output_path, bytes).context("Failed to write object file")?;
    Ok(())
}
