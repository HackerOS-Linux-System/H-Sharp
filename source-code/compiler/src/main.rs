use anyhow::{Context, Result};
use cranelift::prelude::*;
use cranelift::codegen::ir::Function;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;

#[derive(Debug, Deserialize, Serialize, Clone)]
enum HSharpLiteral {
    Int(i32),
    Bool(bool),
    String(String),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
enum HSharpOp {
    Add,
    Eq,
    Lt,
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
enum Type {
    I8,
    I32,
    Bool,
    Pointer(Box<Type>),
    Unit,
}

impl Type {
    fn size(&self) -> u32 {
        match self {
            Type::I8 => 1,
            Type::I32 => 4,
            Type::Bool => 1,
            Type::Pointer(_) => 8,
            Type::Unit => 0,
        }
    }
    fn cl_type(&self) -> types::Type {
        match self {
            Type::I8 => types::I8,
            Type::I32 => types::I32,
            Type::Bool => types::I8,
            Type::Pointer(_) => types::I64,
            Type::Unit => types::INVALID,
        }
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
enum HSharpExpr {
    Literal(HSharpLiteral),
    Var(String),
    Alloc(Box<HSharpExpr>),
    Dealloc(Box<HSharpExpr>),
    Deref(Box<HSharpExpr>),
    Assign(Box<HSharpExpr>, Box<HSharpExpr>),
    Print(Box<HSharpExpr>),
    Block(Vec<HSharpStmt>),
    Direct(Box<HSharpExpr>),
    BinOp(HSharpOp, Box<HSharpExpr>, Box<HSharpExpr>),
    AddrOf(Box<HSharpExpr>),
    If(Box<HSharpExpr>, Box<HSharpExpr>, Option<Box<HSharpExpr>>),
    While(Box<HSharpExpr>, Box<HSharpExpr>),
    Call(String, Vec<HSharpExpr>),
    Cast(Type, Box<HSharpExpr>),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
enum HSharpStmt {
    Let(String, Option<Type>, HSharpExpr),
    Expr(HSharpExpr),
    FunctionDef(String, Vec<(String, Type)>, Type, Box<HSharpExpr>),
    // Import is resolved in parser, not here
}

#[derive(Debug, Deserialize, Serialize, Clone)]
struct HSharpProgram {
    stmts: Vec<HSharpStmt>,
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: h-sharp-compiler <input_json> <output_obj>");
        std::process::exit(1);
    }
    let input_json = &args[1];
    let output_obj = &args[2];
    let json_data = fs::read_to_string(input_json).context("Failed to read input JSON")?;
    let program: HSharpProgram = serde_json::from_str(&json_data).context("Failed to parse JSON")?;
    check_program(&program)?;
    compile_program(&program, output_obj)?;
    Ok(())
}

fn check_program(program: &HSharpProgram) -> Result<()> {
    let has_functions = program.stmts.iter().any(|s| matches!(s, HSharpStmt::FunctionDef(..)));
    if has_functions {
        let mut func_map: HashMap<String, (Vec<Type>, Type)> = HashMap::new();
        for stmt in &program.stmts {
            if let HSharpStmt::FunctionDef(name, params, ret, _) = stmt {
                let param_tys = params.iter().map(|(_, t)| t.clone()).collect();
                if func_map.insert(name.clone(), (param_tys, ret.clone())).is_some() {
                    return Err(anyhow::anyhow!("Duplicate function {}", name));
                }
            } else if let HSharpStmt::Let(..) | HSharpStmt::Expr(..) = stmt {
                return Err(anyhow::anyhow!("Top-level lets and exprs not allowed with functions"));
            }
        }
        if !func_map.contains_key("main") {
            return Err(anyhow::anyhow!("No main function"));
        }
        for stmt in &program.stmts {
            if let HSharpStmt::FunctionDef(name, params, ret, body) = stmt {
                let mut type_env: Vec<HashMap<String, Type>> = vec![HashMap::new()];
                for (pname, pty) in params {
                    type_env.last_mut().unwrap().insert(pname.clone(), pty.clone());
                }
                let body_ty = infer_type(body, &type_env, &func_map)?;
                if body_ty != *ret {
                    return Err(anyhow::anyhow!("Function body type mismatch for {}. Expected {:?}, got {:?}", name, ret, body_ty));
                }
            }
        }
    } else {
        let mut type_env: Vec<HashMap<String, Type>> = vec![HashMap::new()];
        check_stmts(&program.stmts, &mut type_env, &HashMap::new())?;
    }
    Ok(())
}

fn check_stmts(stmts: &Vec<HSharpStmt>, type_env: &mut Vec<HashMap<String, Type>>, func_map: &HashMap<String, (Vec<Type>, Type)>) -> Result<()> {
    for stmt in stmts {
        match stmt {
            HSharpStmt::Let(name, opt_ty, expr) => {
                let expr_ty = infer_type(expr, type_env, func_map)?;
                if let Some(ty) = opt_ty {
                    if *ty != expr_ty {
                        return Err(anyhow::anyhow!("Type mismatch for let"));
                    }
                }
                type_env.last_mut().unwrap().insert(name.clone(), expr_ty);
            }
            HSharpStmt::Expr(expr) => {
                infer_type(expr, type_env, func_map)?;
            }
            _ => return Err(anyhow::anyhow!("Unexpected stmt in block")),
        }
    }
    Ok(())
}

fn infer_type(expr: &HSharpExpr, type_env: &Vec<HashMap<String, Type>>, func_map: &HashMap<String, (Vec<Type>, Type)>) -> Result<Type> {
    match expr {
        HSharpExpr::Literal(lit) => Ok(match lit {
            HSharpLiteral::Int(_) => Type::I32,
                                       HSharpLiteral::Bool(_) => Type::Bool,
                                       HSharpLiteral::String(_) => Type::Pointer(Box::new(Type::I8)),
        }),
        HSharpExpr::Var(name) => type_env.iter().rev().find_map(|m| m.get(name)).cloned().ok_or(anyhow::anyhow!("Undefined var: {}", name)),
        HSharpExpr::Alloc(size) => {
            if infer_type(size, type_env, func_map)? != Type::I32 {
                return Err(anyhow::anyhow!("Alloc size must be I32"));
            }
            Ok(Type::Pointer(Box::new(Type::I8)))
        }
        HSharpExpr::Dealloc(ptr) => {
            if let Type::Pointer(_) = infer_type(ptr, type_env, func_map)? {
                Ok(Type::Unit)
            } else {
                Err(anyhow::anyhow!("Dealloc must be pointer"))
            }
        }
        HSharpExpr::Deref(ptr) => {
            if let Type::Pointer(inner) = infer_type(ptr, type_env, func_map)? {
                Ok(*inner)
            } else {
                Err(anyhow::anyhow!("Deref must be pointer"))
            }
        }
        HSharpExpr::Assign(lhs, rhs) => {
            if let HSharpExpr::Deref(_) = **lhs {
                let lhs_ty = infer_type(lhs, type_env, func_map)?;
                let rhs_ty = infer_type(rhs, type_env, func_map)?;
                if lhs_ty == rhs_ty {
                    Ok(lhs_ty)
                } else {
                    Err(anyhow::anyhow!("Assign type mismatch"))
                }
            } else {
                Err(anyhow::anyhow!("Assign LHS must be deref"))
            }
        }
        HSharpExpr::Print(e) => {
            let ty = infer_type(e, type_env, func_map)?;
            if ty == Type::I32 || ty == Type::Pointer(Box::new(Type::I8)) {
                Ok(Type::Unit)
            } else {
                Err(anyhow::anyhow!("Print must be I32 or &i8"))
            }
        }
        HSharpExpr::Block(stmts) => {
            let mut inner_env = type_env.clone();
            inner_env.push(HashMap::new());
            check_stmts(stmts, &mut inner_env, func_map)?;
            Ok(Type::Unit)
        }
        HSharpExpr::Direct(inner) => infer_type(inner, type_env, func_map),
        HSharpExpr::BinOp(op, left, right) => {
            let lt = infer_type(left, type_env, func_map)?;
            let rt = infer_type(right, type_env, func_map)?;
            match op {
                HSharpOp::Add => if lt == Type::I32 && rt == Type::I32 { Ok(Type::I32) } else { Err(anyhow::anyhow!("Add type mismatch")) },
                HSharpOp::Eq => if lt == rt { Ok(Type::Bool) } else { Err(anyhow::anyhow!("Eq type mismatch")) },
                HSharpOp::Lt => if lt == Type::I32 && rt == Type::I32 { Ok(Type::Bool) } else { Err(anyhow::anyhow!("Lt type mismatch")) },
            }
        }
        HSharpExpr::AddrOf(inner) => Ok(Type::Pointer(Box::new(infer_type(inner, type_env, func_map)?))),
        HSharpExpr::If(cond, _, _) => {
            if infer_type(cond, type_env, func_map)? != Type::Bool {
                Err(anyhow::anyhow!("If cond must be Bool"))
            } else {
                Ok(Type::Unit)
            }
        }
        HSharpExpr::While(cond, _) => {
            if infer_type(cond, type_env, func_map)? != Type::Bool {
                Err(anyhow::anyhow!("While cond must be Bool"))
            } else {
                Ok(Type::Unit)
            }
        }
        HSharpExpr::Call(name, args) => {
            let (param_tys, ret) = func_map.get(name).cloned().ok_or(anyhow::anyhow!("Undefined function: {}", name))?;
            if args.len() != param_tys.len() {
                return Err(anyhow::anyhow!("Arg count mismatch for {}", name));
            }
            for (a, p) in args.iter().zip(param_tys) {
                if infer_type(a, type_env, func_map)? != p {
                    return Err(anyhow::anyhow!("Arg type mismatch in call to {}", name));
                }
            }
            Ok(ret)
        }
        HSharpExpr::Cast(ty, e) => {
            let ety = infer_type(e, type_env, func_map)?;
            match (&ety, ty) {
                (Type::Pointer(_), Type::Pointer(_)) => Ok(ty.clone()),
                _ => Err(anyhow::anyhow!("Invalid cast")),
            }
        }
    }
}

fn compile_program(program: &HSharpProgram, output_path: &str) -> Result<()> {
    let isa_builder = cranelift_native::builder()
    .map_err(|msg| anyhow::anyhow!("{}", msg))
    .context("Failed to build ISA")?;

    let isa = isa_builder.finish(settings::Flags::new(settings::builder())).context("Failed to finalize ISA")?;
    let builder = ObjectBuilder::new(isa, "hsharp_module", cranelift_module::default_libcall_names())?;
    let mut module = ObjectModule::new(builder);

    let malloc_id = module.declare_function("malloc", Linkage::Import, &signature_for_alloc(&module))?;
    let free_id = module.declare_function("free", Linkage::Import, &signature_for_dealloc(&module))?;
    let print_int_id = module.declare_function("print_int", Linkage::Import, &signature_for_print_int(&module))?;
    let print_str_id = module.declare_function("print_str", Linkage::Import, &signature_for_print_str(&module))?;

    let has_functions = program.stmts.iter().any(|s| matches!(s, HSharpStmt::FunctionDef(..)));
    let mut string_constants: HashMap<String, DataId> = HashMap::new();

    if has_functions {
        let mut func_ids: HashMap<String, FuncId> = HashMap::new();
        let mut func_sigs: HashMap<String, Signature> = HashMap::new();
        for stmt in &program.stmts {
            if let HSharpStmt::FunctionDef(name, params, ret, _) = stmt {
                let mut sig = module.make_signature();
                for (_, pty) in params {
                    sig.params.push(AbiParam::new(pty.cl_type()));
                }
                if ret.cl_type() != types::INVALID {
                    sig.returns.push(AbiParam::new(ret.cl_type()));
                }
                let linkage = if name == "main" { Linkage::Export } else { Linkage::Local };
                let func_id = module.declare_function(name, linkage, &sig)?;
                func_ids.insert(name.clone(), func_id);
                func_sigs.insert(name.clone(), sig);
            }
        }
        for stmt in &program.stmts {
            if let HSharpStmt::FunctionDef(name, params, ret, body) = stmt {
                let mut ctx = codegen::Context::new();
                let sig = func_sigs.get(name).unwrap().clone();
                ctx.func.signature = sig;
                let mut builder_ctx = FunctionBuilderContext::new();
                let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
                let entry_block = builder.create_block();
                builder.append_block_params_for_function_params(entry_block);
                builder.switch_to_block(entry_block);
                builder.seal_block(entry_block);
                let mut vars: Vec<HashMap<String, Value>> = vec![HashMap::new()];
                let mut type_env: Vec<HashMap<String, Type>> = vec![HashMap::new()];
                for (i, (pname, pty)) in params.iter().enumerate() {
                    let param_val = builder.block_params(entry_block)[i];
                    let slot_data = StackSlotData::new(StackSlotKind::ExplicitSlot, pty.size());
                    let slot = builder.create_sized_stack_slot(slot_data);
                    let addr = builder.ins().stack_addr(types::I64, slot, 0);
                    builder.ins().store(MemFlags::trusted(), param_val, addr, 0);
                    vars.last_mut().unwrap().insert(pname.clone(), addr);
                    type_env.last_mut().unwrap().insert(pname.clone(), pty.clone());
                }
                let val = compile_expr(body, &mut builder, &mut module, malloc_id, free_id, print_int_id, print_str_id, &mut vars, &mut type_env, &mut string_constants, &func_ids)?;
                if ret.cl_type() != types::INVALID {
                    builder.ins().return_(&[val]);
                } else {
                    builder.ins().return_(&[]);
                }
                builder.finalize();
                module.define_function(func_ids[name], &mut ctx)?;
            }
        }
    } else {
        let mut ctx = codegen::Context::new();
        let mut func = Function::new();
        let sig = signature_for_main(&module);
        func.signature = sig.clone();
        ctx.func = func;
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);
        let mut vars: Vec<HashMap<String, Value>> = vec![HashMap::new()];
        let mut type_env: Vec<HashMap<String, Type>> = vec![HashMap::new()];
        for stmt in &program.stmts {
            compile_stmt(stmt, &mut builder, &mut module, malloc_id, free_id, print_int_id, print_str_id, &mut vars, &mut type_env, &mut string_constants, &HashMap::new())?;
        }
        let zero = builder.ins().iconst(types::I32, 0);
        builder.ins().return_(&[zero]);
        builder.finalize();
        let main_id = module.declare_function("main", Linkage::Export, &sig)?;
        module.define_function(main_id, &mut ctx)?;
    }
    let product = module.finish();
    let bytes = product.emit()?;
    fs::write(output_path, bytes).context("Failed to write object file")?;
    Ok(())
}

fn signature_for_main(module: &ObjectModule) -> Signature {
    let mut sig = module.make_signature();
    sig.returns.push(AbiParam::new(types::I32));
    sig
}

fn signature_for_alloc(module: &ObjectModule) -> Signature {
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

fn signature_for_dealloc(module: &ObjectModule) -> Signature {
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig
}

fn signature_for_print_int(module: &ObjectModule) -> Signature {
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I32));
    sig
}

fn signature_for_print_str(module: &ObjectModule) -> Signature {
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig
}

fn compile_stmt(
    stmt: &HSharpStmt,
    builder: &mut FunctionBuilder,
    module: &mut ObjectModule,
    malloc_id: FuncId,
    free_id: FuncId,
    print_int_id: FuncId,
    print_str_id: FuncId,
    vars: &mut Vec<HashMap<String, Value>>,
    type_env: &mut Vec<HashMap<String, Type>>,
    string_constants: &mut HashMap<String, DataId>,
    func_ids: &HashMap<String, FuncId>,
) -> Result<Value> {
    match stmt {
        HSharpStmt::Let(name, opt_ty, expr) => {
            let val = compile_expr(expr, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
            let expr_ty = infer_type(expr, type_env, &HashMap::new())?;
            if let Some(ty) = opt_ty {
                if *ty != expr_ty {
                    return Err(anyhow::anyhow!("Type mismatch"));
                }
            }
            let size = expr_ty.size();
            let slot_data = StackSlotData::new(StackSlotKind::ExplicitSlot, size);
            let slot = builder.create_sized_stack_slot(slot_data);
            let addr = builder.ins().stack_addr(types::I64, slot, 0);
            builder.ins().store(MemFlags::trusted(), val, addr, 0);
            vars.last_mut().unwrap().insert(name.clone(), addr);
            type_env.last_mut().unwrap().insert(name.clone(), expr_ty);
            Ok(builder.ins().iconst(types::I32, 0))
        }
        HSharpStmt::Expr(expr) => compile_expr(expr, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids),
        _ => Err(anyhow::anyhow!("Unexpected stmt")),
    }
}

fn compile_expr(
    expr: &HSharpExpr,
    builder: &mut FunctionBuilder,
    module: &mut ObjectModule,
    malloc_id: FuncId,
    free_id: FuncId,
    print_int_id: FuncId,
    print_str_id: FuncId,
    vars: &mut Vec<HashMap<String, Value>>,
    type_env: &mut Vec<HashMap<String, Type>>,
    string_constants: &mut HashMap<String, DataId>,
    func_ids: &HashMap<String, FuncId>,
) -> Result<Value> {
    let ty = infer_type(expr, type_env, &HashMap::new())?;
    match expr {
        HSharpExpr::Literal(lit) => Ok(match lit {
            HSharpLiteral::Int(n) => builder.ins().iconst(types::I32, *n as i64),
                                       HSharpLiteral::Bool(b) => builder.ins().iconst(types::I8, if *b { 1 } else { 0 }),
                                       HSharpLiteral::String(s) => {
                                           let data_id = if let Some(&id) = string_constants.get(s) {
                                               id
                                           } else {
                                               let name = format!("str_{}", string_constants.len());
                                               let mut data_desc = DataDescription::new();
                                               let mut bytes = s.as_bytes().to_vec();
                                               bytes.push(0);
                                               data_desc.define(bytes.into_boxed_slice());
                                               let id = module.declare_data(&name, Linkage::Local, false, false)?;
                                               module.define_data(id, &data_desc)?;
                                               string_constants.insert(s.clone(), id);
                                               id
                                           };
                                           let gv = module.declare_data_in_func(data_id, builder.func);
                                           builder.ins().global_value(types::I64, gv)
                                       }
        }),
        HSharpExpr::Var(name) => {
            let addr = vars.iter().rev().find_map(|m| m.get(name)).cloned().ok_or(anyhow::anyhow!("Undefined var"))?;
            if ty.cl_type() == types::INVALID {
                Ok(addr)
            } else {
                Ok(builder.ins().load(ty.cl_type(), MemFlags::trusted(), addr, 0))
            }
        }
        HSharpExpr::Alloc(size_expr) => {
            let size = compile_expr(size_expr, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
            let size64 = builder.ins().sextend(types::I64, size);
            let malloc_call = module.declare_func_in_func(malloc_id, builder.func);
            let call_inst = builder.ins().call(malloc_call, &[size64]);
            Ok(builder.inst_results(call_inst)[0])
        }
        HSharpExpr::Dealloc(ptr_expr) => {
            let ptr = compile_expr(ptr_expr, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
            let free_call = module.declare_func_in_func(free_id, builder.func);
            builder.ins().call(free_call, &[ptr]);
            Ok(builder.ins().iconst(types::I32, 0))
        }
        HSharpExpr::Deref(ptr_expr) => {
            let ptr = compile_expr(ptr_expr, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
            Ok(builder.ins().load(ty.cl_type(), MemFlags::trusted(), ptr, 0))
        }
        HSharpExpr::Assign(lhs, rhs) => {
            // Fix check for dereference to avoid moving out of borrow
            if let HSharpExpr::Deref(ptr_expr) = &**lhs {
                let ptr = compile_expr(ptr_expr, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
                let val = compile_expr(rhs, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
                builder.ins().store(MemFlags::trusted(), val, ptr, 0);
                Ok(val)
            } else {
                Err(anyhow::anyhow!("Assign LHS must be deref"))
            }
        }
        HSharpExpr::Print(e) => {
            let val = compile_expr(e, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
            let func_id = if ty == Type::Pointer(Box::new(Type::I8)) { print_str_id } else { print_int_id };
            let call = module.declare_func_in_func(func_id, builder.func);
            builder.ins().call(call, &[val]);
            Ok(builder.ins().iconst(types::I32, 0))
        }
        HSharpExpr::Block(stmts) => {
            vars.push(HashMap::new());
            type_env.push(HashMap::new());
            let mut last = builder.ins().iconst(types::I32, 0);
            for stmt in stmts {
                last = compile_stmt(stmt, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
            }
            vars.pop();
            type_env.pop();
            Ok(last)
        }
        HSharpExpr::Direct(inner) => compile_expr(inner, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids),
        HSharpExpr::BinOp(op, left, right) => {
            let l = compile_expr(left, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
            let r = compile_expr(right, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
            Ok(match op {
                HSharpOp::Add => builder.ins().iadd(l, r),
               HSharpOp::Eq => {
                   let cmp = builder.ins().icmp(IntCC::Equal, l, r);
                   builder.ins().uextend(types::I32, cmp)
               }
               HSharpOp::Lt => {
                   let cmp = builder.ins().icmp(IntCC::SignedLessThan, l, r);
                   builder.ins().uextend(types::I32, cmp)
               }
            })
        }
        HSharpExpr::AddrOf(inner) => {
            Ok(match **inner {
                HSharpExpr::Var(ref name) => vars.iter().rev().find_map(|m| m.get(name)).cloned().ok_or(anyhow::anyhow!("Undefined"))?,
               HSharpExpr::Deref(ref p) => compile_expr(p, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?,
               _ => return Err(anyhow::anyhow!("AddrOf of non-lvalue")),
            })
        }
        HSharpExpr::If(cond, then_block, else_block) => {
            let c = compile_expr(cond, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
            let then_b = builder.create_block();
            let merge_b = builder.create_block();
            let else_b = if else_block.is_some() { builder.create_block() } else { merge_b };

            builder.ins().brif(c, then_b, &[], else_b, &[]);

            builder.switch_to_block(then_b);
            compile_expr(then_block, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
            builder.ins().jump(merge_b, &[]);

            if let Some(else_expr) = else_block {
                builder.switch_to_block(else_b);
                compile_expr(else_expr, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
                builder.ins().jump(merge_b, &[]);
            }

            builder.switch_to_block(merge_b);
            Ok(builder.ins().iconst(types::I32, 0))
        }
        HSharpExpr::While(cond, body) => {
            let head_b = builder.create_block();
            let body_b = builder.create_block();
            let exit_b = builder.create_block();
            builder.ins().jump(head_b, &[]);
            builder.switch_to_block(head_b);
            let c = compile_expr(cond, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;

            builder.ins().brif(c, body_b, &[], exit_b, &[]);

            builder.switch_to_block(body_b);
            compile_expr(body, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids)?;
            builder.ins().jump(head_b, &[]);
            builder.switch_to_block(exit_b);
            Ok(builder.ins().iconst(types::I32, 0))
        }
        HSharpExpr::Call(name, args) => {
            let args_val: Vec<Value> = args.iter().map(|a| compile_expr(a, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids).unwrap()).collect();
            let func_id = *func_ids.get(name).ok_or(anyhow::anyhow!("Undefined func"))?;
            let call = module.declare_func_in_func(func_id, builder.func);
            let inst = builder.ins().call(call, &args_val);
            let results = builder.inst_results(inst);
            if !results.is_empty() {
                Ok(results[0])
            } else {
                Ok(builder.ins().iconst(types::I32, 0))
            }
        }
        HSharpExpr::Cast(_, e) => compile_expr(e, builder, module, malloc_id, free_id, print_int_id, print_str_id, vars, type_env, string_constants, func_ids),
    }
}
