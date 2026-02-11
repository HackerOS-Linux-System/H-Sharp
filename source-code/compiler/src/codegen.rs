use crate::ast::*;
use anyhow::Result;
use cranelift::codegen::ir::TrapCode;
use cranelift::prelude::*;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use cranelift_object::ObjectModule;
use std::collections::HashMap;

pub struct CompilerState<'a> {
    pub malloc_id: FuncId,
    pub free_id: FuncId,
    pub write_int_id: FuncId,
    pub write_str_id: FuncId,
    pub write_float_id: FuncId,
    pub arena_new_id: FuncId,
    pub arena_alloc_id: FuncId,
    pub arena_free_id: FuncId,
    pub memcpy_id: FuncId,
    pub vars: &'a mut Vec<HashMap<String, Value>>,
    pub type_env: &'a mut Vec<HashMap<String, HType>>,
    pub string_constants: &'a mut HashMap<String, DataId>,
    pub func_ids: &'a HashMap<String, FuncId>,
    pub func_types: &'a HashMap<String, (Vec<HType>, HType)>,
    pub type_map: &'a HashMap<String, StructOrUnion>,
    pub arena: Value,
    pub in_direct: bool,
}

pub fn infer_type(
    expr: &HSharpExpr,
    type_env: &[HashMap<String, HType>],
    func_map: &HashMap<String, (Vec<HType>, HType)>,
                  type_map: &HashMap<String, StructOrUnion>,
) -> Result<HType> {
    match expr {
        HSharpExpr::Literal(lit) => Ok(match lit {
            HSharpLiteral::Int(_) => HType::I32,
                                       HSharpLiteral::Bool(_) => HType::Bool,
                                       HSharpLiteral::String(_) => HType::Pointer(Box::new(HType::I8)),
                                       HSharpLiteral::Float(_) => HType::F64,
        }),
        HSharpExpr::Var(name) => type_env
        .iter()
        .rev()
        .find_map(|m| m.get(name))
        .cloned()
        .ok_or_else(|| anyhow::anyhow!("Undefined variable: {}", name)),
        HSharpExpr::Alloc(size) => {
            if infer_type(size, type_env, func_map, type_map)? != HType::I32 {
                return Err(anyhow::anyhow!("Alloc size must be I32"));
            }
            Ok(HType::Pointer(Box::new(HType::I8)))
        }
        HSharpExpr::Dealloc(ptr) => {
            if let HType::Pointer(_) = infer_type(ptr, type_env, func_map, type_map)? {
                Ok(HType::Unit)
            } else {
                Err(anyhow::anyhow!("Dealloc must be on pointer"))
            }
        }
        HSharpExpr::Deref(ptr) => match infer_type(ptr, type_env, func_map, type_map)? {
            HType::Pointer(inner) => Ok(*inner),
            _ => Err(anyhow::anyhow!("Deref must be on pointer")),
        },
        HSharpExpr::Assign(lhs, rhs) => {
            if let HSharpExpr::Deref(_) = **lhs {
                let lhs_ty = infer_type(lhs, type_env, func_map, type_map)?;
                let rhs_ty = infer_type(rhs, type_env, func_map, type_map)?;
                if lhs_ty == rhs_ty {
                    Ok(lhs_ty)
                } else {
                    Err(anyhow::anyhow!("Assign type mismatch"))
                }
            } else {
                Err(anyhow::anyhow!("Assign LHS must be deref"))
            }
        }
        HSharpExpr::Write(e) => {
            let ty = infer_type(e, type_env, func_map, type_map)?;
            match &ty {
                HType::I32 | HType::F64 => Ok(HType::Unit),
                HType::Pointer(inner) if **inner == HType::I8 => Ok(HType::Unit),
                _ => Err(anyhow::anyhow!("Write supports I32, F64, or &i8")),
            }
        }
        HSharpExpr::Block(stmts) => {
            let mut inner_env = type_env.to_vec();
            inner_env.push(HashMap::new());
            if let Some(HSharpStmt::Expr(last)) = stmts.last() {
                infer_type(last, &inner_env, func_map, type_map)
            } else {
                Ok(HType::Unit)
            }
        }
        HSharpExpr::Direct(inner) => infer_type(inner, type_env, func_map, type_map),
        HSharpExpr::BinOp(op, left, right) => {
            let lt = infer_type(left, type_env, func_map, type_map)?;
            let rt = infer_type(right, type_env, func_map, type_map)?;
            if (lt == HType::I32 && rt == HType::I32) || (lt == HType::F64 && rt == HType::F64) {
                match op {
                    HSharpOp::Add => Ok(lt),
                    HSharpOp::Eq | HSharpOp::Lt => Ok(HType::Bool),
                }
            } else {
                Err(anyhow::anyhow!("BinOp type mismatch"))
            }
        }
        HSharpExpr::AddrOf(inner) => Ok(HType::Pointer(Box::new(infer_type(
            inner, type_env, func_map, type_map,
        )?))),
        HSharpExpr::If(cond, _, _) => {
            if infer_type(cond, type_env, func_map, type_map)? != HType::Bool {
                Err(anyhow::anyhow!("If condition must be Bool"))
            } else {
                Ok(HType::Unit)
            }
        }
        HSharpExpr::While(cond, _) => {
            if infer_type(cond, type_env, func_map, type_map)? != HType::Bool {
                Err(anyhow::anyhow!("While condition must be Bool"))
            } else {
                Ok(HType::Unit)
            }
        }
        HSharpExpr::Call(name, args) => {
            let (param_tys, ret) = func_map
            .get(name)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("Undefined function: {}", name))?;
            if args.len() != param_tys.len() {
                return Err(anyhow::anyhow!("Argument count mismatch"));
            }
            Ok(ret)
        }
        HSharpExpr::Cast(ty, _) => Ok(ty.clone()),
        HSharpExpr::StructLit(name, _) => Ok(HType::Struct(name.clone())),
        HSharpExpr::UnionLit(name, _, _) => Ok(HType::Union(name.clone())),
        HSharpExpr::ArrayLit(elems) => {
            if elems.is_empty() {
                return Err(anyhow::anyhow!("Empty array literal"));
            }
            let elem_ty = infer_type(&elems[0], type_env, func_map, type_map)?;
            Ok(HType::Array(Box::new(elem_ty), elems.len()))
        }
        HSharpExpr::Field(s_expr, field) => {
            let st = infer_type(s_expr, type_env, func_map, type_map)?;
            let name = match st {
                HType::Struct(n) | HType::Union(n) => n,
                _ => return Err(anyhow::anyhow!("Field access on non-struct/union")),
            };
            let s = type_map
            .get(&name)
            .ok_or_else(|| anyhow::anyhow!("Undefined type: {}", name))?;
            s.field_type(field)
            .ok_or_else(|| anyhow::anyhow!("Undefined field: {}", field))
        }
        HSharpExpr::Index(arr, _) => {
            match infer_type(arr, type_env, func_map, type_map)? {
                HType::Array(inner, _) => Ok(*inner),
                _ => Err(anyhow::anyhow!("Index on non-array")),
            }
        }
        HSharpExpr::For(_, _, _, _) => Ok(HType::Unit),
        HSharpExpr::Return(e) => infer_type(e, type_env, func_map, type_map),
    }
}

pub fn compile_stmt(
    builder: &mut FunctionBuilder,
    module: &mut ObjectModule,
    state: &mut CompilerState,
    stmt: &HSharpStmt,
) -> Result<Value> {
    match stmt {
        HSharpStmt::Let(name, opt_ty, expr) => {
            let val = compile_expr(builder, module, state, expr)?;
            let expr_ty = infer_type(expr, state.type_env, state.func_types, state.type_map)?;
            if let Some(ty) = opt_ty {
                if *ty != expr_ty {
                    return Err(anyhow::anyhow!("Type mismatch in let"));
                }
            }
            let repr_size = if expr_ty.is_value_type() {
                expr_ty.size(state.type_map)
            } else {
                8
            };
            let align = if expr_ty.is_value_type() {
                expr_ty.alignment(state.type_map)
            } else {
                8
            };
            let align_shift = align.ilog2() as u8;
            let slot_data = StackSlotData::new(StackSlotKind::ExplicitSlot, repr_size, align_shift);
            let slot = builder.create_sized_stack_slot(slot_data);
            let addr = builder.ins().stack_addr(types::I64, slot, 0);
            builder.ins().store(MemFlags::trusted(), val, addr, 0);
            state.vars.last_mut().unwrap().insert(name.clone(), addr);
            state.type_env.last_mut().unwrap().insert(name.clone(), expr_ty);
            Ok(builder.ins().iconst(types::I32, 0))
        }
        HSharpStmt::Expr(expr) => compile_expr(builder, module, state, expr),
        _ => Err(anyhow::anyhow!("Unexpected stmt")),
    }
}

pub fn compile_expr(
    builder: &mut FunctionBuilder,
    module: &mut ObjectModule,
    state: &mut CompilerState,
    expr: &HSharpExpr,
) -> Result<Value> {
    let ty = infer_type(expr, state.type_env, state.func_types, state.type_map)?;
    match expr {
        HSharpExpr::Literal(lit) => Ok(match lit {
            HSharpLiteral::Int(n) => builder.ins().iconst(types::I32, *n as i64),
                                       HSharpLiteral::Bool(b) => builder.ins().iconst(types::I8, if *b { 1 } else { 0 }),
                                       HSharpLiteral::String(s) => {
                                           let data_id = if let Some(&id) = state.string_constants.get(s) {
                                               id
                                           } else {
                                               let name = format!("str_{}", state.string_constants.len());
                                               let mut data_desc = DataDescription::new();
                                               let mut bytes = s.as_bytes().to_vec();
                                               bytes.push(0);
                                               data_desc.define(bytes.into_boxed_slice());
                                               let id = module.declare_data(&name, Linkage::Local, false, false)?;
                                               module.define_data(id, &data_desc)?;
                                               state.string_constants.insert(s.clone(), id);
                                               id
                                           };
                                           let gv = module.declare_data_in_func(data_id, builder.func);
                                           builder.ins().global_value(types::I64, gv)
                                       }
                                       HSharpLiteral::Float(f) => builder.ins().f64const(*f),
        }),
        HSharpExpr::Var(name) => {
            let addr = state
            .vars
            .iter()
            .rev()
            .find_map(|m| m.get(name))
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("Undefined variable: {}", name))?;
            Ok(builder.ins().load(ty.param_type(), MemFlags::trusted(), addr, 0))
        }
        HSharpExpr::Alloc(size_expr) => {
            let size = compile_expr(builder, module, state, size_expr)?;
            let size64 = builder.ins().sextend(types::I64, size);
            let alloc_call = if state.in_direct {
                module.declare_func_in_func(state.malloc_id, builder.func)
            } else {
                module.declare_func_in_func(state.arena_alloc_id, builder.func)
            };
            let args = if state.in_direct {
                vec![size64]
            } else {
                vec![state.arena, size64]
            };
            let call_inst = builder.ins().call(alloc_call, &args);
            let ptr = builder.inst_results(call_inst)[0];
            let zero = builder.ins().iconst(types::I64, 0);
            let cmp = builder.ins().icmp(IntCC::Equal, ptr, zero);
            builder.ins().trapnz(cmp, TrapCode::HEAP_OUT_OF_BOUNDS);
            Ok(ptr)
        }
        HSharpExpr::Dealloc(ptr_expr) => {
            if !state.in_direct {
                return Err(anyhow::anyhow!("dealloc outside direct"));
            }
            let ptr = compile_expr(builder, module, state, ptr_expr)?;
            let free_call = module.declare_func_in_func(state.free_id, builder.func);
            builder.ins().call(free_call, &[ptr]);
            Ok(builder.ins().iconst(types::I32, 0))
        }
        HSharpExpr::Deref(ptr_expr) => {
            let ptr = compile_expr(builder, module, state, ptr_expr)?;
            let zero = builder.ins().iconst(types::I64, 0);
            let cmp = builder.ins().icmp(IntCC::Equal, ptr, zero);
            // Replaced NULL_REFERENCE with HEAP_OUT_OF_BOUNDS as standard null trap
            builder.ins().trapnz(cmp, TrapCode::HEAP_OUT_OF_BOUNDS);
            if ty.is_value_type() {
                Ok(builder.ins().load(ty.cl_type(), MemFlags::trusted(), ptr, 0))
            } else {
                Ok(ptr)
            }
        }
        HSharpExpr::Assign(lhs, rhs) => {
            if let HSharpExpr::Deref(ptr_expr) = &**lhs {
                let dst = compile_expr(builder, module, state, ptr_expr)?;
                let src = compile_expr(builder, module, state, rhs)?;
                if ty.is_value_type() {
                    builder.ins().store(MemFlags::trusted(), src, dst, 0);
                } else {
                    let size_const = builder.ins().iconst(types::I64, ty.size(state.type_map) as i64);
                    let memcpy_call = module.declare_func_in_func(state.memcpy_id, builder.func);
                    builder.ins().call(memcpy_call, &[dst, src, size_const]);
                }
                Ok(src)
            } else {
                Err(anyhow::anyhow!("Assign LHS must be deref"))
            }
        }
        HSharpExpr::Write(e) => {
            let val = compile_expr(builder, module, state, e)?;
            let func_id = match &ty {
                HType::I32 => state.write_int_id,
                HType::F64 => state.write_float_id,
                HType::Pointer(inner) if **inner == HType::I8 => state.write_str_id,
                _ => return Err(anyhow::anyhow!("Unsupported write type")),
            };
            let call = module.declare_func_in_func(func_id, builder.func);
            builder.ins().call(call, &[val]);
            Ok(builder.ins().iconst(types::I32, 0))
        }
        HSharpExpr::Block(stmts) => {
            state.vars.push(HashMap::new());
            state.type_env.push(HashMap::new());
            let mut last = builder.ins().iconst(types::I32, 0);
            for stmt in stmts {
                last = compile_stmt(builder, module, state, stmt)?;
            }
            state.vars.pop();
            state.type_env.pop();
            Ok(last)
        }
        HSharpExpr::Direct(inner) => {
            let old_direct = state.in_direct;
            state.in_direct = true;
            let res = compile_expr(builder, module, state, inner);
            state.in_direct = old_direct;
            res
        }
        HSharpExpr::BinOp(op, left, right) => {
            let l = compile_expr(builder, module, state, left)?;
            let r = compile_expr(builder, module, state, right)?;
            Ok(match ty {
                HType::I32 => match op {
                    HSharpOp::Add => builder.ins().iadd(l, r),
               HSharpOp::Eq => {
                   let cmp = builder.ins().icmp(IntCC::Equal, l, r);
                   builder.ins().uextend(types::I8, cmp)
               }
               HSharpOp::Lt => {
                   let cmp = builder.ins().icmp(IntCC::SignedLessThan, l, r);
                   builder.ins().uextend(types::I8, cmp)
               }
                },
                HType::F64 => match op {
                    HSharpOp::Add => builder.ins().fadd(l, r),
               HSharpOp::Eq => {
                   let cmp = builder.ins().fcmp(FloatCC::Equal, l, r);
                   builder.ins().uextend(types::I8, cmp)
               }
               HSharpOp::Lt => {
                   let cmp = builder.ins().fcmp(FloatCC::LessThan, l, r);
                   builder.ins().uextend(types::I8, cmp)
               }
                },
                _ => return Err(anyhow::anyhow!("Invalid binop type")),
            })
        }
        HSharpExpr::AddrOf(inner) => {
            match **inner {
                HSharpExpr::Var(ref name) => {
                    let addr = state.vars.iter().rev()
                    .find_map(|m| m.get(name)).cloned()
                    .ok_or_else(|| anyhow::anyhow!("Undefined variable"))?;
                    Ok(addr)
                },
                HSharpExpr::Deref(ref p) => compile_expr(builder, module, state, p),
                HSharpExpr::Field(ref s, ref f) => {
                    let s_ptr = compile_expr(builder, module, state, s)?;
                    let s_ty = infer_type(s, state.type_env, state.func_types, state.type_map)?;
                    let name = match s_ty {
                        HType::Struct(n) | HType::Union(n) => n,
                        _ => return Err(anyhow::anyhow!("Field addr_of on non-struct")),
                    };
                    let su = state.type_map.get(&name).ok_or_else(|| anyhow::anyhow!("Undefined type"))?;
                    let offset = su.field_offset(f, state.type_map) as i64;
                    Ok(builder.ins().iadd_imm(s_ptr, offset))
                }
                HSharpExpr::Index(ref a, ref i) => {
                    let a_ptr = compile_expr(builder, module, state, a)?;
                    let index = compile_expr(builder, module, state, i)?;
                    let a_ty = infer_type(a, state.type_env, state.func_types, state.type_map)?;
                    let (inner_ty, _) = match a_ty {
                        HType::Array(inner, l) => (*inner, l),
                        _ => return Err(anyhow::anyhow!("Index addr_of on non-array")),
                    };
                    let elem_size = inner_ty.size(state.type_map) as i64;
                    let offset = builder.ins().imul_imm(index, elem_size);
                    Ok(builder.ins().iadd(a_ptr, offset))
                }
                _ => Err(anyhow::anyhow!("AddrOf of non-lvalue")),
            }
        }
        HSharpExpr::If(cond, then_block, else_block) => {
            let c = compile_expr(builder, module, state, cond)?;
            let then_b = builder.create_block();
            let merge_b = builder.create_block();
            let else_b = if else_block.is_some() { builder.create_block() } else { merge_b };
            builder.ins().brif(c, then_b, &[], else_b, &[]);
            builder.switch_to_block(then_b);
            compile_expr(builder, module, state, then_block)?;
            builder.ins().jump(merge_b, &[]);
            if let Some(else_expr) = else_block {
                builder.switch_to_block(else_b);
                compile_expr(builder, module, state, else_expr)?;
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
            let c = compile_expr(builder, module, state, cond)?;
            builder.ins().brif(c, body_b, &[], exit_b, &[]);
            builder.switch_to_block(body_b);
            compile_expr(builder, module, state, body)?;
            builder.ins().jump(head_b, &[]);
            builder.switch_to_block(exit_b);
            Ok(builder.ins().iconst(types::I32, 0))
        }
        HSharpExpr::Call(name, args) => {
            let mut args_val: Vec<Value> = Vec::new();
            for a in args {
                args_val.push(compile_expr(builder, module, state, a)?);
            }
            let func_id = *state.func_ids.get(name).ok_or_else(|| anyhow::anyhow!("Undefined func"))?;
            let call = module.declare_func_in_func(func_id, builder.func);
            let inst = builder.ins().call(call, &args_val);
            let results = builder.inst_results(inst);
            if !results.is_empty() {
                Ok(results[0])
            } else {
                Ok(builder.ins().iconst(types::I32, 0))
            }
        }
        HSharpExpr::Cast(_, e) => compile_expr(builder, module, state, e),
        HSharpExpr::StructLit(name, fields) => {
            let s = state.type_map.get(name).ok_or_else(|| anyhow::anyhow!("Undefined struct"))?;
            if let StructOrUnion::Struct(fdefs) = s {
                let size = ty.size(state.type_map);
                let size_val = builder.ins().iconst(types::I64, size as i64);
                let alloc_call = if state.in_direct {
                    module.declare_func_in_func(state.malloc_id, builder.func)
                } else {
                    module.declare_func_in_func(state.arena_alloc_id, builder.func)
                };
                let args = if state.in_direct {
                    vec![size_val]
                } else {
                    vec![state.arena, size_val]
                };
                let call_inst = builder.ins().call(alloc_call, &args);
                let ptr = builder.inst_results(call_inst)[0];
                let zero = builder.ins().iconst(types::I64, 0);
                let cmp = builder.ins().icmp(IntCC::Equal, ptr, zero);
                builder.ins().trapnz(cmp, TrapCode::HEAP_OUT_OF_BOUNDS);
                let mut offset = 0;
                for (i, f) in fields.iter().enumerate() {
                    let val = compile_expr(builder, module, state, f)?;
                    let fty = &fdefs[i].1;
                    let falign = fty.alignment(state.type_map) as i64;
                    offset = ((offset + falign - 1) / falign) * falign;
                    let field_ptr = builder.ins().iadd_imm(ptr, offset);
                    if fty.is_value_type() {
                        builder.ins().store(MemFlags::trusted(), val, field_ptr, 0);
                    } else {
                        let fsize = builder.ins().iconst(types::I64, fty.size(state.type_map) as i64);
                        let memcpy_call = module.declare_func_in_func(state.memcpy_id, builder.func);
                        builder.ins().call(memcpy_call, &[field_ptr, val, fsize]);
                    }
                    offset += fty.size(state.type_map) as i64;
                }
                Ok(ptr)
            } else {
                Err(anyhow::anyhow!("Not a struct"))
            }
        }
        HSharpExpr::UnionLit(u_name, f_name, e) => {
            let u = state.type_map.get(u_name).ok_or_else(|| anyhow::anyhow!("Undefined union"))?;
            if let StructOrUnion::Union(_) = u {
                let size = ty.size(state.type_map);
                let size_val = builder.ins().iconst(types::I64, size as i64);
                let alloc_call = if state.in_direct {
                    module.declare_func_in_func(state.malloc_id, builder.func)
                } else {
                    module.declare_func_in_func(state.arena_alloc_id, builder.func)
                };
                let args = if state.in_direct {
                    vec![size_val]
                } else {
                    vec![state.arena, size_val]
                };
                let call_inst = builder.ins().call(alloc_call, &args);
                let ptr = builder.inst_results(call_inst)[0];
                let zero = builder.ins().iconst(types::I64, 0);
                let cmp = builder.ins().icmp(IntCC::Equal, ptr, zero);
                builder.ins().trapnz(cmp, TrapCode::HEAP_OUT_OF_BOUNDS);
                let val = compile_expr(builder, module, state, e)?;
                let fty = u.field_type(f_name).ok_or_else(|| anyhow::anyhow!("Undefined field"))?;
                if fty.is_value_type() {
                    builder.ins().store(MemFlags::trusted(), val, ptr, 0);
                } else {
                    let fsize = builder.ins().iconst(types::I64, fty.size(state.type_map) as i64);
                    let memcpy_call = module.declare_func_in_func(state.memcpy_id, builder.func);
                    builder.ins().call(memcpy_call, &[ptr, val, fsize]);
                }
                Ok(ptr)
            } else {
                Err(anyhow::anyhow!("Not a union"))
            }
        }
        HSharpExpr::ArrayLit(elems) => {
            let elem_ty = infer_type(&elems[0], state.type_env, state.func_types, state.type_map)?;
            let size = ty.size(state.type_map);
            let size_val = builder.ins().iconst(types::I64, size as i64);
            let alloc_call = if state.in_direct {
                module.declare_func_in_func(state.malloc_id, builder.func)
            } else {
                module.declare_func_in_func(state.arena_alloc_id, builder.func)
            };
            let args = if state.in_direct {
                vec![size_val]
            } else {
                vec![state.arena, size_val]
            };
            let call_inst = builder.ins().call(alloc_call, &args);
            let ptr = builder.inst_results(call_inst)[0];
            let zero = builder.ins().iconst(types::I64, 0);
            let cmp = builder.ins().icmp(IntCC::Equal, ptr, zero);
            builder.ins().trapnz(cmp, TrapCode::HEAP_OUT_OF_BOUNDS);
            let elem_size = elem_ty.size(state.type_map) as i64;
            for (i, e) in elems.iter().enumerate() {
                let val = compile_expr(builder, module, state, e)?;
                let offset = i as i64 * elem_size;
                let elem_ptr = builder.ins().iadd_imm(ptr, offset);
                if elem_ty.is_value_type() {
                    builder.ins().store(MemFlags::trusted(), val, elem_ptr, 0);
                } else {
                    let esize = builder.ins().iconst(types::I64, elem_size);
                    let memcpy_call = module.declare_func_in_func(state.memcpy_id, builder.func);
                    builder.ins().call(memcpy_call, &[elem_ptr, val, esize]);
                }
            }
            Ok(ptr)
        }
        HSharpExpr::Field(s_expr, field) => {
            let s_val = compile_expr(builder, module, state, s_expr)?;
            let s_ty = infer_type(s_expr, state.type_env, state.func_types, state.type_map)?;
            let name = match s_ty {
                HType::Struct(n) | HType::Union(n) => n,
                _ => return Err(anyhow::anyhow!("Field access on non-struct/union")),
            };
            let su = state.type_map.get(&name).ok_or_else(|| anyhow::anyhow!("Undefined type"))?;
            let offset = su.field_offset(field, state.type_map) as i64;
            let field_ptr = builder.ins().iadd_imm(s_val, offset);
            if ty.is_value_type() {
                Ok(builder.ins().load(ty.cl_type(), MemFlags::trusted(), field_ptr, 0))
            } else {
                Ok(field_ptr)
            }
        }
        HSharpExpr::Index(arr, idx) => {
            let a_val = compile_expr(builder, module, state, arr)?;
            let index = compile_expr(builder, module, state, idx)?;
            let a_ty = infer_type(arr, state.type_env, state.func_types, state.type_map)?;
            let (inner_ty, len) = match a_ty {
                HType::Array(inner, l) => (*inner, l),
                _ => return Err(anyhow::anyhow!("Index on non-array")),
            };
            let zero = builder.ins().iconst(types::I32, 0);
            let len_val = builder.ins().iconst(types::I32, len as i64);
            let lt_zero = builder.ins().icmp(IntCC::SignedLessThan, index, zero);
            let ge_len = builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, index, len_val);
            let oob = builder.ins().bor(lt_zero, ge_len);
            builder.ins().trapnz(oob, TrapCode::unwrap_user(0));
            let elem_size = inner_ty.size(state.type_map) as i64;
            let offset = builder.ins().imul_imm(index, elem_size);
            let elem_ptr = builder.ins().iadd(a_val, offset);
            if inner_ty.is_value_type() {
                Ok(builder.ins().load(inner_ty.cl_type(), MemFlags::trusted(), elem_ptr, 0))
            } else {
                Ok(elem_ptr)
            }
        }
        HSharpExpr::For(var, start, end, body) => {
            let start_val = compile_expr(builder, module, state, start)?;
            let end_val = compile_expr(builder, module, state, end)?;
            let head_b = builder.create_block();
            let body_b = builder.create_block();
            let exit_b = builder.create_block();
            // i32 = 4 bytes, alignment 4 (2^2)
            let iter_slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 4, 2));
            let iter_addr = builder.ins().stack_addr(types::I64, iter_slot, 0);
            builder.ins().store(MemFlags::trusted(), start_val, iter_addr, 0);
            state.vars.push(HashMap::new());
            state.type_env.push(HashMap::new());
            state.vars.last_mut().unwrap().insert(var.clone(), iter_addr);
            state.type_env.last_mut().unwrap().insert(var.clone(), HType::I32);
            builder.ins().jump(head_b, &[]);
            builder.switch_to_block(head_b);
            let iter_val = builder.ins().load(types::I32, MemFlags::trusted(), iter_addr, 0);
            let cmp = builder.ins().icmp(IntCC::SignedLessThan, iter_val, end_val);
            builder.ins().brif(cmp, body_b, &[], exit_b, &[]);
            builder.switch_to_block(body_b);
            compile_expr(builder, module, state, body)?;
            let iter_val_2 = builder.ins().load(types::I32, MemFlags::trusted(), iter_addr, 0);
            let one = builder.ins().iconst(types::I32, 1);
            let new_iter = builder.ins().iadd(iter_val_2, one);
            builder.ins().store(MemFlags::trusted(), new_iter, iter_addr, 0);
            builder.ins().jump(head_b, &[]);
            builder.switch_to_block(exit_b);
            state.vars.pop();
            state.type_env.pop();
            Ok(builder.ins().iconst(types::I32, 0))
        }
        HSharpExpr::Return(e) => {
            let val = compile_expr(builder, module, state, e)?;
            let free_call = module.declare_func_in_func(state.arena_free_id, builder.func);
            builder.ins().call(free_call, &[state.arena]);
            if ty.param_type() != types::INVALID {
                builder.ins().return_(&[val]);
            } else {
                builder.ins().return_(&[]);
            }
            Ok(builder.ins().iconst(types::I32, 0))
        }
    }
}
