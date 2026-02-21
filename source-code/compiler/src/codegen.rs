use crate::ast::*;
use crate::typechecker::{TypeChecker, FuncSig};
use crate::types::{StructOrUnion, HTypeExt};
use anyhow::Result;
use cranelift::prelude::*;
use cranelift::prelude::types as cl_types;
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
    pub func_types: &'a HashMap<String, FuncSig>,
    pub type_map: &'a HashMap<String, StructOrUnion>,
    pub arena: Value,
    pub in_direct: bool,
}

pub fn is_block_terminated(builder: &FunctionBuilder) -> bool {
    if builder.is_unreachable() {
        return true;
    }
    let block = builder.current_block().unwrap();
    if let Some(inst) = builder.func.layout.last_inst(block) {
        return builder.func.dfg.insts[inst].opcode().is_terminator();
    }
    false
}

fn emit_dead_block_value(builder: &mut FunctionBuilder) -> Value {
    let dead_block = builder.create_block();
    builder.switch_to_block(dead_block);
    builder.seal_block(dead_block);
    let val = builder.ins().iconst(cl_types::I32, 0);
    // Use an infinite loop as a terminator for dead code.
    builder.ins().jump(dead_block, &[]);
    val
}

fn get_expr_type(expr: &HSharpExpr, state: &CompilerState) -> Result<HType> {
    let checker = TypeChecker::new(state.type_map, state.func_types);
    checker.check_expr(expr, state.type_env)
}

fn is_unsigned(ty: &HType) -> bool {
    matches!(ty, HType::U8 | HType::U16 | HType::U32 | HType::U64)
}

// Compile expression as an L-value (address)
fn compile_lvalue(
    builder: &mut FunctionBuilder,
    module: &mut ObjectModule,
    state: &mut CompilerState,
    expr: &HSharpExpr,
    loop_ctx: Option<(Block, Block)>,
) -> Result<Value> {
    match expr {
        HSharpExpr::Var(name) => {
            state.vars.iter().rev().find_map(|m| m.get(name))
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("Undefined variable: {}", name))
        },
        // Deref (*ptr = val). The address is the value of 'ptr' expression.
        HSharpExpr::Unary(UnaryOp::Deref, inner) => {
            compile_expr(builder, module, state, inner, loop_ctx)
        },
        HSharpExpr::Field(inner, field_name) => {
            let base_addr = compile_lvalue(builder, module, state, inner, loop_ctx)?;
            let inner_ty = get_expr_type(inner, state)?;
            let struct_name = match inner_ty {
                HType::Struct(s, _) => s,
                HType::Pointer(b) => match *b { HType::Struct(s, _) => s, _ => return Err(anyhow::anyhow!("Field access on non-struct")) },
                _ => return Err(anyhow::anyhow!("Field access on non-struct"))
            };
            let struct_def = state.type_map.get(&struct_name).ok_or_else(|| anyhow::anyhow!("Unknown struct"))?;
            let offset = struct_def.field_offset(field_name, state.type_map);
            Ok(builder.ins().iadd_imm(base_addr, offset as i64))
        },
        HSharpExpr::Index(arr_expr, idx_expr) => {
            let base_addr = compile_lvalue(builder, module, state, arr_expr, loop_ctx)?;
            let idx_val = compile_expr(builder, module, state, idx_expr, loop_ctx)?;
            let arr_ty = get_expr_type(arr_expr, state)?;
            // Bounds Checking Logic
            if !state.in_direct {
                match &arr_ty {
                    HType::Slice(_) => {
                        // Slice layout: { ptr (offset 0), len (offset 8) }
                        // base_addr is address of the slice struct on stack
                        let len = builder.ins().load(cl_types::I64, MemFlags::trusted(), base_addr, 8);
                        let idx_i64 = builder.ins().sextend(cl_types::I64, idx_val); // Ensure comparison in I64
                        let out_of_bounds = builder.ins().icmp(IntCC::UnsignedGreaterThanOrEqual, idx_i64, len);
                        builder.ins().trapnz(out_of_bounds, TrapCode::user(1).unwrap());
                    },
                    HType::Array(_, size) => {
                        // Static array: len is constant known at compile time
                        let len = builder.ins().iconst(cl_types::I64, *size as i64);
                        let idx_i64 = builder.ins().sextend(cl_types::I64, idx_val);
                        let out_of_bounds = builder.ins().icmp(IntCC::UnsignedGreaterThanOrEqual, idx_i64, len);
                        builder.ins().trapnz(out_of_bounds, TrapCode::user(1).unwrap());
                    },
                    _ => {} // Pointer - unchecked
                }
            }
            // Handle different array types
            let (elem_ty, start_addr) = match arr_ty {
                HType::Array(inner, _) => (*inner.clone(), base_addr),
                HType::Slice(inner) => {
                    // Slice is { ptr, len }. Load ptr.
                    let ptr = builder.ins().load(cl_types::I64, MemFlags::trusted(), base_addr, 0);
                    (*inner.clone(), ptr)
                },
                HType::Pointer(inner) => (*inner.clone(), builder.ins().load(cl_types::I64, MemFlags::trusted(), base_addr, 0)),
                _ => return Err(anyhow::anyhow!("Index on non-array"))
            };
            let elem_size = elem_ty.size(state.type_map);
            let idx_i64 = builder.ins().uextend(cl_types::I64, idx_val); // Assume idx is i32, extend
            let offset = builder.ins().imul_imm(idx_i64, elem_size as i64);
            Ok(builder.ins().iadd(start_addr, offset))
        },
        // If expr is a Call/StructLit that returns an aggregate, compile_expr returns the address (L-value equivalent)
        HSharpExpr::Call(..) | HSharpExpr::StructLit(..) | HSharpExpr::Alloc(..) => {
            compile_expr(builder, module, state, expr, loop_ctx)
        },
        _ => Err(anyhow::anyhow!("Invalid l-value expression: {:?}", expr))
    }
}

pub fn compile_stmt(
    builder: &mut FunctionBuilder,
    module: &mut ObjectModule,
    state: &mut CompilerState,
    stmt: &HSharpStmt,
    loop_ctx: Option<(Block, Block)>, // (break_target, continue_target)
) -> Result<Value> {
    match stmt {
        HSharpStmt::Let(name, _, expr) => {
            let val = compile_expr(builder, module, state, expr, loop_ctx)?;
            let ty = get_expr_type(expr, state)?;
            let size = if ty.is_value_type() { ty.size(state.type_map) } else { 8 };
            let align = if ty.is_value_type() { ty.alignment(state.type_map) } else { 8 };
            let slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, align.ilog2() as u8));
            let addr = builder.ins().stack_addr(cl_types::I64, slot, 0);
            // Only emit stores if the block isn't already terminated (e.g. by a return in the let-expr)
            if !is_block_terminated(builder) {
                if ty.is_value_type() && !matches!(ty, HType::Slice(_)) {
                    builder.ins().store(MemFlags::trusted(), val, addr, 0);
                } else {
                    // Aggregate copy (like struct/slice) - val is pointer to source
                    let sz = builder.ins().iconst(cl_types::I64, size as i64);
                    let memcpy = module.declare_func_in_func(state.memcpy_id, builder.func);
                    builder.ins().call(memcpy, &[addr, val, sz]);
                }
            }
            state.vars.last_mut().unwrap().insert(name.clone(), addr);
            state.type_env.last_mut().unwrap().insert(name.clone(), ty);
            if !is_block_terminated(builder) {
                Ok(builder.ins().iconst(cl_types::I32, 0))
            } else {
                Ok(emit_dead_block_value(builder))
            }
        }
        HSharpStmt::Expr(expr) => compile_expr(builder, module, state, expr, loop_ctx),
        _ => {
            if !is_block_terminated(builder) {
                Ok(builder.ins().iconst(cl_types::I32, 0))
            } else {
                Ok(emit_dead_block_value(builder))
            }
        }
    }
}

pub fn compile_expr(
    builder: &mut FunctionBuilder,
    module: &mut ObjectModule,
    state: &mut CompilerState,
    expr: &HSharpExpr,
    loop_ctx: Option<(Block, Block)>,
) -> Result<Value> {
    // Optimization: Don't check type for Block/Direct immediately as it might involve scoping issues handled inside
    let ty = if !matches!(expr, HSharpExpr::Block(_) | HSharpExpr::Direct(_)) {
        get_expr_type(expr, state)?
    } else {
        HType::Unit
    };
    match expr {
        HSharpExpr::Assign(lhs, rhs) => {
            let r_val = compile_expr(builder, module, state, rhs, loop_ctx)?;
            let l_addr = compile_lvalue(builder, module, state, lhs, loop_ctx)?;
            let r_ty = get_expr_type(rhs, state)?;
            if !is_block_terminated(builder) {
                if r_ty.is_value_type() && !matches!(r_ty, HType::Slice(_)) && !matches!(r_ty, HType::Struct(_, _)) {
                    builder.ins().store(MemFlags::trusted(), r_val, l_addr, 0);
                } else {
                    let size = r_ty.size(state.type_map);
                    let sz = builder.ins().iconst(cl_types::I64, size as i64);
                    let memcpy = module.declare_func_in_func(state.memcpy_id, builder.func);
                    builder.ins().call(memcpy, &[l_addr, r_val, sz]);
                }
            }
            Ok(r_val)
        },
        HSharpExpr::Break => {
            if let Some((break_target, _)) = loop_ctx {
                builder.ins().jump(break_target, &[]);
                Ok(emit_dead_block_value(builder))
            } else { Err(anyhow::anyhow!("Break outside loop")) }
        }
        HSharpExpr::Continue => {
            if let Some((_, continue_target)) = loop_ctx {
                builder.ins().jump(continue_target, &[]);
                Ok(emit_dead_block_value(builder))
            } else { Err(anyhow::anyhow!("Continue outside loop")) }
        }
        HSharpExpr::Literal(lit) => Ok(match lit {
            HSharpLiteral::Int(n) => builder.ins().iconst(cl_types::I32, *n as i64),
                                       HSharpLiteral::Bool(b) => builder.ins().iconst(cl_types::I8, if *b { 1 } else { 0 }),
                                       HSharpLiteral::Float(f) => builder.ins().f64const(*f),
                                       HSharpLiteral::Byte(b) => builder.ins().iconst(cl_types::I8, *b as i64),
                                       HSharpLiteral::String(s) | HSharpLiteral::RawString(s) => {
                                           let data_id = if let Some(&id) = state.string_constants.get(s) { id } else {
                                               let name = format!("str_{}", state.string_constants.len());
                                               let mut desc = DataDescription::new();
                                               // C-String Support: Append NULL byte
                                               let mut bytes = s.as_bytes().to_vec();
                                               bytes.push(0);
                                               desc.define(bytes.into_boxed_slice());
                                               let id = module.declare_data(&name, Linkage::Local, false, false)?;
                                               module.define_data(id, &desc)?;
                                               state.string_constants.insert(s.clone(), id);
                                               id
                                           };
                                           let gv = module.declare_data_in_func(data_id, builder.func);
                                           let ptr = builder.ins().global_value(cl_types::I64, gv);
                                           let len = builder.ins().iconst(cl_types::I64, s.len() as i64);
                                           let slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 16, 3));
                                           let addr = builder.ins().stack_addr(cl_types::I64, slot, 0);
                                           builder.ins().store(MemFlags::trusted(), ptr, addr, 0);
                                           builder.ins().store(MemFlags::trusted(), len, addr, 8);
                                           addr
                                       }
        }),
        HSharpExpr::If(cond, then_expr, else_expr) => {
            let cond_val = compile_expr(builder, module, state, cond, loop_ctx)?;
            let then_bb = builder.create_block();
            let else_bb = builder.create_block();
            let merge_bb = builder.create_block();
            // Allocate a stack slot for the result if needed
            let result_loc = if ty != HType::Unit {
                let size = ty.size(state.type_map);
                let align = ty.alignment(state.type_map);
                let slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, align.ilog2() as u8));
                Some(builder.ins().stack_addr(cl_types::I64, slot, 0))
            } else {
                None
            };
            if !is_block_terminated(builder) {
                builder.ins().brif(cond_val, then_bb, &[], else_bb, &[]);
            }
            // Then branch
            builder.switch_to_block(then_bb);
            builder.seal_block(then_bb);
            let then_val = compile_expr(builder, module, state, then_expr, loop_ctx)?;
            if !is_block_terminated(builder) {
                if let Some(addr) = result_loc {
                    if ty.is_value_type() && !matches!(ty, HType::Slice(_)) && !matches!(ty, HType::Struct(_, _)) {
                        builder.ins().store(MemFlags::trusted(), then_val, addr, 0);
                    } else {
                        let size = ty.size(state.type_map);
                        let sz = builder.ins().iconst(cl_types::I64, size as i64);
                        let memcpy = module.declare_func_in_func(state.memcpy_id, builder.func);
                        builder.ins().call(memcpy, &[addr, then_val, sz]);
                    }
                }
                builder.ins().jump(merge_bb, &[]);
            }
            // Else branch
            builder.switch_to_block(else_bb);
            builder.seal_block(else_bb);
            let else_val = if let Some(e) = else_expr {
                compile_expr(builder, module, state, e, loop_ctx)?
            } else {
                builder.ins().iconst(cl_types::I32, 0)
            };
            if !is_block_terminated(builder) {
                if else_expr.is_some() {
                    if let Some(addr) = result_loc {
                        if ty.is_value_type() && !matches!(ty, HType::Slice(_)) && !matches!(ty, HType::Struct(_, _)) {
                            builder.ins().store(MemFlags::trusted(), else_val, addr, 0);
                        } else {
                            let size = ty.size(state.type_map);
                            let sz = builder.ins().iconst(cl_types::I64, size as i64);
                            let memcpy = module.declare_func_in_func(state.memcpy_id, builder.func);
                            builder.ins().call(memcpy, &[addr, else_val, sz]);
                        }
                    }
                }
                builder.ins().jump(merge_bb, &[]);
            }
            // Merge branch
            builder.switch_to_block(merge_bb);
            builder.seal_block(merge_bb);
            if let Some(addr) = result_loc {
                if ty.is_value_type() && !matches!(ty, HType::Slice(_)) && !matches!(ty, HType::Struct(_, _)) {
                    Ok(builder.ins().load(ty.cl_type(), MemFlags::trusted(), addr, 0))
                } else {
                    Ok(addr)
                }
            } else {
                Ok(builder.ins().iconst(cl_types::I32, 0))
            }
        },
        HSharpExpr::Alloc(size_expr) => {
            let size_val = compile_expr(builder, module, state, size_expr, loop_ctx)?;
            // Extend i32 size to i64
            let size_ty = get_expr_type(size_expr, state)?;
            let size_i64 = if size_ty == HType::I32 { builder.ins().uextend(cl_types::I64, size_val) } else { size_val };
            let alloc_func = module.declare_func_in_func(state.arena_alloc_id, builder.func);
            let call = builder.ins().call(alloc_func, &[state.arena, size_i64]);
            Ok(builder.inst_results(call)[0])
        },
        HSharpExpr::Dealloc(_) => {
            Ok(builder.ins().iconst(cl_types::I32, 0))
        },
        // Unary Ops: AddrOf(BitAnd), Deref(Mul), Neg(Sub), BitNot(Not)
        HSharpExpr::Unary(op, inner) => {
            match op {
                UnaryOp::AddrOf => compile_lvalue(builder, module, state, inner, loop_ctx),
                UnaryOp::Deref => {
                    let ptr = compile_expr(builder, module, state, inner, loop_ctx)?;
                    if ty.is_value_type() && !matches!(ty, HType::Slice(_)) && !matches!(ty, HType::Struct(_, _)) {
                        Ok(builder.ins().load(ty.cl_type(), MemFlags::trusted(), ptr, 0))
                    } else {
                        Ok(ptr)
                    }
                },
                UnaryOp::Neg => {
                    let v = compile_expr(builder, module, state, inner, loop_ctx)?;
                    Ok(builder.ins().ineg(v))
                },
                UnaryOp::BitNot => {
                    // Assuming BitNot or BoolNot depending on type.
                    let v = compile_expr(builder, module, state, inner, loop_ctx)?;
                    Ok(builder.ins().bnot(v))
                }
            }
        },
        HSharpExpr::SizeOf(t) => {
            let s = t.size(state.type_map);
            Ok(builder.ins().iconst(cl_types::I32, s as i64))
        },
        HSharpExpr::Return(expr) => {
            let val = compile_expr(builder, module, state, expr, loop_ctx)?;
            // Cleanup arena before return
            let free_func = module.declare_func_in_func(state.arena_free_id, builder.func);
            builder.ins().call(free_func, &[state.arena]);
            let expr_ty = get_expr_type(expr, state)?;
            let ret_ty = expr_ty.cl_type();
            // Coercion logic similar to end of function
            let val_ty = builder.func.dfg.value_type(val);
            let final_val = if val_ty == cl_types::I32 && ret_ty == cl_types::I64 {
                builder.ins().sextend(cl_types::I64, val)
            } else if val_ty == cl_types::I64 && ret_ty == cl_types::I32 {
                builder.ins().ireduce(cl_types::I32, val)
            } else {
                val
            };
            if ret_ty != cl_types::INVALID {
                builder.ins().return_(&[final_val]);
            } else {
                builder.ins().return_(&[]);
            }
            Ok(emit_dead_block_value(builder))
        },
        HSharpExpr::Call(name, args) => {
            let func_id = *state.func_ids.get(name).ok_or_else(|| anyhow::anyhow!("Function not found: {}", name))?;
            let mut arg_vals = Vec::new();
            for arg in args {
                arg_vals.push(compile_expr(builder, module, state, arg, loop_ctx)?);
            }
            let call = module.declare_func_in_func(func_id, builder.func);
            let call_inst = builder.ins().call(call, &arg_vals);
            let results = builder.inst_results(call_inst);
            if !results.is_empty() { Ok(results[0]) } else { Ok(builder.ins().iconst(cl_types::I32, 0)) }
        },
        HSharpExpr::Cast(target_ty, inner) => {
            let val = compile_expr(builder, module, state, inner, loop_ctx)?;
            let src_ty = get_expr_type(inner, state)?;
            match (src_ty, target_ty) {
                (HType::I32, HType::F64) => Ok(builder.ins().fcvt_from_sint(cl_types::F64, val)),
                (HType::F64, HType::I32) => Ok(builder.ins().fcvt_to_sint_sat(cl_types::I32, val)),
                (HType::I32, HType::I8) => Ok(builder.ins().ireduce(cl_types::I8, val)),
                (HType::I32, HType::I64) => Ok(builder.ins().uextend(cl_types::I64, val)),
                (HType::I64, HType::I32) => Ok(builder.ins().ireduce(cl_types::I32, val)),
                (HType::Pointer(_), HType::I64) => Ok(val),
                (HType::I64, HType::Pointer(_)) => Ok(val),
                _ => Ok(val)
            }
        },
        HSharpExpr::Match(target, cases, default) => {
            let t_val = compile_expr(builder, module, state, target, loop_ctx)?;
            let merge_block = builder.create_block();
            // Result slot
            let result_loc = if ty != HType::Unit {
                let size = ty.size(state.type_map);
                let align = ty.alignment(state.type_map);
                let slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, align.ilog2() as u8));
                Some(builder.ins().stack_addr(cl_types::I64, slot, 0))
            } else {
                None
            };
            let mut handled_all = false;
            for (cond, body) in cases {
                let is_wildcard = if let HSharpExpr::Var(n) = cond { n == "_" } else { false };
                if is_wildcard {
                    // Unconditional match
                    let body_block = builder.create_block();
                    if !is_block_terminated(builder) {
                        builder.ins().jump(body_block, &[]);
                    }
                    builder.switch_to_block(body_block);
                    builder.seal_block(body_block);
                    let val = compile_expr(builder, module, state, body, loop_ctx)?;
                    if !is_block_terminated(builder) {
                        if let Some(addr) = result_loc {
                            if ty.is_value_type() && !matches!(ty, HType::Slice(_)) && !matches!(ty, HType::Struct(_, _)) {
                                builder.ins().store(MemFlags::trusted(), val, addr, 0);
                            } else {
                                let size = ty.size(state.type_map);
                                let sz = builder.ins().iconst(cl_types::I64, size as i64);
                                let memcpy = module.declare_func_in_func(state.memcpy_id, builder.func);
                                builder.ins().call(memcpy, &[addr, val, sz]);
                            }
                        }
                        builder.ins().jump(merge_block, &[]);
                    }
                    handled_all = true;
                    break;
                } else {
                    // Comparison case
                    let next_case = builder.create_block();
                    let c_val = compile_expr(builder, module, state, cond, loop_ctx)?;
                    let cmp = builder.ins().icmp(IntCC::Equal, t_val, c_val);
                    let body_block = builder.create_block();
                    if !is_block_terminated(builder) {
                        builder.ins().brif(cmp, body_block, &[], next_case, &[]);
                    }
                    builder.switch_to_block(body_block);
                    builder.seal_block(body_block);
                    let val = compile_expr(builder, module, state, body, loop_ctx)?;
                    if !is_block_terminated(builder) {
                        if let Some(addr) = result_loc {
                            if ty.is_value_type() && !matches!(ty, HType::Slice(_)) && !matches!(ty, HType::Struct(_, _)) {
                                builder.ins().store(MemFlags::trusted(), val, addr, 0);
                            } else {
                                let size = ty.size(state.type_map);
                                let sz = builder.ins().iconst(cl_types::I64, size as i64);
                                let memcpy = module.declare_func_in_func(state.memcpy_id, builder.func);
                                builder.ins().call(memcpy, &[addr, val, sz]);
                            }
                        }
                        builder.ins().jump(merge_block, &[]);
                    }
                    builder.switch_to_block(next_case);
                    builder.seal_block(next_case);
                }
            }
            if !handled_all {
                if let Some(d) = default {
                    let val = compile_expr(builder, module, state, d, loop_ctx)?;
                    if !is_block_terminated(builder) {
                        if let Some(addr) = result_loc {
                            if ty.is_value_type() && !matches!(ty, HType::Slice(_)) && !matches!(ty, HType::Struct(_, _)) {
                                builder.ins().store(MemFlags::trusted(), val, addr, 0);
                            } else {
                                let size = ty.size(state.type_map);
                                let sz = builder.ins().iconst(cl_types::I64, size as i64);
                                let memcpy = module.declare_func_in_func(state.memcpy_id, builder.func);
                                builder.ins().call(memcpy, &[addr, val, sz]);
                            }
                        }
                    }
                }
                if !is_block_terminated(builder) {
                    builder.ins().jump(merge_block, &[]);
                }
            }
            builder.switch_to_block(merge_block);
            builder.seal_block(merge_block);
            if let Some(addr) = result_loc {
                if ty.is_value_type() && !matches!(ty, HType::Slice(_)) && !matches!(ty, HType::Struct(_, _)) {
                    Ok(builder.ins().load(ty.cl_type(), MemFlags::trusted(), addr, 0))
                } else {
                    Ok(addr)
                }
            } else {
                Ok(builder.ins().iconst(cl_types::I32, 0))
            }
        },
        HSharpExpr::While(cond, body) => {
            let head = builder.create_block();
            let exit = builder.create_block();
            let body_b = builder.create_block();
            if !is_block_terminated(builder) {
                builder.ins().jump(head, &[]);
            }
            builder.switch_to_block(head);
            // Cannot seal head yet (backedge)
            let c = compile_expr(builder, module, state, cond, loop_ctx)?;
            if !is_block_terminated(builder) {
                builder.ins().brif(c, body_b, &[], exit, &[]);
            }
            builder.switch_to_block(body_b);
            builder.seal_block(body_b);
            compile_expr(builder, module, state, body, Some((exit, head)))?;
            if !is_block_terminated(builder) {
                builder.ins().jump(head, &[]);
            }
            builder.switch_to_block(exit);
            builder.seal_block(head); // Now head is fully connected
            builder.seal_block(exit);
            Ok(builder.ins().iconst(cl_types::I32, 0))
        },
        HSharpExpr::For(var, start, end, body) => {
            let start_val = compile_expr(builder, module, state, start, loop_ctx)?;
            let end_val = compile_expr(builder, module, state, end, loop_ctx)?;
            // Stack slot for 'i'
            let slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 4, 0));
            let i_addr = builder.ins().stack_addr(cl_types::I64, slot, 0);
            builder.ins().store(MemFlags::trusted(), start_val, i_addr, 0);
            state.vars.last_mut().unwrap().insert(var.clone(), i_addr);
            state.type_env.last_mut().unwrap().insert(var.clone(), HType::I32);
            let head_bb = builder.create_block();
            let body_bb = builder.create_block();
            let exit_bb = builder.create_block();
            if !is_block_terminated(builder) {
                builder.ins().jump(head_bb, &[]);
            }
            builder.switch_to_block(head_bb);
            let curr_i = builder.ins().load(cl_types::I32, MemFlags::trusted(), i_addr, 0);
            let cmp = builder.ins().icmp(IntCC::SignedLessThan, curr_i, end_val);
            builder.ins().brif(cmp, body_bb, &[], exit_bb, &[]);
            builder.switch_to_block(body_bb);
            builder.seal_block(body_bb);
            compile_expr(builder, module, state, body, Some((exit_bb, head_bb)))?;
            if !is_block_terminated(builder) {
                // Increment i
                let i_val = builder.ins().load(cl_types::I32, MemFlags::trusted(), i_addr, 0);
                let one = builder.ins().iconst(cl_types::I32, 1);
                let next_i = builder.ins().iadd(i_val, one);
                builder.ins().store(MemFlags::trusted(), next_i, i_addr, 0);
                builder.ins().jump(head_bb, &[]);
            }
            builder.switch_to_block(exit_bb);
            builder.seal_block(head_bb);
            builder.seal_block(exit_bb);
            Ok(builder.ins().iconst(cl_types::I32, 0))
        },
        HSharpExpr::Var(name) => {
            let addr = *state.vars.iter().rev().find_map(|m| m.get(name))
            .ok_or_else(|| anyhow::anyhow!("Undefined variable: {}", name))?;
            if ty.is_value_type() && !matches!(ty, HType::Slice(_)) && !matches!(ty, HType::Struct(_, _)) {
                Ok(builder.ins().load(ty.cl_type(), MemFlags::trusted(), addr, 0))
            } else {
                Ok(addr)
            }
        },
        HSharpExpr::MethodCall(obj, method, args) => {
            let obj_ty = get_expr_type(obj, state)?;
            let struct_name = match obj_ty { HType::Struct(s, _) => s, HType::Pointer(b) => match *b { HType::Struct(s, _) => s, _ => "".into() }, _ => "".into() };
            let mangled = format!("{}_{}", struct_name, method);
            let fid = *state.func_ids.get(&mangled).ok_or_else(|| anyhow::anyhow!("Method not found: {}", mangled))?;
            let mut vals = Vec::new();
            for a in args { vals.push(compile_expr(builder, module, state, a, loop_ctx)?); }
            let call = module.declare_func_in_func(fid, builder.func);
            let call_inst = builder.ins().call(call, &vals);
            let results = builder.inst_results(call_inst);
            if !results.is_empty() { Ok(results[0]) } else { Ok(builder.ins().iconst(cl_types::I32, 0)) }
        },
        HSharpExpr::BinOp(op, left, right) => {
            let l = compile_expr(builder, module, state, left, loop_ctx)?;
            let r = compile_expr(builder, module, state, right, loop_ctx)?;
            let l_ty = get_expr_type(left, state)?;
            match op {
                HSharpOp::Add => Ok(builder.ins().iadd(l, r)),
                HSharpOp::Sub => Ok(builder.ins().isub(l, r)),
                HSharpOp::Mul => Ok(builder.ins().imul(l, r)),
                HSharpOp::Div => {
                    if is_unsigned(&l_ty) {
                        Ok(builder.ins().udiv(l, r))
                    } else {
                        Ok(builder.ins().sdiv(l, r))
                    }
                },
                HSharpOp::Mod => {
                    if is_unsigned(&l_ty) {
                        Ok(builder.ins().urem(l, r))
                    } else {
                        Ok(builder.ins().srem(l, r))
                    }
                },
                HSharpOp::BitAnd => Ok(builder.ins().band(l, r)),
                HSharpOp::BitOr => Ok(builder.ins().bor(l, r)),
                HSharpOp::BitXor => Ok(builder.ins().bxor(l, r)),
                HSharpOp::Shl => Ok(builder.ins().ishl(l, r)),
                HSharpOp::Shr => {
                    if is_unsigned(&l_ty) {
                        Ok(builder.ins().ushr(l, r))
                    } else {
                        Ok(builder.ins().sshr(l, r))
                    }
                },
                HSharpOp::Eq => Ok(builder.ins().icmp(IntCC::Equal, l, r)),
                HSharpOp::Ne => Ok(builder.ins().icmp(IntCC::NotEqual, l, r)),
                HSharpOp::Lt => {
                    let cc = if is_unsigned(&l_ty) {
                        IntCC::UnsignedLessThan
                    } else {
                        IntCC::SignedLessThan
                    };
                    Ok(builder.ins().icmp(cc, l, r))
                },
                HSharpOp::Gt => {
                    let cc = if is_unsigned(&l_ty) {
                        IntCC::UnsignedGreaterThan
                    } else {
                        IntCC::SignedGreaterThan
                    };
                    Ok(builder.ins().icmp(cc, l, r))
                },
                HSharpOp::Le => {
                    let cc = if is_unsigned(&l_ty) {
                        IntCC::UnsignedLessThanOrEqual
                    } else {
                        IntCC::SignedLessThanOrEqual
                    };
                    Ok(builder.ins().icmp(cc, l, r))
                },
                HSharpOp::Ge => {
                    let cc = if is_unsigned(&l_ty) {
                        IntCC::UnsignedGreaterThanOrEqual
                    } else {
                        IntCC::SignedGreaterThanOrEqual
                    };
                    Ok(builder.ins().icmp(cc, l, r))
                },
                _ => Err(anyhow::anyhow!("Unsupported binary operator in codegen: {:?}", op))
            }
        },
        HSharpExpr::Block(stmts) => {
            state.vars.push(HashMap::new()); state.type_env.push(HashMap::new());
            let mut last = if !is_block_terminated(builder) {
                builder.ins().iconst(cl_types::I32, 0)
            } else {
                emit_dead_block_value(builder)
            };
            for s in stmts {
                if !is_block_terminated(builder) {
                    last = compile_stmt(builder, module, state, s, loop_ctx)?;
                }
            }
            // RAII Note: Here we would insert calls to drop/free for variables in the current scope
            state.vars.pop(); state.type_env.pop();
            Ok(last)
        },
        HSharpExpr::Direct(inner) => {
            let old_direct = state.in_direct;
            state.in_direct = true;
            let res = compile_expr(builder, module, state, inner, loop_ctx);
            state.in_direct = old_direct;
            res
        },
        HSharpExpr::Write(expr) => {
            let val = compile_expr(builder, module, state, expr, loop_ctx)?;
            let arg_ty = get_expr_type(expr, state)?;
            match arg_ty {
                HType::I32 => {
                    let f = module.declare_func_in_func(state.write_int_id, builder.func);
                    builder.ins().call(f, &[val]);
                },
                HType::F64 => {
                    let f = module.declare_func_in_func(state.write_float_id, builder.func);
                    builder.ins().call(f, &[val]);
                },
                HType::Struct(name, _) if name == "String" => {
                    let f = module.declare_func_in_func(state.write_str_id, builder.func);
                    builder.ins().call(f, &[val]);
                },
                _ => {}
            }
            Ok(builder.ins().iconst(cl_types::I32, 0))
        },
        HSharpExpr::Field(..) | HSharpExpr::Index(..) => {
            let addr = compile_lvalue(builder, module, state, expr, loop_ctx)?;
            if ty.is_value_type() && !matches!(ty, HType::Slice(_)) && !matches!(ty, HType::Struct(_, _)) {
                Ok(builder.ins().load(ty.cl_type(), MemFlags::trusted(), addr, 0))
            } else {
                Ok(addr)
            }
        },
        HSharpExpr::StructLit(name, fields) => {
            let size = ty.size(state.type_map);
            let align = ty.alignment(state.type_map);
            let slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, align.ilog2() as u8));
            let base_addr = builder.ins().stack_addr(cl_types::I64, slot, 0);
            // Note: name is ignored here because we trust the typechecker/monomorphization
            // to have resolved the type correctly. The struct layout is retrieved via
            // ty.size() which internally looks up the name.
            let struct_name = match ty {
                HType::Struct(n, _) => n,
                _ => return Err(anyhow::anyhow!("StructLit type mismatch")),
            };
            let struct_def = state.type_map.get(&struct_name).ok_or_else(|| anyhow::anyhow!("Unknown struct: {}", struct_name))?;
            if let StructOrUnion::Struct(def_fields) = struct_def {
                for (i, expr) in fields.iter().enumerate() {
                    if i >= def_fields.len() { break; }
                    let (fname, fty) = &def_fields[i];
                    let offset = struct_def.field_offset(fname, state.type_map);
                    let val = compile_expr(builder, module, state, expr, loop_ctx)?;
                    let addr = builder.ins().iadd_imm(base_addr, offset as i64);
                    if fty.is_value_type() && !matches!(fty, HType::Slice(_)) && !matches!(fty, HType::Struct(_, _)) {
                        builder.ins().store(MemFlags::trusted(), val, addr, 0);
                    } else {
                        let size = fty.size(state.type_map);
                        let sz = builder.ins().iconst(cl_types::I64, size as i64);
                        let memcpy = module.declare_func_in_func(state.memcpy_id, builder.func);
                        builder.ins().call(memcpy, &[addr, val, sz]);
                    }
                }
            }
            Ok(base_addr)
        },
        HSharpExpr::ArrayLit(elems) => {
            let len = elems.len();
            if len == 0 { return Ok(builder.ins().iconst(cl_types::I64, 0)); }
            let inner_ty = get_expr_type(&elems[0], state)?;
            let size = inner_ty.size(state.type_map) * len as u32;
            let align = inner_ty.alignment(state.type_map);
            let slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, align.ilog2() as u8));
            let base_addr = builder.ins().stack_addr(cl_types::I64, slot, 0);
            let elem_size = inner_ty.size(state.type_map);
            for (i, e) in elems.iter().enumerate() {
                let val = compile_expr(builder, module, state, e, loop_ctx)?;
                let offset = (i as u32 * elem_size) as i64;
                let addr = builder.ins().iadd_imm(base_addr, offset);
                if inner_ty.is_value_type() && !matches!(inner_ty, HType::Slice(_)) && !matches!(inner_ty, HType::Struct(_, _)) {
                    builder.ins().store(MemFlags::trusted(), val, addr, 0);
                } else {
                    let sz = builder.ins().iconst(cl_types::I64, elem_size as i64);
                    let memcpy = module.declare_func_in_func(state.memcpy_id, builder.func);
                    builder.ins().call(memcpy, &[addr, val, sz]);
                }
            }
            Ok(base_addr)
        },
        _ => Err(anyhow::anyhow!("Unsupported expression in codegen: {:?}", expr))
    }
}
