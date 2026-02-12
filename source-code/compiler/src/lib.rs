pub mod ast;
pub mod codegen;
pub mod typechecker;

use crate::ast::*;
use crate::codegen::{compile_expr, CompilerState, is_block_terminated}; // compile_stmt removed from import
use anyhow::{Context, Result};
use cranelift::prelude::*;
use cranelift::prelude::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataId, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::HashMap;
use std::fs;

pub fn compile_program(
    program: &HSharpProgram,
    output_path: &str,
) -> Result<()> {
    let mut type_map: HashMap<String, StructOrUnion> = HashMap::new();
    // Inject core String struct: { ptr: *i8, len: i64 }
    type_map.insert("String".to_string(), StructOrUnion::Struct(vec![
        ("ptr".to_string(), HType::Pointer(Box::new(HType::I8))),
                                                                ("len".to_string(), HType::I64), // Slice length often pointer-sized, using i64
    ]));

    for stmt in &program.stmts {
        match stmt {
            HSharpStmt::StructDef(name, fields) => { type_map.insert(name.clone(), StructOrUnion::Struct(fields.clone())); }
            HSharpStmt::UnionDef(name, fields) => { type_map.insert(name.clone(), StructOrUnion::Union(fields.clone())); }
            _ => {}
        }
    }

    let mut flag_builder = settings::builder();
    flag_builder.set("opt_level", "speed").unwrap();
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

    // Runtime imports
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(types::I64)); sig.returns.push(AbiParam::new(types::I64));
    let malloc_id = module.declare_function("malloc", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(types::I64));
    let free_id = module.declare_function("free", Linkage::Import, &sig)?;

    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(types::I32));
    let write_int_id = module.declare_function("write_int", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(types::I64)); // Writes string ptr/len? Simplified: pointer
    let write_str_id = module.declare_function("write_str", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(types::F64));
    let write_float_id = module.declare_function("write_float", Linkage::Import, &sig)?;

    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(types::I64)); sig.returns.push(AbiParam::new(types::I64));
    let arena_new_id = module.declare_function("arena_new", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(types::I64)); sig.params.push(AbiParam::new(types::I64)); sig.returns.push(AbiParam::new(types::I64));
    let arena_alloc_id = module.declare_function("arena_alloc", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(types::I64));
    let arena_free_id = module.declare_function("arena_free", Linkage::Import, &sig)?;
    let mut sig = Signature::new(CallConv::SystemV); sig.params.push(AbiParam::new(types::I64)); sig.params.push(AbiParam::new(types::I64)); sig.params.push(AbiParam::new(types::I64));
    let memcpy_id = module.declare_function("memcpy", Linkage::Import, &sig)?;

    let mut string_constants: HashMap<String, DataId> = HashMap::new();
    let mut func_ids: HashMap<String, FuncId> = HashMap::new();
    let mut func_types: HashMap<String, (Vec<HType>, HType)> = HashMap::new();
    let mut func_sigs: HashMap<String, Signature> = HashMap::new();

    // Register built-in functions so typechecker and codegen know about them
    func_types.insert("write_int".to_string(), (vec![HType::I32], HType::Unit));
    func_ids.insert("write_int".to_string(), write_int_id);

    func_types.insert("write_float".to_string(), (vec![HType::F64], HType::Unit));
    func_ids.insert("write_float".to_string(), write_float_id);

    func_types.insert("write_str".to_string(), (vec![HType::Struct("String".to_string())], HType::Unit));
    func_ids.insert("write_str".to_string(), write_str_id);

    // Collect functions (including Impl methods mangled as Type_method)
    let mut flattened_stmts = Vec::new();
    for stmt in &program.stmts {
        match stmt {
            HSharpStmt::Impl(struct_name, methods) => {
                for m in methods {
                    if let HSharpStmt::FunctionDef(fn_name, params, ret, body) = m {
                        let mangled = format!("{}_{}", struct_name, fn_name);
                        flattened_stmts.push(HSharpStmt::FunctionDef(mangled, params.clone(), ret.clone(), body.clone()));
                    }
                }
            },
            _ => flattened_stmts.push(stmt.clone())
        }
    }

    // Declaration Pass
    for stmt in &flattened_stmts {
        if let HSharpStmt::FunctionDef(name, params, ret, _) = stmt {
            let param_tys = params.iter().map(|(_, t)| t.clone()).collect::<Vec<_>>();
            func_types.insert(name.clone(), (param_tys.clone(), ret.clone()));
            let mut sig = module.make_signature();
            for pty in &param_tys {
                sig.params.push(AbiParam::new(pty.param_type()));
            }
            if ret.param_type() != types::INVALID {
                sig.returns.push(AbiParam::new(ret.param_type()));
            }
            let linkage = if name == "main" { Linkage::Export } else { Linkage::Local };
            let func_id = module.declare_function(name, linkage, &sig)?;
            func_ids.insert(name.clone(), func_id);
            func_sigs.insert(name.clone(), sig);
        }
    }

    // Compilation Pass
    for stmt in &flattened_stmts {
        if let HSharpStmt::FunctionDef(name, params, ret, body) = stmt {
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
                let param_repr = builder.block_params(entry_block)[i];
                let is_aggregate = !pty.is_value_type() || matches!(pty, HType::Slice(_));
                let size = pty.size(&type_map);
                let align = pty.alignment(&type_map);

                // Always allocate a stack slot for parameters.
                // If it's a value type, store the value.
                // If it's an aggregate (passed by reference/pointer), copy the data from the pointer to the stack (Pass-by-Value semantics).
                let slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, align.ilog2() as u8));
                let addr = builder.ins().stack_addr(types::I64, slot, 0);

                if !is_aggregate {
                    builder.ins().store(MemFlags::trusted(), param_repr, addr, 0);
                } else {
                    // param_repr is the pointer to the source data. Memcpy to local stack.
                    let sz = builder.ins().iconst(types::I64, size as i64);
                    let memcpy = module.declare_func_in_func(memcpy_id, builder.func);
                    builder.ins().call(memcpy, &[addr, param_repr, sz]);
                }

                vars.last_mut().unwrap().insert(pname.clone(), addr);
                type_env.last_mut().unwrap().insert(pname.clone(), pty.clone());
            }

            let capacity = builder.ins().iconst(types::I64, 1_048_576);
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

            // Implicit return at end of function block.
            // Only generate if the block isn't already terminated (e.g. by explicit return or infinite loop).
            if !is_block_terminated(&builder) {
                let free_call = module.declare_func_in_func(arena_free_id, builder.func);
                builder.ins().call(free_call, &[arena]);

                let ret_ty = ret.param_type();
                if ret_ty != types::INVALID {
                    let val_ty = builder.func.dfg.value_type(val);
                    // Coerce i32 to i64 if needed (e.g. Unit or Int literal returning as I64)
                    let final_val = if val_ty == types::I32 && ret_ty == types::I64 {
                        builder.ins().sextend(types::I64, val)
                    } else if val_ty == types::I64 && ret_ty == types::I32 {
                        builder.ins().ireduce(types::I32, val)
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

    let product = module.finish();
    let bytes = product.emit()?;
    fs::write(output_path, bytes).context("Failed to write object file")?;
    Ok(())
}
