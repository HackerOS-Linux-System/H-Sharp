mod ast;
mod codegen;

use crate::ast::*;
use crate::codegen::{compile_expr, compile_stmt, CompilerState};
use anyhow::{Context, Result};
use cranelift::prelude::*;
use cranelift::prelude::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataId, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::HashMap;
use std::fs;

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
    let mut type_map: HashMap<String, StructOrUnion> = HashMap::new();
    for stmt in &program.stmts {
        match stmt {
            HSharpStmt::StructDef(name, fields) => {
                if type_map
                    .insert(name.clone(), StructOrUnion::Struct(fields.clone()))
                    .is_some()
                    {
                        return Err(anyhow::anyhow!("Duplicate struct definition: {}", name));
                    }
            }
            HSharpStmt::UnionDef(name, fields) => {
                if type_map
                    .insert(name.clone(), StructOrUnion::Union(fields.clone()))
                    .is_some()
                    {
                        return Err(anyhow::anyhow!("Duplicate union definition: {}", name));
                    }
            }
            _ => {}
        }
    }
    compile_program(&program, output_obj, &type_map)?;
    Ok(())
}

fn compile_program(
    program: &HSharpProgram,
    output_path: &str,
    type_map: &HashMap<String, StructOrUnion>,
) -> Result<()> {
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

    // Helpers to create signatures
    let signature_for_alloc = |_module: &ObjectModule| {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        sig
    };
    let signature_for_dealloc = |_| {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig
    };
    let signature_for_write_int = |_| {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I32));
        sig
    };
    let signature_for_write_str = |_| {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig
    };
    let signature_for_write_float = |_| {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::F64));
        sig
    };
    let signature_for_arena_new = |_| {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        sig
    };
    let signature_for_arena_alloc = |_| {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        sig
    };
    let signature_for_arena_free = |_| {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig
    };
    let signature_for_memcpy = |_| {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64)); // dst
        sig.params.push(AbiParam::new(types::I64)); // src
        sig.params.push(AbiParam::new(types::I64)); // len
        sig
    };

    let malloc_id =
    module.declare_function("malloc", Linkage::Import, &signature_for_alloc(&module))?;
    let free_id =
    module.declare_function("free", Linkage::Import, &signature_for_dealloc(&module))?;
    let write_int_id = module.declare_function(
        "write_int",
        Linkage::Import,
        &signature_for_write_int(&module),
    )?;
    let write_str_id = module.declare_function(
        "write_str",
        Linkage::Import,
        &signature_for_write_str(&module),
    )?;
    let write_float_id = module.declare_function(
        "write_float",
        Linkage::Import,
        &signature_for_write_float(&module),
    )?;
    let arena_new_id = module.declare_function(
        "arena_new",
        Linkage::Import,
        &signature_for_arena_new(&module),
    )?;
    let arena_alloc_id = module.declare_function(
        "arena_alloc",
        Linkage::Import,
        &signature_for_arena_alloc(&module),
    )?;
    let arena_free_id = module.declare_function(
        "arena_free",
        Linkage::Import,
        &signature_for_arena_free(&module),
    )?;
    let memcpy_id =
    module.declare_function("memcpy", Linkage::Import, &signature_for_memcpy(&module))?;

    let has_functions = program
    .stmts
    .iter()
    .any(|s| matches!(s, HSharpStmt::FunctionDef(..)));
    let mut string_constants: HashMap<String, DataId> = HashMap::new();
    let mut func_ids: HashMap<String, FuncId> = HashMap::new();
    let mut func_types: HashMap<String, (Vec<HType>, HType)> = HashMap::new();
    let mut func_sigs: HashMap<String, Signature> = HashMap::new();

    if has_functions {
        for stmt in &program.stmts {
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
                let linkage = if name == "main" {
                    Linkage::Export
                } else {
                    Linkage::Local
                };
                let func_id = module.declare_function(name, linkage, &sig)?;
                func_ids.insert(name.clone(), func_id);
                func_sigs.insert(name.clone(), sig);
            }
        }

        for stmt in &program.stmts {
            if let HSharpStmt::FunctionDef(name, params, ret, body) = stmt {
                let mut codegen_ctx = cranelift::codegen::Context::new();
                let sig = func_sigs.get(name).unwrap().clone();
                codegen_ctx.func.signature = sig;
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
                    let repr_size = if pty.is_value_type() {
                        pty.size(type_map)
                    } else {
                        8
                    };
                    let align = if pty.is_value_type() {
                        pty.alignment(type_map)
                    } else {
                        8
                    };
                    let align_shift = align.ilog2() as u8;
                    let slot_data = StackSlotData::new(StackSlotKind::ExplicitSlot, repr_size, align_shift);
                    let slot = builder.create_sized_stack_slot(slot_data);
                    let addr = builder.ins().stack_addr(types::I64, slot, 0);
                    builder.ins().store(MemFlags::trusted(), param_repr, addr, 0);
                    vars.last_mut().unwrap().insert(pname.clone(), addr);
                    type_env
                    .last_mut()
                    .unwrap()
                    .insert(pname.clone(), pty.clone());
                }

                let capacity = builder.ins().iconst(types::I64, 1_048_576);
                let new_call = module.declare_func_in_func(arena_new_id, builder.func);
                let call_inst = builder.ins().call(new_call, &[capacity]);
                let arena = builder.inst_results(call_inst)[0];

                let mut state = CompilerState {
                    malloc_id,
                    free_id,
                    write_int_id,
                    write_str_id,
                    write_float_id,
                    arena_new_id,
                    arena_alloc_id,
                    arena_free_id,
                    memcpy_id,
                    vars: &mut vars,
                    type_env: &mut type_env,
                    string_constants: &mut string_constants,
                    func_ids: &func_ids,
                    func_types: &func_types,
                    type_map,
                    arena,
                    in_direct: false,
                };

                let val = compile_expr(&mut builder, &mut module, &mut state, body)?;
                let free_call = module.declare_func_in_func(arena_free_id, builder.func);
                builder.ins().call(free_call, &[arena]);
                if ret.param_type() != types::INVALID {
                    builder.ins().return_(&[val]);
                } else {
                    builder.ins().return_(&[]);
                }
                builder.finalize();
                module.define_function(func_ids[name], &mut codegen_ctx)?;
            }
        }
    } else {
        // Compile main script style
        let mut codegen_ctx = cranelift::codegen::Context::new();
        let mut sig = Signature::new(CallConv::SystemV);
        sig.returns.push(AbiParam::new(types::I32));
        codegen_ctx.func.signature = sig.clone();

        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut codegen_ctx.func, &mut builder_ctx);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let mut vars: Vec<HashMap<String, Value>> = vec![HashMap::new()];
        let mut type_env: Vec<HashMap<String, HType>> = vec![HashMap::new()];
        let capacity = builder.ins().iconst(types::I64, 1_048_576);
        let new_call = module.declare_func_in_func(arena_new_id, builder.func);
        let call_inst = builder.ins().call(new_call, &[capacity]);
        let arena = builder.inst_results(call_inst)[0];

        let mut state = CompilerState {
            malloc_id,
            free_id,
            write_int_id,
            write_str_id,
            write_float_id,
            arena_new_id,
            arena_alloc_id,
            arena_free_id,
            memcpy_id,
            vars: &mut vars,
            type_env: &mut type_env,
            string_constants: &mut string_constants,
            func_ids: &func_ids,
            func_types: &func_types,
            type_map,
            arena,
            in_direct: false,
        };

        for stmt in &program.stmts {
            compile_stmt(&mut builder, &mut module, &mut state, stmt)?;
        }
        let free_call = module.declare_func_in_func(arena_free_id, builder.func);
        builder.ins().call(free_call, &[arena]);
        let zero = builder.ins().iconst(types::I32, 0);
        builder.ins().return_(&[zero]);
        builder.finalize();

        let main_id = module.declare_function("main", Linkage::Export, &sig)?;
        module.define_function(main_id, &mut codegen_ctx)?;
    }

    let product = module.finish();
    let bytes = product.emit()?;
    fs::write(output_path, bytes).context("Failed to write object file")?;
    Ok(())
}
