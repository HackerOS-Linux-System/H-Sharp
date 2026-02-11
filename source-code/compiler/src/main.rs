use anyhow::{Context, Result};
use cranelift::prelude::*;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use serde::{Deserialize, Serialize};
use std::fs::{self, File};
use std::io::{self, BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use target_lexicon::Triple;

// Simple AST representation for H# language.
// Since the language spec is partial, we'll define a toy AST with basic features:
// - Variables with manual memory management (alloc/dealloc).
// - Arena allocator simulation via custom functions.
// - Unsafe-like blocks for manual ops.
// For demo, H# code like:
// unsafe {
//   let ptr = alloc(4); // allocate 4 bytes
//   *ptr = 42;
//   print(*ptr);
//   dealloc(ptr);
// }

#[derive(Debug, Deserialize, Serialize, Clone)]
enum HSharpExpr {
    Literal(i32),
    Var(String),
    Alloc(Box<HSharpExpr>), // alloc(size)
    Dealloc(Box<HSharpExpr>), // dealloc(ptr)
    Deref(Box<HSharpExpr>), // *ptr
    Assign(Box<HSharpExpr>, Box<HSharpExpr>), // ptr = expr
    Print(Box<HSharpExpr>),
    Block(Vec<HSharpStmt>),
    Unsafe(Box<HSharpExpr>),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
enum HSharpStmt {
    Let(String, HSharpExpr),
    Expr(HSharpExpr),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
struct HSharpProgram {
    stmts: Vec<HSharpStmt>,
}

fn main() -> Result<()> {
    // Assume parser/lexer outputs JSON to a temp file, path provided as arg.
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: h-sharp-compiler <input_json> <output_obj>");
        std::process::exit(1);
    }
    let input_json = &args[1];
    let output_obj = &args[2];

    // Read JSON from parser.
    let json_data = fs::read_to_string(input_json).context("Failed to read input JSON")?;
    let program: HSharpProgram = serde_json::from_str(&json_data).context("Failed to parse JSON")?;

    // Compile to object file using Cranelift.
    compile_program(&program, output_obj)?;

    Ok(())
}

fn compile_program(program: &HSharpProgram, output_path: &str) -> Result<()> {
    // Setup Cranelift.
    let isa_builder = cranelift_native::builder().context("Failed to build ISA")?;
    let isa = isa_builder.finish(settings::Flags::new(settings::builder())).context("Failed to finalize ISA")?;

    let builder = ObjectBuilder::new(isa, "hsharp_module", cranelift_module::default_libcall_names())?;
    let mut module = ObjectModule::new(builder);

    // Declare external functions for alloc/dealloc/print (runtime provided).
    let alloc_id = module.declare_function("hsharp_alloc", Linkage::Import, &signature_for_alloc(&module))?;
    let dealloc_id = module.declare_function("hsharp_dealloc", Linkage::Import, &signature_for_dealloc(&module))?;
    let print_id = module.declare_function("hsharp_print", Linkage::Import, &signature_for_print(&module))?;

    // Define main function.
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

    // Compile statements.
    for stmt in &program.stmts {
        compile_stmt(stmt, &mut builder, &mut module, alloc_id, dealloc_id, print_id)?;
    }

    // Return 0.
    let zero = builder.ins().iconst(types::I32, 0);
    builder.ins().return_(&[zero]);

    builder.finalize();

    // Verify and define.
    module.define_function(module.declare_function("main", Linkage::Export, &sig)?, &mut ctx)?;

    // Finalize module and write object file.
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
    sig.params.push(AbiParam::new(types::I64)); // size
    sig.returns.push(AbiParam::new(types::I64)); // ptr (i64 for simplicity)
    sig
}

fn signature_for_dealloc(module: &ObjectModule) -> Signature {
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64)); // ptr
    sig
}

fn signature_for_print(module: &ObjectModule) -> Signature {
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I32)); // value
    sig
}

// Toy variable environment: use a simple hashmap for var names to Value.
use std::collections::HashMap;

fn compile_stmt(
    stmt: &HSharpStmt,
    builder: &mut FunctionBuilder,
    module: &mut ObjectModule,
    alloc_id: FuncId,
    dealloc_id: FuncId,
    print_id: FuncId,
) -> Result<()> {
    let mut vars: HashMap<String, Value> = HashMap::new();
    match stmt {
        HSharpStmt::Let(name, expr) => {
            let val = compile_expr(expr, builder, module, alloc_id, dealloc_id, print_id, &mut vars)?;
            vars.insert(name.clone(), val);
        }
        HSharpStmt::Expr(expr) => {
            compile_expr(expr, builder, module, alloc_id, dealloc_id, print_id, &mut vars)?;
        }
    }
    Ok(())
}

fn compile_expr(
    expr: &HSharpExpr,
    builder: &mut FunctionBuilder,
    module: &mut ObjectModule,
    alloc_id: FuncId,
    dealloc_id: FuncId,
    print_id: FuncId,
    vars: &mut HashMap<String, Value>,
) -> Value {
    match expr {
        HSharpExpr::Literal(n) => builder.ins().iconst(types::I32, *n as i64),
        HSharpExpr::Var(name) => *vars.get(name).unwrap_or_else(|| panic!("Undefined var: {}", name)),
        HSharpExpr::Alloc(size_expr) => {
            let size = compile_expr(size_expr, builder, module, alloc_id, dealloc_id, print_id, vars);
            let alloc_call = module.declare_func_in_func(alloc_id, builder.func);
            builder.ins().call(alloc_call, &[size])
        }
        HSharpExpr::Dealloc(ptr_expr) => {
            let ptr = compile_expr(ptr_expr, builder, module, alloc_id, dealloc_id, print_id, vars);
            let dealloc_call = module.declare_func_in_func(dealloc_id, builder.func);
            builder.ins().call(dealloc_call, &[ptr]);
            builder.ins().iconst(types::I32, 0) // return dummy
        }
        HSharpExpr::Deref(ptr_expr) => {
            let ptr = compile_expr(ptr_expr, builder, module, alloc_id, dealloc_id, print_id, vars);
            // Simulate deref: load from memory. Assume ptr is i64 address.
            builder.ins().load(types::I32, MemFlags::new(), ptr, 0)
        }
        HSharpExpr::Assign(lhs, rhs) => {
            if let HSharpExpr::Deref(ptr_expr) = **lhs {
                let ptr = compile_expr(&ptr_expr, builder, module, alloc_id, dealloc_id, print_id, vars);
                let val = compile_expr(rhs, builder, module, alloc_id, dealloc_id, print_id, vars);
                builder.ins().store(MemFlags::new(), val, ptr, 0);
                val
            } else {
                panic!("Assign LHS must be deref");
            }
        }
        HSharpExpr::Print(expr) => {
            let val = compile_expr(expr, builder, module, alloc_id, dealloc_id, print_id, vars);
            let print_call = module.declare_func_in_func(print_id, builder.func);
            builder.ins().call(print_call, &[val]);
            builder.ins().iconst(types::I32, 0) // dummy
        }
        HSharpExpr::Block(stmts) => {
            let mut last = builder.ins().iconst(types::I32, 0);
            for stmt in stmts {
                compile_stmt(stmt, builder, module, alloc_id, dealloc_id, print_id)?;
            }
            last
        }
        HSharpExpr::Unsafe(inner) => {
            // Unsafe just compiles inner, assuming manual management inside.
            compile_expr(inner, builder, module, alloc_id, dealloc_id, print_id, vars)
        }
    }
}

// Note: This is a highly simplified toy compiler.
// In a real implementation, you'd need:
// - Proper memory management simulation (arena via custom allocator).
// - Full AST for the language.
// - Error handling.
// - Optimization passes.
// - Linker integration for runtime (alloc/dealloc/print impl).
// - Communication via JSON for parser output.
// - Cranelift for JIT or AOT.
// Also, arena allocator would be a runtime feature, perhaps with custom types.
// For manual management, add more ops like raw pointers, casts.
// This skeleton assumes the parser produces the JSON AST as defined.
