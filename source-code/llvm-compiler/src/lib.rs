/// H# LLVM/inkwell native code generator
/// Installed at: ~/.hackeros/H#/bins/h#-compiler
/// Called by vira for release builds.

pub mod codegen;
pub mod types;
pub mod builtins;
pub mod optimize;

use hsharp_parser::ast::Module;
use hsharp_compiler::CompileOptions;

pub use codegen::LlvmCodegen;
pub use codegen::CodegenError;

/// Compile H# module to native binary via LLVM
pub fn compile_llvm(module: &Module, opts: &CompileOptions) -> Result<(), CodegenError> {
    let mut cg = LlvmCodegen::new(opts)?;
    cg.declare_functions(module)?;
    cg.compile_module(module)?;
    cg.emit(&opts.output, opts.optimize)
}

/// Compile to LLVM IR text (for inspection / --emit-ir)
pub fn emit_ir(module: &Module, opts: &CompileOptions) -> Result<String, CodegenError> {
    let mut cg = LlvmCodegen::new(opts)?;
    cg.declare_functions(module)?;
    cg.compile_module(module)?;
    Ok(cg.get_ir())
}

/// Compile to object file only (for --emit-obj)
pub fn emit_object(module: &Module, opts: &CompileOptions, out: &str) -> Result<(), CodegenError> {
    let mut cg = LlvmCodegen::new(opts)?;
    cg.declare_functions(module)?;
    cg.compile_module(module)?;
    cg.emit_object_file(out)
}
