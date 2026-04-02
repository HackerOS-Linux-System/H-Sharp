pub mod codegen;
pub mod typechecker;
pub mod target;

use hsharp_parser::ast::Module;
use std::path::Path;

pub use codegen::CodegenError;
pub use typechecker::TypeError;
pub use target::TargetTriple;

#[derive(Debug, Clone)]
pub struct CompileOptions {
    pub target: TargetTriple,
    pub optimize: bool,
    pub static_link: bool,
    pub debug_info: bool,
    pub output: String,
}

impl Default for CompileOptions {
    fn default() -> Self {
        Self {
            target: TargetTriple::host(),
            optimize: true,
            static_link: true,
            debug_info: false,
            output: "output".to_string(),
        }
    }
}

#[derive(Debug)]
pub enum CompileError {
    Type(TypeError),
    Codegen(CodegenError),
    Io(std::io::Error),
    Linker(String),
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::Type(e) => write!(f, "type error: {}", e),
            CompileError::Codegen(e) => write!(f, "codegen error: {}", e),
            CompileError::Io(e) => write!(f, "io error: {}", e),
            CompileError::Linker(s) => write!(f, "linker error: {}", s),
        }
    }
}

pub fn compile(module: &Module, opts: &CompileOptions) -> Result<(), CompileError> {
    // 1. Type check
    let mut tc = typechecker::TypeChecker::new();
    tc.check_module(module).map_err(CompileError::Type)?;

    // 2. Code generation
    let mut cg = codegen::Codegen::new(&module.file, opts);
    cg.compile_module(module).map_err(CompileError::Codegen)?;

    // 3. Emit object file
    cg.emit_object(&opts.output).map_err(CompileError::Codegen)?;

    Ok(())
}
