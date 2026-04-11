pub mod cranelift_codegen;
pub mod runtime;
pub mod target;
pub mod typechecker;
pub mod types;

// Keep old C codegen as fallback
pub mod codegen;

use hsharp_parser::ast::Module;

pub use target::TargetTriple;
pub use typechecker::TypeError;

#[derive(Debug, Clone)]
pub struct CompileOptions {
    pub target: TargetTriple,
    pub optimize: bool,
    pub static_link: bool,
    pub debug_info: bool,
    pub output: String,
    /// Use Cranelift native backend (true) or C transpilation fallback (false)
    pub use_cranelift: bool,
}

impl Default for CompileOptions {
    fn default() -> Self {
        Self {
            target: TargetTriple::host(),
            optimize: true,
            static_link: true,
            debug_info: false,
            output: "output".to_string(),
            use_cranelift: true,
        }
    }
}

#[derive(Debug)]
pub enum CompileError {
    Type(TypeError),
    Codegen(String),
    Cranelift(cranelift_codegen::CodegenError),
    Io(std::io::Error),
    Linker(String),
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::Type(e)      => write!(f, "type error: {}", e),
            CompileError::Codegen(s)   => write!(f, "codegen error: {}", s),
            CompileError::Cranelift(e) => write!(f, "cranelift error: {}", e),
            CompileError::Io(e)        => write!(f, "io error: {}", e),
            CompileError::Linker(s)    => write!(f, "linker error: {}", s),
        }
    }
}

pub fn compile(module: &Module, opts: &CompileOptions) -> Result<(), CompileError> {
    // Type check always
    let mut tc = typechecker::TypeChecker::new();
    tc.check_module(module).map_err(CompileError::Type)?;

    if opts.use_cranelift {
        compile_cranelift(module, opts)
    } else {
        compile_c_fallback(module, opts)
    }
}

fn compile_cranelift(module: &Module, opts: &CompileOptions) -> Result<(), CompileError> {
    let mut cg = cranelift_codegen::CraneliftCodegen::new(opts)
        .map_err(CompileError::Cranelift)?;

    cg.declare_functions(module).map_err(CompileError::Cranelift)?;
    cg.compile_module(module).map_err(CompileError::Cranelift)?;
    cranelift_codegen::emit_module(cg, &opts.output).map_err(CompileError::Cranelift)?;
    Ok(())
}

fn compile_c_fallback(module: &Module, opts: &CompileOptions) -> Result<(), CompileError> {
    let mut cg = codegen::Codegen::new(&module.file, opts);
    cg.compile_module(module)
        .map_err(|e| CompileError::Codegen(e.to_string()))?;
    cg.emit_object(&opts.output)
        .map_err(|e| CompileError::Codegen(e.to_string()))?;
    Ok(())
}
pub mod regions;
pub mod ffi;
