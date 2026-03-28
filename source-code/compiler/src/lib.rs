pub mod codegen;
pub mod typeck;

pub use codegen::{Codegen, CodegenError};
pub use typeck::{TypeChecker, TypeError};

use hsharp_parser::ast::Module;
use thiserror::Error;
use std::path::Path;

#[derive(Error, Debug)]
pub enum CompileError {
    #[error("Błąd parsowania:\n{0}")]
    Parse(String),

    #[error("Błąd typów:\n{errors}")]
    Type { errors: String },

    #[error("Błąd generowania kodu: {0}")]
    Codegen(#[from] CodegenError),

    #[error("Błąd IO: {0}")]
    Io(#[from] std::io::Error),

    #[error("Błąd linkowania: {0}")]
    Link(String),
}

/// Opcje kompilacji
#[derive(Debug, Clone)]
pub struct CompileOptions {
    /// Cel: natywny (x86_64-linux itp.) lub dany triple
    pub target: Option<String>,
    /// Optymalizacje
    pub optimize: bool,
    /// Debug info
    pub debug: bool,
    /// Statyczne linkowanie (domyślnie true)
    pub static_link: bool,
    /// Wyjściowy plik
    pub output: Option<String>,
}

impl Default for CompileOptions {
    fn default() -> Self {
        Self {
            target: None,
            optimize: false,
            debug: false,
            static_link: true,
            output: None,
        }
    }
}

/// Pełny pipeline: source -> type check -> codegen -> obiekt -> binarka
pub fn compile_source(
    source: &str,
    file_name: &str,
    opts: &CompileOptions,
) -> Result<Vec<u8>, CompileError> {
    // 1. Parsowanie
    let module = hsharp_parser::parse(source, file_name)
    .map_err(CompileError::Parse)?;

    // 2. Type checking
    let mut tc = TypeChecker::new();
    if !tc.check_module(&module) {
        let errs = tc.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n");
        return Err(CompileError::Type { errors: errs });
    }

    // 3. Codegen
    let triple = if let Some(t) = &opts.target {
        t.parse::<target_lexicon::Triple>()
        .unwrap_or_else(|_| target_lexicon::Triple::host())
    } else {
        target_lexicon::Triple::host()
    };

    let mut cg = Codegen::new(triple)?;
    let obj_bytes = cg.compile_module(&module)?;

    Ok(obj_bytes)
}

/// Kompiluje plik H# do pliku obiektowego (.o)
pub fn compile_file(
    source_path: &Path,
    opts: &CompileOptions,
) -> Result<(), CompileError> {
    let source = std::fs::read_to_string(source_path)?;
    let file_name = source_path.file_stem()
    .and_then(|s| s.to_str())
    .unwrap_or("module");

    let obj_bytes = compile_source(&source, file_name, opts)?;

    let output = opts.output.as_deref().unwrap_or("a.o");
    std::fs::write(output, &obj_bytes)?;

    Ok(())
}

/// Interpretuje moduł H# - nie generuje binarki, wykonuje bezpośrednio
/// (uproszczony interpreter - tylko dla skryptów .hl)
pub mod interpreter;
