pub mod derive_codegen;
pub mod lifetimes;
pub mod modules;
pub mod traits;
pub mod regions;
pub mod ffi;
pub mod ffi_linker;
pub mod runtime;
pub mod target;
pub mod typechecker;
pub mod optimize_ast;
pub mod builtins_registry;
pub mod features;
pub mod monomorphize;

// LLVM codegen + its support modules (merged from the former
// `hsharp-llvm-compiler` crate).
pub mod codegen;
pub mod builtins;
pub mod llvm_types;
pub mod llvm_optimize;

use hsharp_parser::ast::Module;
pub use target::TargetTriple;
pub use typechecker::{Diagnostic, Severity, print_diagnostics};

#[derive(Debug, Clone)]
pub struct CompileOptions {
    pub target:      TargetTriple,
    pub optimize:    bool,
    pub static_link: bool,
    pub debug_info:  bool,
    pub output:      String,
}

impl Default for CompileOptions {
    fn default() -> Self {
        Self {
            target:      TargetTriple::host(),
            optimize:    true,
            static_link: true,
            debug_info:  false,
            output:      "output".to_string(),
        }
    }
}

#[derive(Debug)]
pub enum CompileError {
    /// Type-checking / feature-capability errors. Already printed by the
    /// time this is returned via `print_diagnostics`.
    Diagnostics(Vec<Diagnostic>),
    Codegen(codegen::CodegenError),
    Io(std::io::Error),
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::Diagnostics(d) => write!(f, "{} error(s)", d.iter().filter(|x| x.severity == Severity::Error).count()),
            CompileError::Codegen(e)     => write!(f, "codegen: {}", e),
            CompileError::Io(e)          => write!(f, "io: {}", e),
        }
    }
}

impl std::error::Error for CompileError {}
impl From<std::io::Error>          for CompileError { fn from(e: std::io::Error)          -> Self { CompileError::Io(e) } }
impl From<codegen::CodegenError>   for CompileError { fn from(e: codegen::CodegenError)   -> Self { CompileError::Codegen(e) } }

/// Compile an H# module to a native binary via LLVM.
///
/// `source` is the original source text (required for diagnostic spans).
///
/// Pipeline:
///   0. trait registration + #[derive] expansion
///   1. typecheck → Vec<Diagnostic>
///   2. feature/backend capability → Vec<Diagnostic>
///   3. monomorphize generics
///   4. AST-level optimisations (constant folding, string concat, DCE, #[inline])
///   5. LLVM codegen → object → link → binary
pub fn compile(module: &Module, source: &str, opts: &CompileOptions) -> Result<(), CompileError> {
    // ── Pass 0: trait registration + #[derive] expansion ──────────────────
    let mut trait_registry = traits::TraitRegistry::new();
    for item in &module.items {
        match item {
            hsharp_parser::ast::Item::TraitDef(t) => trait_registry.register_trait(t),
            hsharp_parser::ast::Item::ImplBlock(b) => trait_registry.register_impl(b),
            _ => {}
        }
    }
    let derive_items = derive_codegen::expand_derives(module);

    let mut items = module.items.clone();
    items.extend(derive_items);
    for fn_def in trait_registry.emit_fns() {
        items.push(hsharp_parser::ast::Item::FnDef(fn_def.clone()));
    }

    let mut module = hsharp_parser::ast::Module {
        file:       module.file.clone(),
        edition:    module.edition.clone(),
        directives: module.directives.clone(),
        imports:    module.imports.clone(),
        items,
    };

    // ── Pass 1+2: typecheck + feature/capability check ─────────────────────
    let mut tc = typechecker::TypeChecker::new();
    let mut diags = tc.check_module(&module);
    diags.extend(features::check_module_features(&module, builtins_registry::Backend::Llvm));

    if !diags.is_empty() {
        print_diagnostics(&diags, source, &module.file);
    }
    if diags.iter().any(|d| d.severity == Severity::Error) {
        return Err(CompileError::Diagnostics(diags));
    }

    // ── Pass 3: monomorphize generics ──────────────────────────────────────
    let _mono_stats = monomorphize::monomorphize(&mut module, &mut tc);

    // ── Pass 4: AST-level optimisations ────────────────────────────────────
    let (module, _opt_stats) = optimize_ast::OptimizeContext::new().run(module);

    // ── Pass 5: LLVM codegen → object → binary ─────────────────────────────
    let cg = codegen::LlvmCodegen::new(opts)?;
    cg.compile_full(&module)?;
    Ok(())
}
