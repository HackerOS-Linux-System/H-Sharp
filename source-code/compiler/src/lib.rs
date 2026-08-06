pub mod derive_codegen;
pub mod lifetimes;
pub mod modules;
pub mod traits;
pub mod regions;
pub mod ffi;
pub mod ffi_cpp;
pub mod ffi_rust_native;
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

/// The kind of artifact the compiler should produce.
///
/// Default: `Binary` (a native executable).
/// Override via `h# compile --emit <kind>`.
#[derive(Debug, Clone, PartialEq, Default)]
pub enum OutputKind {
    /// Native executable (default). No special flags needed.
    #[default]
    Binary,
    /// Relocatable object file (.o) — no linker step, raw LLVM object.
    Object,
    /// Shared / dynamic library (.so on Linux, .dylib on macOS, .dll on Windows).
    SharedLib,
    /// Static archive (.a). The compiled .o is archived with `ar`.
    StaticLib,
}

impl OutputKind {
    /// Extension to append to the output name (overrides target exe_suffix for non-binary).
    pub fn file_suffix(&self, target: &TargetTriple) -> &'static str {
        match self {
            OutputKind::Binary    => "",           // exe_suffix() applied separately
            OutputKind::Object    => ".o",
            OutputKind::SharedLib => {
                if target.llvm_triple.contains("windows") { ".dll" }
                else if target.llvm_triple.contains("darwin") { ".dylib" }
                else { ".so" }
            }
            OutputKind::StaticLib => ".a",
        }
    }

    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "bin" | "binary" | "exe"     => Some(OutputKind::Binary),
            "obj" | "object" | "o"       => Some(OutputKind::Object),
            "so"  | "dylib" | "dll"
            | "shared" | "shared-lib"    => Some(OutputKind::SharedLib),
            "a"   | "lib" | "static"
            | "static-lib" | "archive"   => Some(OutputKind::StaticLib),
            _                            => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct CompileOptions {
    pub target:      TargetTriple,
    pub optimize:    bool,
    pub static_link: bool,
    pub debug_info:  bool,
    pub output:      String,
    /// What kind of artifact to produce (default: Binary).
    pub output_kind: OutputKind,
    /// `--mem-mode <default|safety|arc|arena|pointers>` — a project-wide
    /// fallback `MemoryMode`, applied (in `compile()` below, alongside
    /// the per-file `@: mode` directive — see ast.rs's
    /// `apply_file_mem_mode`) to every function that ends up with no
    /// `@mode` from either its own annotation or its file's `@:` line.
    /// This is what lets `bytes.hk`'s `mem_mode` setting (see the `bytes`
    /// package manager) apply to a whole project without editing a `@:`
    /// line into every single source file by hand — `bytes` just passes
    /// this flag through when it shells out to `hsharp build`/`compile`.
    /// A function's own `@mode` still wins over this, and so does its
    /// file's `@:` directive if it has one — this is only the last,
    /// weakest fallback.
    pub default_mem_mode: Option<hsharp_parser::ast::MemoryMode>,
}

impl Default for CompileOptions {
    fn default() -> Self {
        Self {
            target:      TargetTriple::host(),
            optimize:    true,
            static_link: true,
            debug_info:  false,
            output:      "output".to_string(),
            output_kind: OutputKind::Binary,
            default_mem_mode: None,
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
        file:          module.file.clone(),
        edition:       module.edition.clone(),
        file_mem_mode: module.file_mem_mode,
        imports:       module.imports.clone(),
        items,
    };
    // `@: mode` file-level directive (see ast.rs's `apply_file_mem_mode`
    // doc comment): rewrites every function in `module` still at
    // `MemoryMode::Default` to the file's declared default. Doing this
    // once, right here, means the typechecker's mem-mode gate and every
    // codegen pass below see a plain, already-resolved per-function
    // `MemoryMode` exactly like before — neither of them needs to know
    // the file-level directive exists at all.
    hsharp_parser::ast::apply_file_mem_mode(&mut module);
    // `--mem-mode` CLI flag (see CompileOptions::default_mem_mode): the
    // weakest of the three sources of a function's MemoryMode, applied
    // last so a function's own `@mode` and its file's `@: mode` directive
    // both still win over it.
    if let Some(default_mode) = opts.default_mem_mode {
        for item in &mut module.items {
            hsharp_parser::ast::apply_file_mem_mode_item(item, default_mode);
        }
    }

    // ── Pass 1+2: typecheck + feature/capability check ─────────────────────
    let mut tc = typechecker::TypeChecker::new();
    let mut diags = tc.check_module(&module);
    diags.extend(features::check_module_features(&module, builtins_registry::Backend::Llvm));

    // ── Pass 2.5: lifetime consistency (basic v1) ───────────────────────────
    // `lifetimes.rs`'s `LifetimeChecker` was a complete, self-contained pass
    // that had never actually been called from anywhere in the pipeline —
    // it type-checked nothing because nothing invoked `check_module` on it.
    // Wired in here as advisory warnings, not hard errors: it only
    // understands `&`/`&mut` and explicit `'name` type params today (see
    // `extract_lifetime_from_type`), so a real gap in its own coverage
    // could otherwise turn into a false-positive compile failure on
    // legitimate code. `@safety`'s move check uses the same
    // warn-don't-block posture for the same reason.
    let mut lc = lifetimes::LifetimeChecker::new();
    for err in lc.check_module(&module) {
        eprintln!("warning: {}", err);
    }

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
