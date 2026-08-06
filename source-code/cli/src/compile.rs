use colored::Colorize;
use indicatif::MultiProgress;
use std::path::PathBuf;
use std::time::Instant;

use hsharp_compiler::{
    compile, CompileOptions, OutputKind, TargetTriple,
    ffi_linker,
};

#[allow(clippy::too_many_arguments)]
pub fn run(
    file:      PathBuf,
    output:    Option<String>,
    target:    Option<String>,
    release:   bool,
    no_opt:    bool,
    debug:     bool,
    dynamic:   bool,
    emit_ir:   bool,
    emit_kind: Option<String>,
    verbose:   bool,
    mem_mode:  Option<String>,
) {
    let t0 = Instant::now();

    // ── Resolve paths ───────────────────────────────────────────────────────
    let src_path = &file;
    let stem = src_path.file_stem()
    .and_then(|s| s.to_str())
    .unwrap_or("output");

    std::fs::create_dir_all("build").ok();
    let out_path = output.unwrap_or_else(|| format!("build/{}", stem));

    // ── Target ──────────────────────────────────────────────────────────────
    let triple = if let Some(t) = target {
        match TargetTriple::from_str(&t) {
            Some(tt) => tt,
            None => {
                eprintln!("{} unknown target `{}`. Run `h# targets` to list them.", "Error:".red().bold(), t);
                std::process::exit(1);
            }
        }
    } else {
        TargetTriple::host()
    };

    // ── Output kind (--emit flag) ────────────────────────────────────────────
    let output_kind = if let Some(ref kind_str) = emit_kind {
        match OutputKind::from_str(kind_str) {
            Some(k) => k,
            None => {
                eprintln!(
                    "{} unknown --emit kind `{}`. Valid: bin, obj, so, lib",
                    "Error:".red().bold(), kind_str
                );
                std::process::exit(1);
            }
        }
    } else {
        OutputKind::Binary
    };

    // ── Flags ───────────────────────────────────────────────────────────────
    let optimize    = release && !no_opt;
    let static_link = !dynamic;

    // ── --mem-mode (project-wide MemoryMode fallback) ────────────────────────
    // See `CompileOptions::default_mem_mode`'s doc comment: this is the
    // weakest of the three ways a function ends up with a `MemoryMode` —
    // its own `@mode` annotation wins, then its file's `@: mode`
    // directive, then finally this flag. Mainly meant to be set by the
    // `bytes` package manager reading a `mem_mode` key out of `bytes.hk`,
    // not typed by hand very often.
    let default_mem_mode = match mem_mode.as_deref() {
        None => None,
        Some("default")  => Some(hsharp_parser::ast::MemoryMode::Default),
        Some("safety")   => Some(hsharp_parser::ast::MemoryMode::Safety),
        Some("arc")      => Some(hsharp_parser::ast::MemoryMode::Arc),
        Some("arena")    => Some(hsharp_parser::ast::MemoryMode::Arena),
        Some("pointers") => Some(hsharp_parser::ast::MemoryMode::Pointers),
        Some(other) => {
            eprintln!(
                "{} unknown --mem-mode `{}`. Valid: default, safety, arc, arena, pointers",
                "Error:".red().bold(), other
            );
            std::process::exit(1);
        }
    };

    let opts = CompileOptions {
        target:      triple.clone(),
        optimize,
        static_link,
        debug_info:  debug,
        output:      out_path.clone(),
        output_kind: output_kind.clone(),
        default_mem_mode,
    };

    if verbose {
        println!(
            "  {} {} → {}{}  [{}]",
            "Compiling:".green().bold(),
                 src_path.display(),
                 out_path,
                 triple.exe_suffix(),
                 if optimize { "LLVM O3 + native + LTO" } else { "LLVM O0 (debug)" },
        );
        println!();
    }

    // ── Read source ─────────────────────────────────────────────────────────
    let mp = MultiProgress::new();
    let pb1 = crate::make_spinner("Reading source…");
    let source = match std::fs::read_to_string(src_path) {
        Ok(s) => { pb1.finish_and_clear(); s }
        Err(e) => {
            pb1.finish_and_clear();
            eprintln!("{} cannot read `{}`: {}", "Error:".red().bold(), src_path.display(), e);
            std::process::exit(1);
        }
    };

    // ── Parse ───────────────────────────────────────────────────────────────
    let pb2 = crate::make_spinner(&format!("Parsing {}…", src_path.display()));
    let parsed = hsharp_parser::parse(&source, &src_path.display().to_string());
    if parsed.has_errors() {
        pb2.finish_and_clear();
        eprintln!("{}", parsed.render_errors());
        eprintln!("{} parsing failed.", "✗".red().bold());
        std::process::exit(1);
    }
    pb2.finish_with_message(format!("{} Parsed", "✓".green()));

    // ── Resolve `mod X` declarations ─────────────────────────────────────────
    // `mod cli` (etc.) previously did nothing: ModuleResolver::expand_module
    // existed in modules.rs but was never called anywhere in the pipeline, so
    // every item declared in a submodule file was silently absent from the
    // compiled program — any function in it would fail later as
    // "undefined fn: ..." with no indication the real problem was an
    // unresolved `mod` declaration. Expand submodules into the top-level
    // module's item list right after parsing, before anything downstream
    // (typecheck/codegen) ever sees it.
    let mut module = parsed.module.clone();
    {
        let mut resolver = hsharp_compiler::modules::ModuleResolver::new(src_path);
        let entry_dir = src_path.parent().unwrap_or_else(|| std::path::Path::new("."));
        match resolver.expand_module(module.items, entry_dir) {
            Ok(items) => module.items = items,
            Err(e) => {
                pb2.finish_and_clear();
                eprintln!("{} {}", "Error:".red().bold(), e);
                std::process::exit(1);
            }
        }
    }

    // ── --emit-ir: dump IR and exit ─────────────────────────────────────────
    if emit_ir {
        let pb_ir = crate::make_spinner("Building LLVM IR…");
        let cg = hsharp_compiler::codegen::LlvmCodegen::new(&opts)
        .unwrap_or_else(|e| { eprintln!("{} {}", "Error:".red().bold(), e); std::process::exit(1); });
        match cg.compile_to_ir(&module) {
            Ok(ir) => {
                pb_ir.finish_with_message(format!("{} IR generated", "✓".green()));
                println!("{}", ir);
            }
            Err(e) => {
                pb_ir.finish_and_clear();
                eprintln!("{} {}", "Error:".red().bold(), e);
                std::process::exit(1);
            }
        }
        return;
    }

    // ── Full compile pipeline ───────────────────────────────────────────────
    // The `compile()` function in lib.rs runs:
    //   derive/traits → typecheck → features → monomorphize →
    //   optimize_ast → LLVM codegen → link
    // It prints diagnostics (TYPE ERROR boxes) via print_diagnostics before
    // returning Err(Diagnostics(_)).
    let pb3 = crate::make_spinner("Compiling (LLVM)…");
    match compile(&module, &source, &opts) {
        Ok(()) => {
            pb3.finish_with_message(format!("{} Compiled", "✓".green()));
        }
        Err(hsharp_compiler::CompileError::Diagnostics(_)) => {
            // Diagnostics were already printed by compile() via print_diagnostics
            pb3.finish_and_clear();
            eprintln!("{} Compilation failed (type errors above).", "✗".red().bold());
            std::process::exit(1);
        }
        Err(e) => {
            pb3.finish_and_clear();
            eprintln!("{} {}", "✗ Error:".red().bold(), e);
            std::process::exit(1);
        }
    }

    // ── Summary ─────────────────────────────────────────────────────────────
    let artifact_suffix = match output_kind {
        OutputKind::Binary    => triple.exe_suffix().to_string(),
        OutputKind::Object    => ".o".to_string(),
        OutputKind::SharedLib => output_kind.file_suffix(&triple).to_string(),
        OutputKind::StaticLib => ".a".to_string(),
    };
    let bin = format!("{}{}", out_path, artifact_suffix);
    let elapsed = t0.elapsed();

    // Show extern link flags if any
    let link_flags = ffi_linker::collect_link_flags(&parsed.module);
    let link_desc  = ffi_linker::describe_flags(&link_flags);

    println!();
    println!("{}", "─".repeat(54).dimmed());
    let artifact_label = match output_kind {
        OutputKind::Binary    => "Binary:  ",
        OutputKind::Object    => "Object:  ",
        OutputKind::SharedLib => "SharedLib:",
        OutputKind::StaticLib => "StaticLib:",
    };
    println!("  {} {}", artifact_label.bold(), bin.cyan());
    println!("  {} {}", "Target:  ".bold(), triple.llvm_triple);
    println!("  {} {}", "Backend: ".bold(), "LLVM (h# v0.8)".green());
    println!("  {} {}", "Mode:    ".bold(), if optimize { "release (O3 + LTO)".yellow().to_string() } else { "debug (O0)".dimmed().to_string() });
    if !link_desc.is_empty() {
        println!("  {} {}", "Linked:  ".bold(), link_desc.yellow());
    }
    println!("  {} {:.2?}", "Time:    ".bold(), elapsed);
    println!("{}", "─".repeat(54).dimmed());
    println!("\n  {} Build complete!", "✓".green().bold());

    let _ = mp;
}
