use colored::Colorize;
use indicatif::MultiProgress;
use std::path::PathBuf;
use std::time::Instant;

use hsharp_compiler::{
    compile, CompileOptions, TargetTriple,
    ffi_linker,
};

#[allow(clippy::too_many_arguments)]
pub fn run(
    file:     PathBuf,
    output:   Option<String>,
    target:   Option<String>,
    release:  bool,
    no_opt:   bool,
    debug:    bool,
    dynamic:  bool,
    emit_ir:  bool,
    verbose:  bool,
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

    // ── Flags ───────────────────────────────────────────────────────────────
    let optimize  = release && !no_opt;
    let static_link = !dynamic;

    let opts = CompileOptions {
        target:      triple.clone(),
        optimize,
        static_link,
        debug_info:  debug,
        output:      out_path.clone(),
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

    // ── --emit-ir: dump IR and exit ─────────────────────────────────────────
    if emit_ir {
        let pb_ir = crate::make_spinner("Building LLVM IR…");
        let cg = hsharp_compiler::codegen::LlvmCodegen::new(&opts)
        .unwrap_or_else(|e| { eprintln!("{} {}", "Error:".red().bold(), e); std::process::exit(1); });
        match cg.compile_to_ir(&parsed.module) {
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
    match compile(&parsed.module, &source, &opts) {
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
    let bin = format!("{}{}", out_path, triple.exe_suffix());
    let elapsed = t0.elapsed();

    // Show extern link flags if any
    let link_flags = ffi_linker::collect_link_flags(&parsed.module);
    let link_desc  = ffi_linker::describe_flags(&link_flags);

    println!();
    println!("{}", "─".repeat(54).dimmed());
    println!("  {} {}", "Binary:  ".bold(), bin.cyan());
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
