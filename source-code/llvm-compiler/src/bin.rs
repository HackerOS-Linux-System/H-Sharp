use colored::*;
use hsharp_compiler::CompileOptions;
use hsharp_llvm_compiler::compile_llvm;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        print_usage();
        std::process::exit(1);
    }

    let mut input   = String::new();
    let mut output  = String::new();
    let mut optimize = false;
    let mut emit_ir  = false;
    let mut debug    = false;
    let mut static_  = false;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--release" | "-O"    => { optimize = true; }
            "--debug"   | "-g"    => { debug = true; }
            "--static"            => { static_ = true; }
            "--emit-ir"           => { emit_ir = true; }
            "-o"                  => { i += 1; output = args.get(i).cloned().unwrap_or_default(); }
            "--version" | "-V"    => { println!("h#-compiler 0.1.0 (LLVM 17)"); return; }
            "--help" | "-h"       => { print_usage(); return; }
            arg if !arg.starts_with('-') => { input = arg.to_string(); }
            _ => {}
        }
        i += 1;
    }

    if input.is_empty() {
        eprintln!("{} no input file", "error:".red().bold());
        std::process::exit(1);
    }

    if output.is_empty() {
        output = input.trim_end_matches(".h#")
            .trim_end_matches(".hsp")
            .to_string();
    }

    // Parse
    let source = match std::fs::read_to_string(&input) {
        Ok(s) => s,
        Err(e) => { eprintln!("{} cannot read {}: {}", "error:".red().bold(), input, e); std::process::exit(1); }
    };

    let parse_result = hsharp_parser::parse(&source, &input);
    if parse_result.has_errors() {
        eprintln!("{} {}", "parse error:".red().bold(), parse_result.render_errors());
        std::process::exit(1);
    }
    let module = parse_result.module;

    let opts = CompileOptions {
        target: hsharp_compiler::TargetTriple::host(),
        optimize,
        static_link: static_,
        debug_info: debug,
        output: output.clone(),
        use_cranelift: false,
    };

    if emit_ir {
        match hsharp_llvm_compiler::emit_ir(&module, &opts) {
            Ok(ir) => { println!("{}", ir); }
            Err(e) => { eprintln!("{} {}", "error:".red().bold(), e); std::process::exit(1); }
        }
        return;
    }

    let mode = if optimize { "release (LLVM O3 + AVX2)" } else { "debug (LLVM O1)" };
    eprintln!("  {} {} → {}", "h#-compiler".cyan().bold(), input.dimmed(), output.cyan());
    eprintln!("  {} {}", "mode:".dimmed(), mode);

    match compile_llvm(&module, &opts) {
        Ok(())  => eprintln!("  {} binary: {}", "✓".green().bold(), output.cyan()),
        Err(e)  => { eprintln!("{} {}", "error:".red().bold(), e); std::process::exit(1); }
    }
}

fn print_usage() {
    println!("h#-compiler — H# LLVM native compiler v0.1.0");
    println!();
    println!("USAGE: h#-compiler <file.h#> [options]");
    println!();
    println!("OPTIONS:");
    println!("  -o <output>   Output file name");
    println!("  --release     Optimized build (O3 + AVX2)");
    println!("  --debug       Include debug info");
    println!("  --static      Static linking");
    println!("  --emit-ir     Print LLVM IR and exit");
    println!("  --version     Print version");
    println!();
    println!("NOTES:");
    println!("  Installed at: ~/.hackeros/H#/bins/h#-compiler");
    println!("  Called automatically by vira for release builds.");
    println!("  For quick preview:  h# preview file.h#  (Cranelift)");
}
