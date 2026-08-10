use colored::Colorize;
use std::path::PathBuf;
use walkdir::WalkDir;

pub fn run(file: Option<PathBuf>) {
    let src_path = file.unwrap_or_else(|| {
        let exts = ["h#", "hsp", "h-sharp"];
        WalkDir::new(".").max_depth(3).into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.file_type().is_file()
                && e.path().extension().and_then(|s| s.to_str()).map(|x| exts.contains(&x)).unwrap_or(false)
                && !e.path().starts_with("./build"))
            .map(|e| e.path().to_path_buf())
            .next()
            .unwrap_or_else(|| {
                eprintln!("{} no .h# files found", "Error:".red().bold());
                std::process::exit(1);
            })
    });

    let source = match std::fs::read_to_string(&src_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{} cannot read `{}`: {}", "Error:".red().bold(), src_path.display(), e);
            std::process::exit(1);
        }
    };

    println!("{} {} (interpreter mode)", "▶ Preview:".cyan().bold(), src_path.display());
    println!("{}", "─".repeat(50).dimmed());

    let result = hsharp_parser::parse(&source, &src_path.display().to_string());
    if result.has_errors() {
        eprintln!("{}", result.render_errors());
        std::process::exit(1);
    }

    let mut module = result.module;
    let mut resolver = hsharp_compiler::modules::ModuleResolver::new(&src_path);
    let entry_dir = src_path.parent().map(|p| p.to_path_buf()).unwrap_or_else(|| std::path::PathBuf::from("."));
    match resolver.expand_module(module.items, &entry_dir) {
        Ok(items) => module.items = items,
        Err(e) => {
            eprintln!("{} {}", "Error:".red().bold(), e);
            std::process::exit(1);
        }
    }
    // Same `@: mode` file-level directive the LLVM backend applies (see
    // hsharp_compiler::lib::compile / ast.rs's `apply_file_mem_mode`) —
    // without this, `hsharp run` and `hsharp build`/`compile` would
    // disagree about which `MemoryMode` a function without its own
    // `@mode` annotation ends up with whenever a file used the new
    // directive, exactly the kind of interpreter/LLVM divergence the
    // rest of `MemoryMode` handling here already tries to surface rather
    // than hide.
    hsharp_parser::ast::apply_file_mem_mode(&mut module);

    let mut interp = hsharp_interpreter::Interpreter::new();
    match interp.run_module(&module) {
        Ok(()) => {
            println!("{}", "─".repeat(50).dimmed());
            println!("{} Preview completed.", "✓".green().bold());
        }
        // `exit(code)` inside the H# program itself now comes back as a
        // dedicated `RuntimeError::Exit` instead of the interpreter
        // calling `std::process::exit` directly from deep inside
        // `call_fn` — see that variant's doc comment in
        // hsharp-interpreter's value.rs for why (short version: it's an
        // uncatchable WASM trap on wasm32-unknown-unknown, which the CLI
        // doesn't target, but the interpreter crate is shared with the
        // WASM playground, which does). Here at the top of the native
        // CLI's own call stack is exactly the right place to actually
        // exit the process — preserves the exact previous behavior for
        // `hsharp preview`/`run`.
        Err(hsharp_interpreter::RuntimeError::Exit(code)) => {
            std::process::exit(code);
        }
        Err(e) => {
            println!("{}", "─".repeat(50).dimmed());
            eprintln!("{} Runtime error: {}", "✗".red().bold(), e);
            std::process::exit(1);
        }
    }
}
