use anyhow::{Context, Result};
use clap::Parser;
use indicatif::{ProgressBar, ProgressStyle};
use std::fs;
use std::io::Write;
use std::process::Command;
use std::time::Duration;
use tempfile::Builder;

#[derive(Parser, Debug)]
#[command(version, about = "H# Compiler Driver", long_about = None)]
struct Args {
    /// Input source file (.h#)
    input: String,

    /// Output executable file
    #[arg(short, long, default_value = "a.out")]
    output: String,

    /// Keep intermediate files (.o, .c)
    #[arg(long)]
    keep_temps: bool,
}

const RUNTIME_C: &str = r#"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// I/O Functions expected by codegen
void write_int(int n) {
printf("%d\n", n);
}

void write_float(double f) {
printf("%f\n", f);
}

// String layout in H# is { char* ptr, long len }
// We receive the pointer to the struct.
void write_str(long* s) {
if (!s) { printf("(null)\n"); return; }
char* ptr = (char*)s[0];
long len = s[1];
fwrite(ptr, 1, len, stdout);
printf("\n");
}

// Simple Arena Allocator Wrappers
long arena_new(long capacity) {
return 0;
}

long arena_alloc(long arena_handle, long size) {
void* ptr = malloc(size);
if (!ptr) {
    fprintf(stderr, "Out of memory\n");
    exit(1);
    }
    memset(ptr, 0, size);
    return (long)ptr;
    }

    void arena_free(long arena_handle) {
    }
    "#;

    fn main() -> Result<()> {
        let args = Args::parse();

        // 1. Read Source
        println!("Compiling {}...", args.input);
        let src = fs::read_to_string(&args.input).context("Failed to read input file")?;

        // 2. Parse
        // parse_code prints errors to stderr via ariadne. We don't use a spinner here to avoid interference.
        let program = match h_sharp_parser::parse_code(&src, &args.input) {
            Ok(p) => p,
            Err(e) => return Err(e),
        };

        // 3. Compile to Object Bytes
        let pb = ProgressBar::new_spinner();
        pb.set_style(ProgressStyle::default_spinner().template("{spinner:.green} {msg}").unwrap());
        pb.set_message("Compiling to object code...");
        pb.enable_steady_tick(Duration::from_millis(100));

        let mut obj_file = Builder::new().suffix(".o").tempfile()?;
        let obj_path = obj_file.path().to_str().unwrap().to_string();

        match h_sharp_compiler::compile_program(&program, &obj_path) {
            Ok(_) => {},
            Err(e) => {
                pb.finish_and_clear();
                return Err(e.context("Codegen failed"));
            }
        }

        // 4. Create Runtime C file
        pb.set_message("Generating runtime...");
        let mut c_file = Builder::new().suffix(".c").tempfile()?;
        c_file.write_all(RUNTIME_C.as_bytes())?;
        let c_path = c_file.path().to_str().unwrap().to_string();

        // 5. Link
        pb.set_message("Linking...");
        let status = Command::new("cc")
        .arg(&obj_path)
        .arg(&c_path)
        .arg("-o")
        .arg(&args.output)
        .arg("-lm")
        .status()
        .context("Failed to run linker (cc). Is a C compiler installed?")?;

        if !status.success() {
            pb.finish_and_clear();
            return Err(anyhow::anyhow!("Linker failed"));
        }

        // Optional: Copy temps if keep_temps is on
        if args.keep_temps {
            let _ = fs::copy(&obj_path, format!("{}.o", args.output));
            let _ = fs::copy(&c_path, format!("{}_runtime.c", args.output));
        }

        pb.finish_with_message(format!("Build successful! Binary: ./{}", args.output));
        Ok(())
    }
