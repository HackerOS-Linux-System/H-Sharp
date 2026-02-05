mod ast;
mod compiler;

use anyhow::{Context, Result};
use std::env;
use std::fs::File;
use std::io::{BufReader, Write};

use crate::ast::Program;
use crate::compiler::compile_program;

fn main() -> Result<()> {
    // CLI: hackerc <input.json> <output.o>
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: hackerc <input_ir.json> <output.o>");
        std::process::exit(1);
    }

    let input_path = &args[1];
    let output_path = &args[2];

    let file = File::open(input_path).with_context(|| format!("Failed to open input file {}", input_path))?;
    let reader = BufReader::new(file);

    let program: Program = serde_json::from_reader(reader).context("Failed to parse JSON IR")?;

    let object_bytes = compile_program(program)?;

    let mut outfile = File::create(output_path).with_context(|| format!("Failed to create output file {}", output_path))?;
    outfile.write_all(&object_bytes)?;

    println!("Backend compilation successful. Object file written to {}", output_path);
    Ok(())
}
