use clap::Parser;
use miette::{Diagnostic, NamedSource, SourceSpan};
use std::fs;
use thiserror::Error;

/// H# Error Reporter
/// Used by Virus Build System to display pretty errors
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to the source file (.hcs)
    #[arg(short, long)]
    file: String,

    /// Error message
    #[arg(short, long)]
    msg: String,

    /// Line number (1-based)
    #[arg(short, long, default_value_t = 1)]
    line: usize,

    /// Column number (1-based)
    #[arg(short, long, default_value_t = 1)]
    col: usize,

    /// Error code (e.g. H#001)
    #[arg(long, default_value = "H#_SYNTAX")]
    code: String,
}

#[derive(Error, Debug, Diagnostic)]
#[error("{message}")]
#[diagnostic(
code(h_sharp::transpilation_error),
             help("Check the syntax in your .hcs file.")
)]
struct HSharpError {
    message: String,
    #[source_code]
    src: NamedSource,
    #[label("Here")]
    span: SourceSpan,
}

fn main() -> miette::Result<()> {
    let args = Args::parse();

    // 1. Read the source file
    let source_content = match fs::read_to_string(&args.file) {
        Ok(content) => content,
        Err(_) => {
            eprintln!("Error: Could not read file {}", args.file);
            return Ok(());
        }
    };

    // 2. Calculate Byte Offset (SourceSpan) from Line/Col
    // Miette requires byte offset, but we get Line/Col from Parser
    let offset = get_offset(&source_content, args.line, args.col);
    let len = 1; // Default to highlighting 1 character if unknown length

    // 3. Construct the Diagnostic
    let err = HSharpError {
        message: args.msg,
        src: NamedSource::new(&args.file, source_content),
        span: SourceSpan::new(offset.into(), len.into()),
    };

    // 4. Render
    // We explicitly print it using debug report to force graphical output
    let report = miette::Report::new(err);
    eprint!("{:?}", report);

    Ok(())
}

fn get_offset(source: &str, line: usize, col: usize) -> usize {
    let mut current_line = 1;
    let mut offset = 0;

    for char in source.chars() {
        if current_line == line {
            // We found the line, add col to offset
            // col is 1-based, offset adds col-1
            return offset + (col.saturating_sub(1));
        }

        offset += char.len_utf8();
        if char == '\n' {
            current_line += 1;
        }
    }

    // Fallback if line out of bounds
    source.len().saturating_sub(1)
}
