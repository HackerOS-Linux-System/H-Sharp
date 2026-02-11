use anyhow::{Context, Result};
use clap::Parser;
use indicatif::{ProgressBar, ProgressStyle};
use std::env;
use std::process::Command;
use std::time::Duration;
use tempfile::NamedTempFile;

#[derive(Parser, Debug)]
#[command(version, about = "H# CLI Tool", long_about = None)]
struct Args {
    /// Input source file
    input: String,

    /// Output object file
    #[arg(short, long)]
    output: String,
}

fn main() -> Result<()> {
    let args = Args::parse();

    // Get home dir
    let home = env::var("HOME").context("Failed to get HOME env")?;
    let bin_path = format!("{}/.hackeros/H-Sharp", home);
    let parser_bin = format!("{}/h-sharp-parser", &bin_path);
    let compiler_bin = format!("{}/h-sharp-compiler", &bin_path);

    // Create temp json file
    let temp_json = NamedTempFile::new().context("Failed to create temp file")?;
    let temp_json_path = temp_json.path().to_str().unwrap().to_string();

    // Progress bar for parsing
    let pb = ProgressBar::new_spinner();
    pb.enable_steady_tick(Duration::from_millis(100));
    pb.set_style(ProgressStyle::default_spinner().template("{spinner:.green} {msg}").unwrap());
    pb.set_message(format!("Parsing {}...", args.input));

    let parser_status = Command::new(&parser_bin)
        .arg(&args.input)
        .arg(&temp_json_path)
        .status()
        .context("Failed to run parser")?;

    if !parser_status.success() {
        pb.finish_with_message("Parsing failed");
        return Err(anyhow::anyhow!("Parser failed"));
    }
    pb.finish_with_message("Parsing complete");

    // Progress bar for compiling
    let pb = ProgressBar::new_spinner();
    pb.enable_steady_tick(Duration::from_millis(100));
    pb.set_style(ProgressStyle::default_spinner().template("{spinner:.green} {msg}").unwrap());
    pb.set_message("Compiling...");

    let compiler_status = Command::new(&compiler_bin)
        .arg(&temp_json_path)
        .arg(&args.output)
        .status()
        .context("Failed to run compiler")?;

    if !compiler_status.success() {
        pb.finish_with_message("Compilation failed");
        return Err(anyhow::anyhow!("Compiler failed"));
    }
    pb.finish_with_message(format!("Compilation successful: {}", args.output));

    Ok(())
}
