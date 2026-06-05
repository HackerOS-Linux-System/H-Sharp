mod cli;
mod config;
mod installer;
mod isolation;
mod jit;
mod lockfile;
mod progress;
mod python_interop;
mod registry;
mod workspace;
mod fmt_cmd;
mod test_runner;
mod doc_gen;

fn main() {
    cli::run().unwrap_or_else(|e| {
        eprintln!("  \x1b[1;31merror:\x1b[0m {}", e);
        std::process::exit(1);
    });
}
