mod cli;
mod config;
mod registry;
mod jit;
mod python_interop;
mod progress;
mod isolation;

fn main() {
    // Clean up sessions from dead processes (handles unexpected shutdowns)
    crate::config::cleanup_stale_sessions();

    if let Err(e) = cli::run() {
        eprintln!("\x1b[31merror:\x1b[0m {}", e);
        std::process::exit(1);
    }
}
