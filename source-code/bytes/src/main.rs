/// bytes — H# RAM-JIT package manager
/// Libraries in: ~/.hackeros/H#/libs/<session>/ (tmpfs, RAM-backed, cleaned on reboot)
/// Vira cache in: ~/.hackeros/H#/.cache/ (persistent, isolated env per package)

mod cli;
mod config;
mod registry;
mod jit;
mod python_interop;
mod progress;
mod isolation;

fn main() {
    if let Err(e) = cli::run() {
        eprintln!("\x1b[31merror:\x1b[0m {}", e);
        std::process::exit(1);
    }
}
