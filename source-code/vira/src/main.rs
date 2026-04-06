mod cli;
mod config;
mod progress;
mod registry;
mod installer;
mod settings;
mod hcl;

fn main() {
    if let Err(e) = cli::run() {
        eprintln!("\x1b[31merror:\x1b[0m {}", e);
        std::process::exit(1);
    }
}
