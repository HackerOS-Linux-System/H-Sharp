use clap::{Parser, Subcommand};

mod registry;
mod installer;
mod lockfile;

#[derive(Parser)]
#[command(name = "bytes", version, about = "bytes — H# package manager")]
pub struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
pub enum Command {
    /// Add a package
    Add { package: String },
    /// Remove a package
    Remove { package: String },
    /// Install all packages from h#.json
    Install,
    /// List installed packages
    List,
    /// Search the Bytes Repository
    Search { query: String },
    /// Show package info
    Info { package: String },
    /// Update all packages
    Update,
}

fn main() {
    let cli = Cli::parse();
    match cli.command {
        Command::Add { package }    => installer::add(&package),
        Command::Remove { package } => installer::remove(&package),
        Command::Install            => installer::install_all(),
        Command::List               => installer::list(),
        Command::Search { query }   => registry::search(&query),
        Command::Info { package }   => registry::info(&package),
        Command::Update             => installer::update_all(),
    }
}
