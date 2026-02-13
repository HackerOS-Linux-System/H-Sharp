use anyhow::{Context, Result};
use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use h_sharp_compiler::compile_program;
use indicatif::{ProgressBar, ProgressStyle};
use owo_colors::OwoColorize;
use ratatui::{
    backend::{Backend, CrosstermBackend},
    layout::{Constraint, Direction, Layout},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Borders, List, ListItem, ListState, Paragraph},
    Terminal,
};
use std::fs::{self};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;
use tempfile::Builder;
use wasmi::{Engine, Linker, Module, Store};

const H_SHARP_LIB_PATH: &str = "/usr/lib/h-sharp/libs";

// URL Bazowy do plików .h# (pojedyncze pliki)
const OFFICIAL_REPO_RAW: &str = "https://raw.githubusercontent.com/HackerOS-Linux-System/H-Sharp/main/libs/add-ons";

// URL Bazowy do katalogów (dla ghdir)
const OFFICIAL_REPO_TREE: &str = "https://github.com/HackerOS-Linux-System/H-Sharp/tree/main/libs/add-ons";

const COMMUNITY_REPO_URL: &str = "https://raw.githubusercontent.com/HackerOS-Linux-System/H-Sharp/main/libs/community/repo.hacker";

const RUNTIME_C: &str = r#"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void write_int(int n) { printf("%d\n", n); }
void write_float(double f) { printf("%f\n", f); }
void write_str(long* s) {
if (!s) { printf("(null)\n"); return; }
char* ptr = (char*)s[0];
long len = s[1];
fwrite(ptr, 1, len, stdout);
printf("\n");
}
long arena_new(long capacity) { return 0; }
long arena_alloc(long arena_handle, long size) {
void* ptr = malloc(size);
if (!ptr) { fprintf(stderr, "Out of memory\n"); exit(1); }
memset(ptr, 0, size);
return (long)ptr;
}
void arena_free(long arena_handle) {}
"#;

// Helper to draw clean boxes around text
fn print_boxed(title: &str, content: &str, color: &str) {
    let lines: Vec<&str> = content.lines().collect();
    let max_len = lines.iter().map(|l| l.len()).max().unwrap_or(0);
    let width = std::cmp::max(max_len + 4, title.len() + 10);

    let (top, border, bottom, title_fmt) = match color {
        "red" => ("┌", "│", "└", title.red().bold().to_string()),
        "green" => ("┌", "│", "└", title.green().bold().to_string()),
        "cyan" => ("┌", "│", "└", title.cyan().bold().to_string()),
        "yellow" => ("┌", "│", "└", title.yellow().bold().to_string()),
        _ => ("┌", "│", "└", title.white().bold().to_string()),
    };

    let h_line = "─".repeat(width - 2);
    let top_right = "┐";
    let bottom_right = "┘";
    let rem_len = width.saturating_sub(title.len() + 7);

    println!("{}{} {} {}{}", top, "─".repeat(3), title_fmt, "─".repeat(rem_len), top_right);
    for line in lines {
        println!("{} {:<w$} {}", border, line, border, w = width - 4);
    }
    println!("{}{}{}", bottom, h_line, bottom_right);
}

struct Args {
    subcommand: String,
    input: Option<String>,
    output: String,
    keep_temps: bool,
    library: Option<String>,
    community: bool,
}

impl Default for Args {
    fn default() -> Self {
        Self {
            subcommand: String::new(),
            input: None,
            output: "a.out".to_string(),
            keep_temps: false,
            library: None,
            community: false,
        }
    }
}

fn parse_args() -> Result<Args, lexopt::Error> {
    use lexopt::prelude::*;

    let mut args = Args::default();
    let mut parser = lexopt::Parser::from_env();

    if let Some(arg) = parser.next()? {
        match arg {
            Value(val) => args.subcommand = val.string()?,
            Long("help") | Short('h') => {
                print_help();
                std::process::exit(0);
            }
            _ => return Err(arg.unexpected()),
        }
    } else {
        print_help();
        std::process::exit(0);
    }

    while let Some(arg) = parser.next()? {
        match arg {
            Value(val) => {
                if args.subcommand == "compile" && args.input.is_none() {
                    args.input = Some(val.string()?);
                } else if (args.subcommand == "install"
                    || args.subcommand == "remove"
                    || args.subcommand == "search"
                    || args.subcommand == "update")
                    && args.library.is_none()
                    {
                        args.library = Some(val.string()?);
                    }
            }
            Long("output") | Short('o') => {
                args.output = parser.value()?.string()?;
            }
            Long("keep-temps") => {
                args.keep_temps = true;
            }
            Long("com") => {
                args.community = true;
            }
            Long("help") | Short('h') => {
                print_help();
                std::process::exit(0);
            }
            _ => return Err(arg.unexpected()),
        }
    }

    Ok(args)
}

fn print_help() {
    print_boxed(
        "H# CLI",
        "Usage: h# <command> [options]\n\nCommands:\n  compile     Compile .h# file\n  install     Install library (File or Add-on Folder)\n  remove      Remove library\n  search      Search library (TUI)\n  update      Update libraries",
                "cyan"
    );
}

fn main() -> Result<()> {
    let args = match parse_args() {
        Ok(a) => a,
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        }
    };

    match args.subcommand.as_str() {
        "compile" => {
            if let Some(input) = args.input {
                handle_compile(input, args.output, args.keep_temps)
            } else {
                print_boxed("Error", "Input file required for compile.", "red");
                std::process::exit(1);
            }
        }
        "install" => {
            if let Some(lib) = args.library {
                handle_install(lib, args.community)
            } else {
                print_boxed("Error", "Library name required.", "red");
                std::process::exit(1);
            }
        }
        "remove" => {
            if let Some(lib) = args.library {
                handle_remove(lib)
            } else {
                print_boxed("Error", "Library name required.", "red");
                std::process::exit(1);
            }
        }
        "search" => {
            if let Some(lib) = args.library {
                handle_search(lib)
            } else {
                print_boxed("Error", "Library name required for search.", "red");
                std::process::exit(1);
            }
        }
        "update" => handle_update(args.library),
        _ => {
            print_boxed("Error", &format!("Unknown command: {}", args.subcommand), "red");
            print_help();
            std::process::exit(1);
        }
    }
}

fn handle_compile(input: String, output: String, keep_temps: bool) -> Result<()> {
    print_boxed("Compiling", &format!("Source: {}\nTarget: {}", input, output), "cyan");

    let src = fs::read_to_string(&input).context("Failed to read input file")?;

    let program = match h_sharp_parser::parse_code(&src, &input) {
        Ok(p) => p,
        Err(e) => return Err(e),
    };

    let pb = ProgressBar::new_spinner();
    pb.set_style(
        ProgressStyle::default_spinner()
        .template("{spinner:.green} {msg}")
        .unwrap(),
    );
    pb.set_message("Compiling to object code...");
    pb.enable_steady_tick(Duration::from_millis(100));

    let obj_file = Builder::new().suffix(".o").tempfile()?;
    let obj_path = obj_file.path().to_str().unwrap().to_string();

    match compile_program(&program, &obj_path) {
        Ok(_) => {}
        Err(e) => {
            pb.finish_and_clear();
            return Err(e.context("Codegen failed"));
        }
    }

    pb.set_message("Generating runtime...");
    let mut c_file = Builder::new().suffix(".c").tempfile()?;
    c_file.write_all(RUNTIME_C.as_bytes())?;
    let c_path = c_file.path().to_str().unwrap().to_string();

    pb.set_message("Linking...");
    let status = Command::new("cc")
    .arg(&obj_path)
    .arg(&c_path)
    .arg("-o")
    .arg(&output)
    .arg("-lm")
    .status()
    .context("Failed to run linker (cc). Is a C compiler installed?")?;

    if !status.success() {
        pb.finish_and_clear();
        return Err(anyhow::anyhow!("Linker failed"));
    }

    if keep_temps {
        let _ = fs::copy(&obj_path, format!("{}.o", output));
        let _ = fs::copy(&c_path, format!("{}_runtime.c", output));
    }

    pb.finish_and_clear();
    print_boxed("Success", &format!("Build successful!\nBinary: ./{}", output), "green");
    Ok(())
}

fn handle_install(library: String, is_community: bool) -> Result<()> {
    print_boxed("Installation", &format!("Library: {}\nSource: {}", library, if is_community { "Community Repo" } else { "Official Repo" }), "cyan");

    let base_path = Path::new(H_SHARP_LIB_PATH);
    let envs_path = base_path.join("envs");

    if let Err(e) = fs::create_dir_all(&envs_path) {
        return Err(anyhow::anyhow!(
            "Failed to create directory structure at {:?}.\nError: {}.\nHint: Try running with sudo.",
            envs_path,
            e
        ));
    }

    // Znajdź dostępne środowisko (env)
    let mut env_name = "env".to_string();
    let mut counter = 1;
    let mut target_dir = envs_path.join(&env_name);

    loop {
        // Sprawdzamy, czy w danym env istnieje plik LUB folder o tej nazwie
        let lib_file_path = target_dir.join(format!("{}.h#", library));
        let lib_dir_path = target_dir.join(&library);

        if lib_file_path.exists() || lib_dir_path.exists() {
            counter += 1;
            env_name = format!("env{}", counter);
            target_dir = envs_path.join(&env_name);
        } else {
            break;
        }
    }
    fs::create_dir_all(&target_dir)?;

    let pb = ProgressBar::new_spinner();
    pb.set_message("Checking source availability...");
    pb.enable_steady_tick(Duration::from_millis(100));

    // KROK 1: Próba pobrania jako pojedynczy plik (Standard)
    let raw_url = if is_community {
        // Logika community (uproszczona, zakłada pliki)
        let list_url = COMMUNITY_REPO_URL;
        let response = reqwest::blocking::get(list_url).context("Failed to fetch community repo")?.text()?;
        let mut found_url = None;
        for line in response.lines() {
            if let Some((name, url)) = line.split_once('-') {
                if name.trim().replace("\"", "") == library {
                    found_url = Some(url.trim().replace("\"", ""));
                    break;
                }
            }
        }
        found_url
    } else {
        Some(format!("{}/{}.h%23", OFFICIAL_REPO_RAW, library))
    };

    if let Some(url) = raw_url {
        let resp_check = reqwest::blocking::get(&url);

        if let Ok(mut resp) = resp_check {
            if resp.status().is_success() {
                // Pobieranie pliku
                let total_size = resp.content_length().unwrap_or(0);
                pb.set_message(format!("Downloading file {}...", library));
                pb.set_length(total_size);

                let mut content = Vec::new();
                let mut buffer = [0; 8192];
                loop {
                    let bytes_read = resp.read(&mut buffer)?;
                    if bytes_read == 0 { break; }
                    content.extend_from_slice(&buffer[..bytes_read]);
                    pb.inc(bytes_read as u64);
                }

                let final_path = target_dir.join(format!("{}.h#", library));
                fs::write(&final_path, &content)?;

                pb.finish_and_clear();
                print_boxed("Installed", &format!("Single-file library installed.\nLocation: {}", final_path.display()), "green");
                return Ok(());
            }
        }
    }

    // KROK 2: Jeśli plik nie istnieje, zakładamy, że to ADD-ON (Katalog)
    // Wymaga narzędzia ghdir
    pb.set_message("File not found, detecting as directory/add-on...");

    // Sprawdź czy ghdir jest w systemie
    if which::which("ghdir").is_err() {
        pb.finish_and_clear();
        return Err(anyhow::anyhow!("Tool 'ghdir' not found in PATH! It is required to download directories/add-ons."));
    }

    let dir_url = if is_community {
        // Dla community musielibyśmy mieć URL do katalogu, tu upraszczamy, że ghdir bierze URL repo
        // Zakładamy, że dla community link z repo.hacker wskazuje na URL katalogu jeśli nie jest plikiem
        return Err(anyhow::anyhow!("Community directory download not fully implemented without direct URL logic."));
    } else {
        format!("{}/{}", OFFICIAL_REPO_TREE, library)
    };

    pb.set_message(format!("Downloading directory via ghdir: {}...", library));

    // Wywołanie ghdir
    // ghdir pobiera do bieżącego katalogu
    let output = Command::new("ghdir")
    .arg(&dir_url)
    .output()
    .context("Failed to execute ghdir")?;

    if !output.status.success() {
        pb.finish_and_clear();
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(anyhow::anyhow!("ghdir failed: {}", stderr));
    }

    pb.set_message("Moving files to isolation...");

    // ghdir pobiera do katalogu o nazwie ostatniego segmentu URL (czyli nazwa biblioteki)
    let downloaded_path = std::env::current_dir()?.join(&library);
    let final_dest_path = target_dir.join(&library);

    if downloaded_path.exists() && downloaded_path.is_dir() {
        if let Err(e) = fs::rename(&downloaded_path, &final_dest_path) {
            // Fallback copy+delete jeśli rename nie działa między partycjami
            pb.finish_and_clear();
            return Err(anyhow::anyhow!("Failed to move downloaded directory: {}", e));
        }
    } else {
        pb.finish_and_clear();
        return Err(anyhow::anyhow!("ghdir completed, but directory '{}' was not found in current path.", library));
    }

    pb.finish_and_clear();

    println!("Verifying environment...");
    if let Err(e) = verify_wasm_environment() {
        print_boxed("Warning", &format!("WASM isolation check failed:\n{}", e), "yellow");
    }

    print_boxed("Installed", &format!("Add-on installed successfully (Directory mode).\nLocation: {}", final_dest_path.display()), "green");

    Ok(())
}

fn handle_remove(library: String) -> Result<()> {
    let base_path = Path::new(H_SHARP_LIB_PATH).join("envs");
    if !base_path.exists() {
        return Err(anyhow::anyhow!("No libraries installed yet."));
    }

    let mut found = false;
    for entry in fs::read_dir(base_path)? {
        let entry = entry?;
        if entry.file_type()?.is_dir() {
            let env_path = entry.path();

            // Sprawdź plik .h#
            let lib_file = env_path.join(format!("{}.h#", library));
            if lib_file.exists() {
                fs::remove_file(&lib_file)?;
                print_boxed("Removed", &format!("File removed from:\n{}", env_path.display()), "green");
                found = true;
            }

            // Sprawdź katalog
            let lib_dir = env_path.join(&library);
            if lib_dir.exists() && lib_dir.is_dir() {
                fs::remove_dir_all(&lib_dir)?;
                print_boxed("Removed", &format!("Directory removed from:\n{}", env_path.display()), "green");
                found = true;
            }
        }
    }

    if !found {
        print_boxed("Not Found", "Library not found in any environment.", "red");
    }
    Ok(())
}

fn handle_search(library: String) -> Result<()> {
    let mut results = Vec::new();
    let base_path = Path::new(H_SHARP_LIB_PATH).join("envs");

    // Search local
    if base_path.exists() {
        if let Ok(entries) = fs::read_dir(base_path) {
            for entry in entries.flatten() {
                if let Ok(ft) = entry.file_type() {
                    if ft.is_dir() {
                        let env_path = entry.path();
                        let env_name = entry.file_name().to_string_lossy().to_string();

                        // 1. Sprawdź czy istnieje plik .h#
                        let file_target = env_path.join(format!("{}.h#", library));
                        if file_target.exists() {
                            results.push(format!("[LOCAL FILE] {} (in {})", library, env_name));
                        }

                        // 2. Sprawdź czy istnieje katalog o tej nazwie (Add-on)
                        let dir_target = env_path.join(&library);
                        if dir_target.exists() && dir_target.is_dir() {
                            results.push(format!("[LOCAL DIR]  {} (in {})", library, env_name));
                        }
                    }
                }
            }
        }
    }

    // Community Check (uproszczony)
    if let Ok(resp) = reqwest::blocking::get(COMMUNITY_REPO_URL) {
        if let Ok(text) = resp.text() {
            for line in text.lines() {
                if line.contains(&library) {
                    results.push(format!("[COMMUNITY] Found match: {}", line.trim()));
                }
            }
        }
    }

    if results.is_empty() {
        results.push(format!("No results found for '{}'.", library));
    }

    // Uruchomienie TUI
    enable_raw_mode()?;
    let mut stdout = std::io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let res = run_search_tui(&mut terminal, &library, results);

    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
             LeaveAlternateScreen,
             DisableMouseCapture
    )?;
    terminal.show_cursor()?;

    if let Err(e) = res {
        println!("Error running TUI: {:?}", e);
    }

    Ok(())
}

fn run_search_tui<B: Backend>(
    terminal: &mut Terminal<B>,
    query: &str,
    items: Vec<String>,
) -> Result<()> {
    let mut list_state = ListState::default();
    list_state.select(Some(0));

    loop {
        terminal.draw(|f| {
            let chunks = Layout::default()
            .direction(Direction::Vertical)
            .constraints([Constraint::Length(3), Constraint::Min(0)].as_ref())
            .split(f.size());

            let title = Paragraph::new(format!("H# Search Results for: '{}' (Press 'q' to exit)", query))
            .style(Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD))
            .block(Block::default().borders(Borders::ALL).title("Search"));
            f.render_widget(title, chunks[0]);

            let list_items: Vec<ListItem> = items
            .iter()
            .map(|i| ListItem::new(Line::from(Span::raw(i))))
            .collect();

            let list = List::new(list_items)
            .block(Block::default().borders(Borders::ALL).title("Results"))
            .highlight_style(Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD))
            .highlight_symbol(">> ");

            f.render_stateful_widget(list, chunks[1], &mut list_state);
        })?;

        if let Event::Key(key) = event::read()? {
            match key.code {
                KeyCode::Char('q') | KeyCode::Esc => return Ok(()),
                KeyCode::Down => {
                    let i = match list_state.selected() {
                        Some(i) => {
                            if i >= items.len() - 1 { 0 } else { i + 1 }
                        }
                        None => 0,
                    };
                    list_state.select(Some(i));
                }
                KeyCode::Up => {
                    let i = match list_state.selected() {
                        Some(i) => {
                            if i == 0 { items.len() - 1 } else { i - 1 }
                        }
                        None => 0,
                    };
                    list_state.select(Some(i));
                }
                _ => {}
            }
        }
    }
}

fn handle_update(library: Option<String>) -> Result<()> {
    if let Some(lib) = library {
        print_boxed("Update", &format!("Updating {}...", lib), "yellow");
    } else {
        print_boxed("Update", "Updating all libraries...", "yellow");
    }
    // Tu można dodać logikę: git pull wewnątrz katalogów lub ponowne pobranie
    Ok(())
}

fn verify_wasm_environment() -> Result<()> {
    let engine = Engine::default();
    let wat = r#"(module)"#;
    let module = Module::new(&engine, wat.as_bytes())?;
    type HostState = ();
    let mut store = Store::new(&engine, ());
    let linker = Linker::<HostState>::new(&engine);
    let _instance = linker
    .instantiate(&mut store, &module)?
    .start(&mut store)?;
    Ok(())
}
