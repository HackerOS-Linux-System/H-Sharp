mod types;
mod run;

pub use run::{run, run_with_limit};

use wasm_bindgen::prelude::*;

/// The H# language version this playground build embeds (shown in the UI
/// footer, e.g. "H# v0.9 · interpreter backend"). Kept in sync manually
/// with `hsharp-cli`'s own version string rather than sharing a single
/// source of truth, since pulling in `hsharp-cli` here would drag in its
/// non-wasm-friendly dependencies (`clap`, `indicatif`, ...) for a single
/// string constant.
#[wasm_bindgen]
pub fn version() -> String {
    // Cargo.toml's workspace version (`0.9.0`) — shown as e.g. "v0.9".
    env!("CARGO_PKG_VERSION").to_string()
}

/// JSON array of the H# editions this build understands, oldest first
/// (`["2026"]`) — lets the playground UI offer a `using "<year>"` picker
/// without hard-coding the list.
#[wasm_bindgen]
pub fn editions() -> String {
    let years: Vec<&str> = hsharp_parser::edition::Edition::ALL.iter().map(|e| e.as_str()).collect();
    serde_json::to_string(&years).unwrap_or_else(|_| "[]".to_string())
}

/// The newest edition this build understands (`"2026"`) — also what a
/// snippet without `using` is read as in the playground.
#[wasm_bindgen]
pub fn latest_edition() -> String {
    hsharp_parser::edition::Edition::LATEST.as_str().to_string()
}

/// Call once, as early as possible on the JS side (right after the wasm
/// module loads), if built with the default `console_error_panic_hook`
/// feature. Without this, a Rust panic that somehow *isn't* caught by
/// `run()`'s own `catch_unwind` (there shouldn't be one — but "shouldn't"
/// isn't "can't", e.g. a panic during `serde_json` serialization itself)
/// shows up in devtools as an opaque "unreachable executed" WASM trap with
/// no message. With the hook installed, it prints the real Rust panic
/// message and location instead.
#[wasm_bindgen(start)]
pub fn init_panic_hook() {
    #[cfg(feature = "console_error_panic_hook")]
    console_error_panic_hook::set_once();
}
