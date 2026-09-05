mod types;
mod run;

pub use run::{run, run_with_limit};

use wasm_bindgen::prelude::*;

/// The H# language version this playground build embeds (shown in the UI
/// footer, e.g. "H# v0.8 · interpreter backend"). Kept in sync manually
/// with `hsharp-cli`'s own version string rather than sharing a single
/// source of truth, since pulling in `hsharp-cli` here would drag in its
/// non-wasm-friendly dependencies (`clap`, `indicatif`, ...) for a single
/// string constant.
#[wasm_bindgen]
pub fn version() -> String {
    "0.8".to_string()
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
