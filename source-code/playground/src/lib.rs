use std::panic::{self, AssertUnwindSafe};
use serde::Serialize;
use wasm_bindgen::prelude::*;

use hsharp_interpreter::Interpreter;

#[derive(Serialize)]
struct Diagnostic {
    message: String,
}

#[derive(Serialize)]
struct RunResult {
    /// Whether the program parsed *and* ran to completion without a
    /// top-level runtime error or panic. `false` doesn't necessarily mean
    /// nothing printed — a program can `write(...)` several lines and
    /// *then* hit an error; `stdout` still has everything printed before
    /// that point, exactly like a real terminal session would.
    ok: bool,
    /// Everything the program printed via `write`/`print`/`println`, in
    /// order, concatenated. Empty string if nothing was printed (or if
    /// parsing failed before any code could run).
    stdout: String,
    /// Parse errors, if any — each already rendered as a human-readable,
    /// source-quoting message (via `hsharp_parser`'s own error renderer),
    /// so the playground UI can just display these as-is.
    parse_errors: Vec<Diagnostic>,
    /// Type errors, if any — populated (and `ok` forced `false`, execution
    /// skipped entirely) whenever parsing succeeded but `hsharp-typecheck`
    /// found at least one `Severity::Error` diagnostic. Warnings (e.g. an
    /// unused variable) are reported here too but don't block execution —
    /// only errors do, matching `hsharp compile`'s own behavior.
    type_errors: Vec<Diagnostic>,
    /// The runtime error or panic message, if execution started but
    /// didn't finish cleanly. `None` when `ok` is `true`, or when parsing
    /// failed before execution could start (see `parse_errors` instead).
    runtime_error: Option<String>,
}

/// Runs a complete H# program's `main()` with a bounded number of
/// statement executions (see `Interpreter::step_limit`), and returns
/// everything it printed as a JSON string (see `RunResult`).
///
/// This is the entry point the playground frontend should actually call —
/// plain `run()` below has no step limit at all and is kept only for
/// embedders that already run untrusted-input-adjacent code inside their
/// own hard wall-clock boundary (e.g. a Worker the host page can
/// `.terminate()`). For a public-facing playground, defense in depth
/// matters: a step limit bounds runaway interpreter work *between*
/// statements (protects against e.g. a single huge allocation inside one
/// non-looping statement), while an *outer* Worker timeout bounds wall-clock
/// time regardless of what's running — see `docs/playground/index.html`'s
/// `runInWorker()`, which does both together. Neither alone is a complete
/// answer; see the module doc comment's "Sandboxing note".
#[wasm_bindgen]
pub fn run_with_limit(source: &str, max_steps: u32) -> String {
    run_inner(source, Some(max_steps as u64))
}

/// Runs a complete H# program's `main()` and returns everything it
/// printed, as a JSON string (see `RunResult`). This is the only entry
/// point the playground frontend needs to call.
///
/// Every failure mode — a parse error, a runtime error (`RuntimeError`),
/// or an outright Rust panic from deep inside a builtin (see the module
/// doc comment above) — is caught and reported back as data, never as a
/// thrown JS exception. The playground UI can therefore always just do
/// `JSON.parse(run(source))` and branch on `.ok` without a `try`/`catch`.
#[wasm_bindgen]
pub fn run(source: &str) -> String {
    run_inner(source, None)
}

fn run_inner(source: &str, max_steps: Option<u64>) -> String {
    let parsed = hsharp_parser::parse(source, "playground.h#");

    if parsed.has_errors() {
        let result = RunResult {
            ok: false,
            stdout: String::new(),
            parse_errors: parsed.errors.iter()
                .map(|e| Diagnostic { message: e.render(&parsed.source) })
                .collect(),
            type_errors: vec![],
            runtime_error: None,
        };
        return serde_json::to_string(&result).unwrap_or_else(|_| fallback_error_json("internal error: failed to serialize parse errors"));
    }

    // Real type checking, not skipped — see the module doc comment's "Real
    // type checking" section for why this changed. `TypeChecker::new()`
    // + `check_module` mirror exactly what `hsharp compile`/`hsharp check`
    // do on the CLI; `hsharp-typecheck` has no LLVM dependency (that's the
    // whole reason it's a separate crate now), so there's nothing
    // WASM-incompatible about running it here.
    let mut tc = hsharp_typecheck::TypeChecker::new();
    let diags = tc.check_module(&parsed.module);
    let has_type_errors = diags.iter().any(|d| matches!(d.severity, hsharp_typecheck::Severity::Error));
    if has_type_errors {
        let result = RunResult {
            ok: false,
            stdout: String::new(),
            parse_errors: vec![],
            type_errors: diags.iter().map(|d| Diagnostic { message: format_type_diag(d, &parsed.source) }).collect(),
            runtime_error: None,
        };
        return serde_json::to_string(&result).unwrap_or_else(|_| fallback_error_json("internal error: failed to serialize type errors"));
    }
    // Warnings (if any) don't block execution, and this v1 doesn't
    // currently surface them separately when there's no error alongside
    // them — a real "warnings even on a clean run" UI affordance is a
    // small, independent follow-up, not blocked on anything architectural.

    // `catch_unwind` needs its closure to be `UnwindSafe`; `Interpreter`
    // holds interior-mutable state (the reactor, captured stdout buffer)
    // that Rust's conservative auto-trait check doesn't consider unwind-
    // safe by default. `AssertUnwindSafe` is the right call here
    // specifically *because* we never touch `interp` again after a panic
    // (we only read `interp.stdout` in the success path below) — there's
    // no way for a partially-mutated, panicked-mid-write state to leak
    // out and be observed.
    let outcome = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut interp = Interpreter::new();
        interp.captured_output = true;
        interp.step_limit = max_steps;
        let run_result = interp.run_module(&parsed.module);
        (interp.stdout, run_result)
    }));

    let result = match outcome {
        Ok((stdout, Ok(()))) => RunResult {
            ok: true,
            stdout,
            parse_errors: vec![],
            type_errors: vec![],
            runtime_error: None,
        },
        // `exit(0)` is a normal, successful early termination (see the
        // `RuntimeError::Exit` doc comment) — not a runtime error. Any
        // other exit code is still not a *panic*, just a program that
        // asked to stop with a non-zero status; report it plainly rather
        // than dressing it up as a crash.
        Ok((stdout, Err(hsharp_interpreter::RuntimeError::Exit(0)))) => RunResult {
            ok: true,
            stdout,
            parse_errors: vec![],
            type_errors: vec![],
            runtime_error: None,
        },
        Ok((stdout, Err(hsharp_interpreter::RuntimeError::Exit(code)))) => RunResult {
            ok: false,
            stdout,
            parse_errors: vec![],
            type_errors: vec![],
            runtime_error: Some(format!("exited with status {}", code)),
        },
        Ok((stdout, Err(runtime_err))) => RunResult {
            ok: false,
            stdout,
            parse_errors: vec![],
            type_errors: vec![],
            runtime_error: Some(runtime_err.to_string()),
        },
        Err(panic_payload) => RunResult {
            ok: false,
            // Best-effort: we can't recover partial stdout across a panic
            // (the `Interpreter` that owned it is gone, unwound with the
            // panic) — see the module doc comment for why this can
            // legitimately happen (e.g. a program calling `exec(...)`,
            // which has no OS process to spawn in a browser tab).
            stdout: String::new(),
            parse_errors: vec![],
            type_errors: vec![],
            runtime_error: Some(format!("panicked: {}", panic_message(&panic_payload))),
        },
    };

    serde_json::to_string(&result).unwrap_or_else(|_| fallback_error_json("internal error: failed to serialize run result"))
}

fn panic_message(payload: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() { return s.to_string(); }
    if let Some(s) = payload.downcast_ref::<String>() { return s.clone(); }
    "(no message)".to_string()
}

/// Renders a `hsharp_typecheck::Diagnostic` the same way `hover.rs`-style
/// consumers want: a plain message string with any fix-it hints appended,
/// consistent with how parse errors are rendered (`e.render(&parsed.source)`
/// above) — the playground UI doesn't need to know or care whether a given
/// message came from the parser or the typechecker, both are just strings
/// in a `Diagnostic { message }` list.
fn format_type_diag(d: &hsharp_typecheck::Diagnostic, _source: &str) -> String {
    let mut msg = d.message.clone();
    if !d.hints.is_empty() {
        msg.push_str("\nhint: ");
        msg.push_str(&d.hints.join("; "));
    }
    msg
}

fn fallback_error_json(msg: &str) -> String {
    format!(r#"{{"ok":false,"stdout":"","parse_errors":[],"runtime_error":{:?}}}"#, msg)
}

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
