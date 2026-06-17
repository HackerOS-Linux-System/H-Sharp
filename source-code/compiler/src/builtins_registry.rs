use crate::typechecker::HType;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Backend {
    /// `hsharp preview` / REPL — tree-walking interpreter crate.
    Interpreter,
    /// `h#` — the LLVM-backed AOT compiler (this crate).
    Llvm,
}

impl Backend {
    pub const ALL: [Backend; 2] = [Backend::Interpreter, Backend::Llvm];

    pub fn name(&self) -> &'static str {
        match self {
            Backend::Interpreter => "interpreter (hsharp preview)",
            Backend::Llvm        => "h# (LLVM, --release)",
        }
    }
}

/// One builtin function's shape + which backends implement it.
pub struct BuiltinSpec {
    /// The name(s) users call (aliases, e.g. "trim"/"str_trim").
    pub names:   &'static [&'static str],
    /// Parameter types (for typechecking; arity overloads like `exec`
    /// list their MAX arity here and the typechecker stays permissive
    /// about fewer args — see typechecker.rs comment on `exec`).
    pub params:  fn() -> Vec<HType>,
    pub ret:     fn() -> HType,
    /// The `hsh_*` C symbol used by the H# runtime (`runtime.rs`,
    /// `builtins.rs::LlvmBuiltins`). `None` for builtins implemented purely
    /// as AST rewrites (e.g. derive dispatch — see optimize_ast.rs) with no
    /// runtime counterpart.
    pub c_symbol: Option<&'static str>,
    /// Backends that currently have a working implementation. Used by
    /// `features.rs` to produce "not supported by backend X" errors.
    pub backends: &'static [Backend],
    /// Short human description, used in `bytes doc`/`--list-builtins`.
    pub doc: &'static str,
}

/// The canonical builtin table.
pub static BUILTINS: &[BuiltinSpec] = &[
    BuiltinSpec {
        names: &["shell", "cmd"],
        params: || vec![HType::Str],
        ret: || HType::Str,
        c_symbol: Some("hsh_shell"),
        backends: &[Backend::Interpreter, Backend::Llvm],
        doc: "Run a command through /bin/sh and capture stdout+stderr. \
SECURITY: prefer shell_escape()/exec() for untrusted input.",
    },
BuiltinSpec {
    names: &["shell_escape", "shquote"],
    params: || vec![HType::Str],
    ret: || HType::Str,
    c_symbol: Some("hsh_shell_escape"),
    // Implemented on Llvm (runtime.rs + builtins.rs, this session).
    // Interpreter dispatch still needs a matching arm (not in this
    // crate — see interpreter/src/lib.rs).
    backends: &[Backend::Llvm],
    doc: "POSIX single-quote-escape a string for safe embedding into shell().",
},
BuiltinSpec {
    names: &["exec"],
    params: || vec![HType::Str, HType::Str, HType::Str, HType::Str],
    ret: || HType::Str,
    c_symbol: Some("hsh_exec1"), // codegen picks exec1..4 by call arity
    backends: &[Backend::Llvm],
    doc: "Direct fork+execve (no shell). exec(cmd[, a1[, a2[, a3]]]) -> captured stdout+stderr.",
},
BuiltinSpec {
    names: &["py_eval"],
    params: || vec![HType::Str],
    ret: || HType::Str,
    c_symbol: Some("hsh_py_eval"),
    backends: &[Backend::Llvm],
    doc: "extern [python, ...] phase 1 bridge: execvp(\"python3\", [\"-c\", code]) -> stdout.",
},
BuiltinSpec {
    names: &["regex_match"],
    params: || vec![HType::Str, HType::Str],
    ret: || HType::Bool,
    c_symbol: Some("hsh_regex_match"),
    backends: &[Backend::Llvm],
    doc: "PCRE2 regex match (§11) — full lookahead/lookbehind/non-greedy support.",
},
BuiltinSpec {
    names: &["regex_find"],
    params: || vec![HType::Str, HType::Str],
    ret: || HType::Str,
    c_symbol: Some("hsh_regex_find"),
    backends: &[Backend::Llvm],
    doc: "PCRE2 regex find — returns first match or empty string.",
},
BuiltinSpec {
    names: &["regex_replace"],
    params: || vec![HType::Str, HType::Str, HType::Str],
    ret: || HType::Str,
    c_symbol: Some("hsh_regex_replace"),
    backends: &[Backend::Llvm],
    doc: "PCRE2 regex replace (global, supports $1/$2 capture group refs).",
},
BuiltinSpec {
    names: &["db_query_bind"],
    params: || vec![HType::Str, HType::Str, HType::Str, HType::Str, HType::Str],
    ret: || HType::Str,
    c_symbol: Some("hsh_sqlite_query_bind1"), // codegen picks bind1/2/3 by arity
    backends: &[Backend::Llvm],
    doc: "Parameterized SQLite query (§12) — SQL-injection-safe via sqlite3_bind_text. \
db_query_bind(db, \"SELECT * FROM t WHERE id=?\", id)",
},
BuiltinSpec {
    names: &["await"],
    params: || vec![HType::Any],
    ret: || HType::Any,
    c_symbol: None,
    // Interpreter-only — `h#` (LLVM) has no async runtime. A call site
    // using `await` when compiling with `h#` should error via
    // features.rs rather than silently treating it as a synchronous
    // no-op.
    backends: &[Backend::Interpreter],
    doc: "Await an async expression. Interpreter only until h# gains an async runtime.",
},
];

/// Look up a builtin spec by any of its names.
pub fn find(name: &str) -> Option<&'static BuiltinSpec> {
    BUILTINS.iter().find(|b| b.names.contains(&name))
}

/// Does `name` have a working implementation on `backend`?
/// Returns `true` for any name not in `BUILTINS` at all (user-defined
/// functions aren't builtins and aren't restricted by this table).
pub fn supported_on(name: &str, backend: Backend) -> bool {
    match find(name) {
        Some(spec) => spec.backends.contains(&backend),
        None => true,
    }
}
