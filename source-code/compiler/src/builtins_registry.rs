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
    names: &["run_cmd_exec"],
    params: || vec![HType::Str, HType::Int],
    ret: || HType::Int,
    c_symbol: Some("hsh_run_cmd_exec"),
    backends: &[Backend::Llvm],
    doc: "Internal: runs `cmd` via /bin/sh with a timeout (seconds; <=0 = none), \
returns the real exit code (-1 = couldn't start, -2 = timed out). Stdout/stderr are read \
back separately via run_cmd_last_stdout()/run_cmd_last_stderr() — see proc::run_cmd's \
H#-level wrapper in stdlib_shims.rs, which is what user code should actually call.",
},
BuiltinSpec {
    names: &["run_cmd_last_stdout"],
    params: || vec![],
    ret: || HType::Str,
    c_symbol: Some("hsh_run_cmd_last_stdout"),
    backends: &[Backend::Llvm],
    doc: "Internal: stdout captured by the most recent run_cmd_exec() call.",
},
BuiltinSpec {
    names: &["run_cmd_last_stderr"],
    params: || vec![],
    ret: || HType::Str,
    c_symbol: Some("hsh_run_cmd_last_stderr"),
    backends: &[Backend::Llvm],
    doc: "Internal: stderr captured by the most recent run_cmd_exec() call.",
},
BuiltinSpec {
    names: &["str_split_count"],
    params: || vec![HType::Str, HType::Str],
    ret: || HType::Int,
    c_symbol: Some("hsh_str_split_count"),
    backends: &[Backend::Llvm],
    doc: "Internal: how many parts `s` splits into on `sep`. See str_split's \
H#-level wrapper in stdlib_shims.rs, which is what user code should actually call.",
},
BuiltinSpec {
    names: &["str_split_part"],
    params: || vec![HType::Str, HType::Str, HType::Int],
    ret: || HType::Str,
    c_symbol: Some("hsh_str_split_part"),
    backends: &[Backend::Llvm],
    doc: "Internal: the i-th (0-indexed) part of `s` split on `sep`.",
},
BuiltinSpec {
    names: &["int_to_str"],
    params: || vec![HType::Int],
    ret: || HType::Str,
    c_symbol: Some("hsh_int_to_str"),
    backends: &[Backend::Llvm],
    doc: "conv::int_to_str — integer to its base-10 string representation.",
},
BuiltinSpec {
    names: &["str_to_int"],
    params: || vec![HType::Str],
    ret: || HType::Int,
    c_symbol: Some("hsh_str_to_int"),
    backends: &[Backend::Llvm],
    doc: "conv::str_to_int — parses a base-10 integer prefix; 0 if none found (never crashes on bad input).",
},
BuiltinSpec {
    names: &["env_get"],
    params: || vec![HType::Str],
    ret: || HType::Str,
    c_symbol: Some("hsh_env_get"),
    backends: &[Backend::Llvm],
    doc: "env::get — environment variable value, or \"\" if unset.",
},
BuiltinSpec {
    names: &["env_read_line"],
    params: || vec![],
    ret: || HType::Str,
    c_symbol: Some("hsh_env_read_line"),
    backends: &[Backend::Llvm],
    doc: "env::read_line — one line from stdin, trailing newline stripped; \"\" on EOF.",
},
BuiltinSpec {
    names: &["fs_remove"],
    params: || vec![HType::Str],
    ret: || HType::Int,
    c_symbol: Some("hsh_remove_file"),
    backends: &[Backend::Llvm],
    doc: "fs::remove — delete a single file.",
},
BuiltinSpec {
    names: &["fs_remove_dir"],
    params: || vec![HType::Str],
    ret: || HType::Int,
    c_symbol: Some("hsh_remove_dir_recursive"),
    backends: &[Backend::Llvm],
    doc: "fs::remove_dir — recursively delete a directory tree (shells out to `rm -rf`, see runtime/core.c's doc comment).",
},
BuiltinSpec {
    names: &["fs_rename"],
    params: || vec![HType::Str, HType::Str],
    ret: || HType::Int,
    c_symbol: Some("hsh_rename"),
    backends: &[Backend::Llvm],
    doc: "fs::rename — move/rename a file or directory.",
},
BuiltinSpec {
    names: &["json_set_str"],
    params: || vec![HType::Str, HType::Str, HType::Str],
    ret: || HType::Str,
    c_symbol: Some("hsh_json_set_str"),
    backends: &[Backend::Llvm],
    doc: "json::set_str — insert-or-replace a string field in a flat JSON object, returns the updated JSON text.",
},
BuiltinSpec {
    names: &["json_get_str"],
    params: || vec![HType::Str, HType::Str],
    ret: || HType::Str,
    c_symbol: Some("hsh_json_get"),
    backends: &[Backend::Llvm],
    doc: "json::get_str — read a string field from a flat JSON object; \"\" if absent.",
},
BuiltinSpec {
    names: &["sin", "cos", "tan", "sqrt", "floor", "ceil"],
    params: || vec![HType::F64],
    ret: || HType::F64,
    c_symbol: None, // dispatched by name in codegen.rs, not a 1:1 c_symbol
    backends: &[Backend::Llvm],
    doc: "math:: — thin libm wrappers.",
},
BuiltinSpec {
    names: &["pow"],
    params: || vec![HType::F64, HType::F64],
    ret: || HType::F64,
    c_symbol: Some("hsh_pow"),
    backends: &[Backend::Llvm],
    doc: "math::pow(base, exponent).",
},
BuiltinSpec {
    names: &["abs"],
    params: || vec![HType::Int],
    ret: || HType::Int,
    c_symbol: None, // dispatches to hsh_abs_i or hsh_abs_f by argument type
    backends: &[Backend::Llvm],
    doc: "math::abs — works on both int and float arguments.",
},
BuiltinSpec {
    names: &["min", "max"],
    params: || vec![HType::Int, HType::Int],
    ret: || HType::Int,
    c_symbol: None, // dispatches by argument type, same as abs
    backends: &[Backend::Llvm],
    doc: "math::min / math::max — work on both int and float arguments.",
},
BuiltinSpec {
    names: &["hostname"],
    params: || vec![],
    ret: || HType::Str,
    c_symbol: Some("hsh_hostname"),
    backends: &[Backend::Llvm],
    doc: "os::hostname.",
},
BuiltinSpec {
    names: &["username"],
    params: || vec![],
    ret: || HType::Str,
    c_symbol: Some("hsh_username"),
    backends: &[Backend::Llvm],
    doc: "os::username — $USER/$LOGNAME, falls back to the passwd database.",
},
BuiltinSpec {
    names: &["platform"],
    params: || vec![],
    ret: || HType::Str,
    c_symbol: Some("hsh_platform"),
    backends: &[Backend::Llvm],
    doc: "os::platform — \"linux\" / \"macos\" / \"windows\".",
},
BuiltinSpec {
    names: &["getcwd", "cwd"],
    params: || vec![],
    ret: || HType::Str,
    c_symbol: Some("hsh_getcwd"),
    backends: &[Backend::Llvm],
    doc: "env::cwd — current working directory.",
},
BuiltinSpec {
    names: &["env_set"],
    params: || vec![HType::Str, HType::Str],
    ret: || HType::Int,
    c_symbol: Some("hsh_setenv"),
    backends: &[Backend::Llvm],
    doc: "env::set — sets an environment variable for this process.",
},
BuiltinSpec {
    names: &["now_unix"],
    params: || vec![],
    ret: || HType::Int,
    c_symbol: Some("hsh_now_unix"),
    backends: &[Backend::Llvm],
    doc: "time::now_unix — seconds since the Unix epoch.",
},
BuiltinSpec {
    names: &["now_ms"],
    params: || vec![],
    ret: || HType::Int,
    c_symbol: Some("hsh_now_ms"),
    backends: &[Backend::Llvm],
    doc: "time — milliseconds since the Unix epoch.",
},
BuiltinSpec {
    names: &["sleep_ms"],
    params: || vec![HType::Int],
    ret: || HType::Int,
    c_symbol: Some("hsh_sleep_ms"),
    backends: &[Backend::Llvm],
    doc: "time::sleep_ms — blocks the current thread for the given duration.",
},
BuiltinSpec {
    names: &["base64_encode"],
    params: || vec![HType::Str],
    ret: || HType::Str,
    c_symbol: Some("hsh_base64_encode"),
    backends: &[Backend::Llvm],
    doc: "encoding::base64 encode (standard alphabet, '=' padded).",
},
BuiltinSpec {
    names: &["base64_decode"],
    params: || vec![HType::Str],
    ret: || HType::Str,
    c_symbol: Some("hsh_base64_decode"),
    backends: &[Backend::Llvm],
    doc: "encoding::base64 decode.",
},
BuiltinSpec {
    names: &["url_encode"],
    params: || vec![HType::Str],
    ret: || HType::Str,
    c_symbol: Some("hsh_url_encode"),
    backends: &[Backend::Llvm],
    doc: "encoding::url percent-encode (RFC 3986 unreserved chars left as-is).",
},
BuiltinSpec {
    names: &["url_decode"],
    params: || vec![HType::Str],
    ret: || HType::Str,
    c_symbol: Some("hsh_url_decode"),
    backends: &[Backend::Llvm],
    doc: "encoding::url percent-decode (also accepts '+' as space).",
},
BuiltinSpec {
    names: &["map_new"],
    params: || vec![HType::Int],
    ret: || HType::Any,
    c_symbol: Some("hsh_map_new"),
    backends: &[Backend::Llvm],
    doc: "HashMap constructor. map_new(true) for string keys (content hash/eq), \
map_new(false) for int keys. See runtime/core.c's HshMap doc comment.",
},
BuiltinSpec {
    names: &["map_set"],
    params: || vec![HType::Any, HType::Any, HType::Any],
    ret: || HType::Void,
    c_symbol: Some("hsh_map_set"),
    backends: &[Backend::Llvm],
    doc: "map_set(map, key, value) — insert or overwrite.",
},
BuiltinSpec {
    names: &["map_get", "map_get_int"],
    params: || vec![HType::Any, HType::Any],
    ret: || HType::Int,
    c_symbol: Some("hsh_map_get"),
    backends: &[Backend::Llvm],
    doc: "map_get(map, key) — 0 if absent; use map_has to distinguish absence from a stored 0.",
},
BuiltinSpec {
    names: &["map_get_str"],
    params: || vec![HType::Any, HType::Any],
    ret: || HType::Str,
    c_symbol: Some("hsh_map_get"),
    backends: &[Backend::Llvm],
    doc: "map_get_str(map, key) — same lookup as map_get, return reinterpreted as a string.",
},
BuiltinSpec {
    names: &["map_has"],
    params: || vec![HType::Any, HType::Any],
    ret: || HType::Bool,
    c_symbol: Some("hsh_map_has"),
    backends: &[Backend::Llvm],
    doc: "map_has(map, key) — real presence check (distinguishes absent from stored-0/false).",
},
BuiltinSpec {
    names: &["map_remove"],
    params: || vec![HType::Any, HType::Any],
    ret: || HType::Bool,
    c_symbol: Some("hsh_map_remove"),
    backends: &[Backend::Llvm],
    doc: "map_remove(map, key) — true if a key was actually removed.",
},
BuiltinSpec {
    names: &["map_len"],
    params: || vec![HType::Any],
    ret: || HType::Int,
    c_symbol: Some("hsh_map_len"),
    backends: &[Backend::Llvm],
    doc: "map_len(map) — number of live entries.",
},
BuiltinSpec {
    names: &["map_keys"],
    params: || vec![HType::Any],
    ret: || HType::Array(Box::new(HType::Any)),
    c_symbol: Some("hsh_map_keys"),
    backends: &[Backend::Llvm],
    doc: "map_keys(map) — array of keys, unspecified order (bucket order).",
},
BuiltinSpec {
    names: &["map_clear"],
    params: || vec![HType::Any],
    ret: || HType::Void,
    c_symbol: Some("hsh_map_clear"),
    backends: &[Backend::Llvm],
    doc: "map_clear(map) — removes all entries, keeps the table allocated.",
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
