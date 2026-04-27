//! H# Core Modules — built into the compiler, always available.
//! use "core -> runtime" from "rt"
//! use "core -> mem"     from "mem"
//! use "core -> types"   from "types"
//! use "core -> io"      from "io"
//! use "core -> panic"   from "panic"

pub mod runtime;
pub mod mem;
pub mod types;
pub mod io;

/// Check if a module name is a core module (not file-based)
pub fn is_core_module(path: &[String]) -> bool {
    matches!(
        path.first().map(|s| s.as_str()),
        Some("runtime") | Some("mem") | Some("memory") |
        Some("types")   | Some("type") |
        Some("io")      | Some("panic") | Some("alloc") |
        Some("intrinsics") | Some("ops") | Some("cmp") |
        Some("convert")    | Some("fmt") | Some("option") |
        Some("result")     | Some("iter") | Some("clone")
    )
}

/// Get the builtin functions exported by a core module
pub fn core_module_fns(path: &[String]) -> &'static [&'static str] {
    match path.first().map(|s| s.as_str()) {
        Some("runtime") => RUNTIME_FNS,
        Some("mem") | Some("memory") => MEM_FNS,
        Some("types") | Some("type") => TYPES_FNS,
        Some("io") => IO_FNS,
        Some("panic") => PANIC_FNS,
        _ => &[],
    }
}

static RUNTIME_FNS: &[&str] = &[
    "spawn", "sleep_ms", "now_unix", "now_ms", "getpid", "hostname",
    "shell", "exit", "abort", "env_get", "env_set",
    "gc_collect", "gc_stats", "arena_new", "arena_free",
];

static MEM_FNS: &[&str] = &[
    "alloc", "free", "realloc", "copy", "set",
    "size_of", "align_of", "null_ptr", "is_null",
    "ptr_add", "ptr_sub", "ptr_read", "ptr_write",
];

static TYPES_FNS: &[&str] = &[
    "type_of", "type_name", "size_of", "align_of",
    "is_int", "is_float", "is_string", "is_bool", "is_nil",
    "to_int", "to_float", "to_string", "to_bool",
    "parse_int", "parse_float",
];

static IO_FNS: &[&str] = &[
    "write", "writeln", "read_line", "read_char",
    "write_stderr", "write_stdout",
    "open_file", "close_file", "read_bytes", "write_bytes",
    "stdin_fd", "stdout_fd", "stderr_fd",
];

static PANIC_FNS: &[&str] = &[
    "panic", "assert", "assert_eq", "assert_ne",
    "unreachable", "todo", "unimplemented",
];
