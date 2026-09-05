mod items;
mod expr;
mod match_check;

use hsharp_parser::ast::*;
use hsharp_parser::span::Span;
use std::collections::HashMap;
use crate::diagnostics::Diagnostic;
use crate::htype::HType;

#[derive(Debug, Clone)]
#[allow(dead_code)]
struct VarInfo { ty: HType, mutable: bool }

#[derive(Debug, Clone)]
#[allow(dead_code)]
struct FnSig { params: Vec<HType>, return_type: HType }

pub struct TypeChecker {
    pub derived_impls:    HashMap<String, (String, String)>,
    pub deprecated_items: HashMap<String, String>,
    pub cfg_disabled_fns: HashMap<String, String>,
    pub test_fns:         Vec<String>,
    pub inline_fns:       std::collections::HashSet<String>,
    pub must_use_fns:     std::collections::HashSet<String>,
    scopes:  Vec<HashMap<String, VarInfo>>,
    fns:     HashMap<String, FnSig>,
    structs: HashMap<String, Vec<(String, HType)>>,
    /// enum name -> list of variant names (for §3 match exhaustiveness)
    enums: HashMap<String, Vec<String>>,
    /// top-level `const`/`pub let` bindings: name -> declared/inferred type,
    /// so `Expr::Ident` resolution finds them the same way it finds locals
    /// (see the `Expr::Ident` arm in `infer_expr`, which checks `lookup`
    /// then falls through here before giving up to the lenient `HType::Any`).
    consts: HashMap<String, HType>,
    current_fn_return: Option<HType>,
    diagnostics: Vec<Diagnostic>,
}


impl TypeChecker {
    pub fn new() -> Self {
        let mut tc = Self {
            scopes:            vec![HashMap::new()],
            fns:               HashMap::new(),
            structs:           HashMap::new(),
            enums:             HashMap::new(),
            consts:            HashMap::new(),
            current_fn_return: None,
            diagnostics:       Vec::new(),
            derived_impls:     HashMap::new(),
            deprecated_items:  HashMap::new(),
            cfg_disabled_fns:  HashMap::new(),
            test_fns:          Vec::new(),
            inline_fns:        std::collections::HashSet::new(),
            must_use_fns:      std::collections::HashSet::new(),
        };
        tc.register_builtins();
        tc
    }

    fn register_builtins(&mut self) {
        let any  = HType::Any;
        let str_ = HType::Str;
        let int  = HType::Int;
        let bool_= HType::Bool;
        let void = HType::Void;
        let f64_ = HType::F64;

        macro_rules! builtin {
            ($name:expr, [$($p:expr),*] => $r:expr) => {
                self.fns.insert($name.into(), FnSig {
                    params: vec![$($p.clone()),*],
                                return_type: $r.clone(),
                });
            };
        }

        // Core I/O
        builtin!("print",    [any]       => void);
        builtin!("println",  [any]       => void);
        builtin!("write",    [any]       => void);
        builtin!("writeln",  [any]       => void);

        // String
        builtin!("to_string",   [any]        => str_);
        builtin!("to_int",      [any]        => int);
        builtin!("parse_int",   [str_]       => HType::Optional(Box::new(int.clone())));
        builtin!("len",         [any]        => int);
        builtin!("trim",        [str_]       => str_);
        builtin!("to_upper",    [str_]       => str_);
        builtin!("upper",       [str_]       => str_);
        builtin!("to_lower",    [str_]       => str_);
        builtin!("lower",       [str_]       => str_);
        builtin!("contains",    [str_, str_] => bool_);
        builtin!("starts_with", [str_, str_] => bool_);
        builtin!("ends_with",   [str_, str_] => bool_);
        builtin!("replace",     [str_, str_, str_] => str_);
        builtin!("str_replace", [str_, str_, str_] => str_);
        builtin!("split",       [str_, str_] => HType::Array(Box::new(str_.clone())));
        builtin!("str_count",   [any]        => int);

        // Control flow / process
        builtin!("exit",   [int]   => void);
        builtin!("panic",  [str_]  => void);
        builtin!("assert", [bool_, str_] => void);

        // System
        builtin!("shell",       [str_]       => str_);
        builtin!("cmd",         [str_]       => str_);
        // SECURITY: prefer these over shell() when arguments may contain
        // untrusted data — see runtime.rs for full rationale.
        builtin!("shell_escape", [str_] => str_);
        builtin!("shquote",      [str_] => str_); // alias
        // exec(cmd[, a1[, a2[, a3]]]) -> string — direct fork+execve, no
        // shell. Codegen resolves to hsh_exec1..4 based on call arg count
        // (1-4 args); the typechecker only needs a permissive entry here.
        builtin!("exec", [str_, str_, str_, str_] => str_);
        // extern [python, "mod"] bridge (phase 1: subprocess, no shell)
        builtin!("py_eval", [str_] => str_);
        builtin!("getpid",      []           => int);
        builtin!("pid",         []           => int);
        builtin!("hostname",    []           => str_);
        builtin!("sleep_ms",    [int]        => void);

        // Time
        builtin!("now_unix",  [] => int);
        builtin!("now_ms",    [] => int);
        builtin!("time_unix", [] => int);
        builtin!("time_ms",   [] => int);

        // Random / crypto
        builtin!("random_hex",    [int]       => str_);
        builtin!("random_int",    [int, int]  => int);
        builtin!("random_string", [int]       => str_);
        builtin!("new_uuid",      []          => str_);
        builtin!("sha256",        [str_]      => str_);
        builtin!("md5",           [str_]      => str_);
        builtin!("xor_hex",       [str_, str_] => str_);

        // Filesystem
        builtin!("fs_read",        [str_]       => str_);
        builtin!("read_file",      [str_]       => str_);
        builtin!("fs_write",       [str_, str_] => void);
        builtin!("write_file",     [str_, str_] => void);
        builtin!("fs_exists",      [str_]       => bool_);
        builtin!("file_exists",    [str_]       => bool_);
        builtin!("fs_mkdir_all",   [str_]       => void);
        builtin!("mkdir_all",      [str_]       => void);
        builtin!("file_size_bytes",[str_]       => int);
        builtin!("is_dir",         [str_]       => bool_);
        builtin!("file_stem",      [str_]       => str_);
        builtin!("file_ext",       [str_]       => str_);
        builtin!("file_parent",    [str_]       => str_);

        // Network
        builtin!("scan_port_net", [str_, int, int] => bool_);
        builtin!("dns_resolve",   [str_]           => str_);
        builtin!("http_get",      [str_]           => str_);

        // ANSI formatting
        builtin!("bold",         [str_] => str_);
        builtin!("green_text",   [str_] => str_);
        builtin!("green",        [str_] => str_);
        builtin!("red_text",     [str_] => str_);
        builtin!("red",          [str_] => str_);
        builtin!("yellow_text",  [str_] => str_);
        builtin!("yellow",       [str_] => str_);
        builtin!("dim_text",     [str_] => str_);
        builtin!("dim",          [str_] => str_);
        builtin!("cyan_text",    [str_] => str_);
        builtin!("cyan",         [str_] => str_);

        // Math
        builtin!("sin",   [f64_] => f64_);
        builtin!("cos",   [f64_] => f64_);
        builtin!("sqrt",  [f64_] => f64_);
        builtin!("abs",   [f64_] => f64_);
        builtin!("floor", [f64_] => f64_);
        builtin!("ceil",  [f64_] => f64_);
        builtin!("pow",   [f64_, f64_] => f64_);

        // DB / regex / misc
        builtin!("re_match",      [str_, str_] => bool_);
        builtin!("re_find",       [str_, str_] => str_);
        builtin!("re_find_all",   [str_, str_] => str_);
        builtin!("re_replace",    [str_, str_, str_] => str_);
        builtin!("regex_match",   [str_, str_] => bool_);
        builtin!("regex_find",    [str_, str_] => str_);
        builtin!("regex_replace", [str_, str_, str_] => str_);
        builtin!("sqlite_open",   [str_] => str_);
        builtin!("sqlite_exec",   [str_, str_] => str_);
        builtin!("sqlite_query",  [str_, str_] => str_);
        // §12: parameterized queries — SQL injection-safe binds.
        // db_query_bind(db, sql, b1[, b2[, b3]]) -> csv rows. Codegen
        // resolves to hsh_sqlite_query_bind1/2/3 based on arity (3-5 args).
        builtin!("db_query_bind", [str_, str_, str_, str_, str_] => str_);
        builtin!("sqlite_close",  [str_] => void);
        builtin!("json_parse",    [str_] => any);
        builtin!("json_get_str",  [any, str_] => str_);

        // v0.7 extras
        builtin!("new_cli_parser", [str_, str_] => any);
        builtin!("str_trim",       [str_]       => str_);
        builtin!("str_contains",   [str_, str_] => bool_);
        builtin!("str_starts_with",[str_, str_] => bool_);
        builtin!("str_ends_with",  [str_, str_] => bool_);
        builtin!("hsh_now_unix",   []           => int);
        builtin!("hsh_now_ms",     []           => int);

        // `@pointers` basic v2 raw memory builtins (see codegen.rs/core.c's
        // hsh_ptr_{read,write}_*) and `@arc` basic v2 atomic refcounting
        // builtins (see hsh_rc_*). Registering these here just gives
        // `infer_expr` a real return type for them instead of falling back
        // to `Any` — actual *reachability* enforcement (only usable from a
        // `@pointers`/`@arc` function or an `unsafe ... end` block) is a
        // separate pass, §13 below (`check_mem_mode_block` and friends).
        builtin!("ptr_read_i64",  [any, int] => int);
        builtin!("ptr_write_i64", [any, int, int] => void);
        builtin!("ptr_read_i32",  [any, int] => int);
        builtin!("ptr_write_i32", [any, int, int] => void);
        builtin!("ptr_read_i16",  [any, int] => int);
        builtin!("ptr_write_i16", [any, int, int] => void);
        builtin!("ptr_read_i8",   [any, int] => int);
        builtin!("ptr_write_i8",  [any, int, int] => void);
        builtin!("ptr_read_f64",  [any, int] => f64_);
        builtin!("ptr_write_f64", [any, int, f64_] => void);
        builtin!("ptr_read_f32",  [any, int] => f64_);
        builtin!("ptr_write_f32", [any, int, f64_] => void);
        builtin!("ptr_read_ptr",  [any, int] => any);
        builtin!("ptr_write_ptr", [any, int, any] => void);
        builtin!("ptr_add",       [any, int] => any);
        builtin!("ptr_is_null",   [any] => bool_);
        builtin!("ptr_alloc_size", [any] => int);
        builtin!("ptr_copy",      [any, any, int] => void);
        builtin!("ptr_compare",   [any, any, int] => int);
        builtin!("ptr_field_offset", [any, str_] => int);
        builtin!("ptr_read_checked",  [any, int, int] => int);
        builtin!("ptr_write_checked", [any, int, int, int] => void);
        builtin!("ptr_fill", [any, int, int] => void);
        builtin!("ptr_zero", [any, int] => void);
        builtin!("arc_alloc",   [int] => any);
        builtin!("arc_retain",  [any] => void);
        builtin!("arc_release", [any] => void);
        builtin!("arc_count",   [any] => int);
        builtin!("arc_downgrade",    [any] => any);
        builtin!("arc_upgrade",      [any] => any);
        builtin!("arc_weak_release", [any] => void);
        builtin!("arc_weak_count",   [any] => int);
        builtin!("arena_checkpoint", [] => int);
        builtin!("arena_rewind",     [int] => void);
        builtin!("arena_used",       [] => int);
        builtin!("arena_capacity",   [] => int);

        // ── Round-4 addition: every builtin the interpreter (call.rs) and
        // LLVM backend (codegen.rs/runtime/core.c) actually implement but
        // that had no entry here at all — meaning every call to one of
        // these silently typechecked as `any` (the checker's default for
        // an unrecognized function name), which is what caused
        // `exec_in_container_with_output`'s `-> (string, bool)` to
        // mismatch as `(any, bool)` once its body called `string_trim`.
        // Signatures below are taken directly from each function's real
        // implementation in interpreter/src/call.rs.
        let str_arr = HType::Array(Box::new(str_.clone()));
        let any_arr = HType::Array(Box::new(any.clone()));
        let int_opt = HType::Optional(Box::new(int.clone()));

        // strings
        builtin!("string_len",          [str_] => int);
        builtin!("string_at",           [str_, int] => str_);
        builtin!("string_chars",        [str_] => str_arr);
        builtin!("string_contains",     [str_, str_] => bool_);
        builtin!("string_contains_str", [str_, str_] => bool_);
        builtin!("string_starts_with",  [str_, str_] => bool_);
        builtin!("string_ends_with",    [str_, str_] => bool_);
        builtin!("string_find",         [str_, str_] => int);
        builtin!("string_rfind",        [str_, str_] => int);
        builtin!("string_lower",        [str_] => str_);
        builtin!("string_to_lower",     [str_] => str_);
        builtin!("string_upper",        [str_] => str_);
        builtin!("string_to_upper",     [str_] => str_);
        builtin!("string_trim",         [str_] => str_);
        builtin!("string_trim_right",   [str_] => str_);
        builtin!("string_pad_right",    [str_, int] => str_);
        builtin!("string_repeat",       [str_, int] => str_);
        builtin!("string_replace",      [str_, str_, str_] => str_);
        builtin!("string_replace_all",  [str_, str_, str_] => str_);
        builtin!("string_split",        [str_, str_] => str_arr);
        builtin!("string_slice",        [str_, int, int] => str_);
        builtin!("string_to_bytes",     [str_] => str_);
        builtin!("str_split",           [str_, str_] => str_arr);
        builtin!("str_join",            [any_arr, str_] => str_);

        // arrays (generic containers — element type is necessarily `any`,
        // since this simple builtin table has no generics; every caller
        // in this codebase that needs a concrete element type gets one by
        // annotating the `let` it assigns the result to, same as any
        // other `any`-returning builtin such as `json_get_obj`)
        builtin!("array_len",      [any_arr] => int);
        builtin!("array_count",    [any_arr] => int);
        builtin!("array_push",     [any_arr, any] => any_arr);
        builtin!("array_pop",      [any_arr] => any_arr);
        builtin!("array_get",      [any_arr, int] => any);
        builtin!("array_set",      [any_arr, int, any] => any_arr);
        builtin!("array_remove",   [any_arr, int] => any_arr);
        builtin!("array_contains", [any_arr, any] => bool_);
        builtin!("array_concat",   [any_arr, any_arr] => any_arr);

        // filesystem / env / path
        builtin!("fs_remove",    [str_] => void);
        builtin!("fs_append",    [str_, str_] => void);
        builtin!("fs_is_dir",    [str_] => bool_);
        builtin!("fs_is_file",   [str_] => bool_);
        builtin!("fs_rmdir",     [str_] => void);
        builtin!("fs_rmdir_all", [str_] => void);
        builtin!("fs_read_lines",[str_] => str_arr);
        builtin!("fs_size",      [str_] => int);
        builtin!("fs_copy",      [str_, str_] => void);
        builtin!("fs_rename",    [str_, str_] => void);
        builtin!("fs_cwd",       [] => str_);
        builtin!("fs_chdir",     [str_] => int);
        builtin!("fs_list_dir",  [str_] => str_arr);
        builtin!("path_join",      [str_, str_] => str_);
        builtin!("path_stem",      [str_] => str_);
        builtin!("path_extension", [str_] => str_);
        builtin!("path_parent",    [str_] => str_);
        builtin!("env_temp_dir", [] => str_);
        builtin!("env_get",      [str_] => str_);
        builtin!("env_args",     [] => str_arr);
        builtin!("env_home",     [] => str_);

        // math
        builtin!("math_sin",   [f64_] => f64_);
        builtin!("math_cos",   [f64_] => f64_);
        builtin!("math_tan",   [f64_] => f64_);
        builtin!("math_asin",  [f64_] => f64_);
        builtin!("math_acos",  [f64_] => f64_);
        builtin!("math_atan",  [f64_] => f64_);
        builtin!("math_atan2", [f64_, f64_] => f64_);
        builtin!("math_sqrt",  [f64_] => f64_);
        builtin!("math_pow",   [f64_, f64_] => f64_);
        builtin!("math_floor", [f64_] => f64_);
        builtin!("math_ceil",  [f64_] => f64_);
        builtin!("math_round", [f64_] => f64_);
        builtin!("math_trunc", [f64_] => f64_);
        builtin!("math_log",   [f64_] => f64_);
        builtin!("math_log2",  [f64_] => f64_);
        builtin!("math_log10", [f64_] => f64_);
        builtin!("math_exp",   [f64_] => f64_);
        builtin!("math_abs",   [any] => any);   // Int(n) -> Int, Float(f) -> Float
        builtin!("math_fabs",  [f64_] => f64_);
        builtin!("math_ipow",  [int, int] => int);
        builtin!("math_min",   [any, any] => any);
        builtin!("math_max",   [any, any] => any);
        builtin!("math_fmin",  [f64_, f64_] => f64_);
        builtin!("math_fmax",  [f64_, f64_] => f64_);
        builtin!("math_clamp", [int, int, int] => int);
        builtin!("math_fclamp",[f64_, f64_, f64_] => f64_);
        builtin!("math_gcd",   [int, int] => int);
        builtin!("math_lcm",   [int, int] => int);
        builtin!("math_pi",  [] => f64_);
        builtin!("math_e",   [] => f64_);
        builtin!("math_tau", [] => f64_);

        // hashing / encoding
        builtin!("hex_encode",   [str_] => str_);
        builtin!("hex_decode",   [str_] => str_);
        builtin!("sha1",         [str_] => str_);
        builtin!("sha512",       [str_] => str_);
        builtin!("hmac_sha256",  [str_, str_] => str_);
        builtin!("hmac_sha512",  [str_, str_] => str_);
        builtin!("rot13",        [str_] => str_);
        builtin!("conv_str_to_int", [str_] => int);
        builtin!("conv_int_to_hex", [int] => str_);
        builtin!("conv_to_bytes",   [str_] => str_);

        // sorting / search
        builtin!("sort_ints",         [any_arr] => any_arr);
        builtin!("sort_strings",      [str_arr] => str_arr);
        builtin!("binary_search",     [any_arr, int] => int);
        builtin!("binary_search_left",[any_arr, int] => int);
        builtin!("min_int",           [any_arr] => int_opt);
        builtin!("max_int",           [any_arr] => int_opt);
        builtin!("merge_sorted",      [any_arr, any_arr] => any_arr);

        // assertions (test framework)
        builtin!("assert_eq",          [any, any] => void);
        builtin!("assert_ne",          [any, any] => void);
        builtin!("assert_true",        [bool_] => void);
        builtin!("assert_false",       [bool_] => void);
        builtin!("assert_nil",         [any] => void);
        builtin!("assert_not_nil",     [any] => void);
        builtin!("assert_err",         [any] => void);
        builtin!("assert_approx",      [f64_, f64_, f64_] => void);
        builtin!("assert_contains",    [str_, str_] => void);
        builtin!("assert_starts_with", [str_, str_] => void);
        builtin!("assert_len",         [any_arr, int] => void);
        builtin!("fail", [str_] => void);
        builtin!("skip", [] => void);

        // misc / system
        builtin!("module_info",   [] => str_);
        builtin!("heap_size",     [] => int);
        builtin!("memory_usage",  [] => int);
        builtin!("scan_port",     [str_, int, int] => bool_);

        // JSON (dynamically-typed by nature — `any` return is correct,
        // not a placeholder, for the value-returning entries; the
        // `_str`/`_int`/`_float`/`_bool` accessors DO have concrete
        // return types and get them)
        builtin!("json_parse_array",      [str_] => any_arr);
        builtin!("json_stringify",        [any] => str_);
        builtin!("json_stringify_pretty", [any] => str_);
        builtin!("json_empty_object",     [] => any);
        builtin!("json_get_int",   [any, str_] => int);
        builtin!("json_get_float", [any, str_] => f64_);
        builtin!("json_get_bool",  [any, str_] => bool_);
        builtin!("json_get_obj",   [any, str_] => any);
        builtin!("json_get_arr",   [any, str_] => any_arr);
        builtin!("json_has_key",   [any, str_] => bool_);
        builtin!("json_is_null",   [any] => bool_);
        builtin!("json_set",       [any, str_, any] => any);
        builtin!("json_as_int",    [any] => int);
        builtin!("json_as_str",    [any] => str_);
        builtin!("json_object",    [] => any);
        builtin!("json_int_at",    [any_arr, int] => int);
        builtin!("json_obj_at",    [any_arr, int] => any);
        builtin!("json_query",     [any, str_] => any);

        // iterator / higher-order array ops (closures make the element
        // and callback types inherently untypeable in this table — same
        // `any`-in-`any`-out rationale as the plain `array_*` family)
        builtin!("iter_map",     [any_arr, any] => any_arr);
        builtin!("iter_filter",  [any_arr, any] => any_arr);
        builtin!("iter_reduce",  [any_arr, any, any] => any);
        builtin!("iter_zip",     [any_arr, any_arr] => any_arr);
        builtin!("iter_chain",   [any_arr, any_arr] => any_arr);
        builtin!("iter_take",    [any_arr, int] => any_arr);
        builtin!("iter_skip",    [any_arr, int] => any_arr);
        builtin!("iter_any",     [any_arr, any] => bool_);
        builtin!("iter_all",     [any_arr, any] => bool_);
        builtin!("iter_sum",     [any_arr] => any);
        builtin!("iter_product", [any_arr] => any);
        builtin!("iter_reverse", [any_arr] => any_arr);
        builtin!("iter_join",    [any_arr, str_] => str_);
        builtin!("iter_repeat",  [any, int] => any_arr);
        builtin!("iter_unique",  [any_arr] => any_arr);

        // HashMap / HashSet / Queue / Stack — each backed by an internal
        // dynamic `Value::Struct{name:"__hashmap"|...}` with no fixed,
        // declared field list the checker could know about, so `any` is
        // the only honest return type for the container itself; the
        // accessor functions DO have concrete types where the underlying
        // implementation guarantees one (len -> int, contains -> bool).
        builtin!("hashmap_new",      [] => any);
        builtin!("hashmap_insert",   [any, any, any] => any);
        builtin!("hashmap_get",      [any, any] => any);
        builtin!("hashmap_contains", [any, any] => bool_);
        builtin!("hashmap_remove",   [any, any] => any);
        builtin!("hashmap_len",      [any] => int);
        builtin!("hashmap_keys",     [any] => str_arr);
        builtin!("hashmap_values",   [any] => any_arr);
        builtin!("hashset_new",       [] => any);
        builtin!("hashset_insert",    [any, any] => any);
        builtin!("hashset_contains",  [any, any] => bool_);
        builtin!("hashset_remove",    [any, any] => any);
        builtin!("hashset_len",       [any] => int);
        builtin!("hashset_to_array",  [any] => any_arr);
        builtin!("queue_new", [] => any);
        builtin!("stack_new", [] => any);

        // regex "text-argument-order" aliases (re_*_ta takes (text,
        // pattern) instead of re_*'s (pattern, text) — same underlying
        // return shape as the re_* function each delegates to)
        builtin!("re_match_ta",       [str_, str_] => bool_);
        builtin!("re_find_ta",        [str_, str_] => str_);
        builtin!("re_find_all_ta",    [str_, str_] => str_arr);
        builtin!("re_replace_ta",     [str_, str_, str_] => str_);
        builtin!("re_replace_all_ta", [str_, str_, str_] => str_);
        builtin!("re_split_ta",       [str_, str_] => str_arr);
        builtin!("regex_find_all",    [str_, str_] => str_arr);

        // SQLite (v0.6) — handles/results are string-based for
        // portability (see call.rs's own comment on `db_open`), so every
        // signature here is concrete, not a placeholder.
        builtin!("db_open",  [str_] => str_);
        builtin!("db_exec",  [str_, str_] => str_);
        builtin!("db_query", [str_, str_] => any_arr);
        builtin!("db_close", [str_] => void);

        // async / profiler
        builtin!("async_spawn",   [any] => any);
        builtin!("async_timeout", [any, int] => any);
        builtin!("prof_start",    [str_] => int);
        builtin!("profile_start", [str_] => int);
        builtin!("prof_end",      [str_] => str_);
        builtin!("profile_end",   [str_] => str_);
        builtin!("prof_report",   [] => str_);
    }

    /// Type-check the module, returning ALL diagnostics found (both errors
    /// and warnings). An empty result means the module passed.
    ///
    /// CALLER CONTRACT (for `hsharp build` / `bytes build`):
    ///   let diags = checker.check_module(&module);
    ///   if !diags.is_empty() {
    ///       print_diagnostics(&diags, &source, &file);
    ///   }
    ///   let has_errors = diags.iter().any(|d| d.severity == Severity::Error);
    ///   if has_errors { /* abort build */ }
    ///
    /// This replaces the old `Result<(), TypeError>` API (which only ever
    /// surfaced the *first* problem, and with no span — the root cause of
    /// the unhelpful `✗ type check failed [8s]` message).
    pub fn check_module(&mut self, module: &Module) -> Vec<Diagnostic> {
        // `std -> lib` resolution is now MANDATORY, not an optional warning.
        // There is no more "built-in fallback" — every `std ->` capability
        // has to come from a real /usr/lib/HackerOS/H#/std/{lib}.h# file
        // (see hsharp-interpreter's `helpers.rs` module doc comment for
        // the full rationale: `std` used to have a second, hidden
        // implementation embedded straight into this compiler/interpreter,
        // which this whole mechanism replaces). A missing file is now a
        // hard compile error with an actionable install hint, checked
        // unconditionally — not just when `/usr/lib/HackerOS` happens to
        // already exist, since that guard is exactly what let this slide
        // by silently on any machine that hadn't set up the full HackerOS
        // layout yet.
        for (import_kind, _alias, span) in &module.imports {
            if let ImportKind::Std { path, .. } = import_kind {
                let lib = path.last().cloned().unwrap_or_default();
                let std_path = format!("/usr/lib/HackerOS/H#/std/{}.h#", lib);
                if !std::path::Path::new(&std_path).exists() {
                    self.diagnostics.push(
                        Diagnostic::error(
                            span.clone(),
                            format!(
                                "std module `{lib}` not found at {std_path}\n\n\
please install h# utils for HackerOS use:\n\
  linux:   hacker unpack h#-utils\n\
  windows: (not available yet — no install path is defined for Windows yet)\n",
                                lib = lib, std_path = std_path,
                            ),
                        )
                    );
                }
            }
        }

        // Pass 1: collect fn/struct/enum signatures (needed for forward
        // references and for §3 checks below: struct field lookup, enum
        // variant lookup for match exhaustiveness).
        for item in &module.items { self.collect_signatures(item); }

        // Pass 2: check bodies
        for item in &module.items { self.check_item(item); }

        std::mem::take(&mut self.diagnostics)
    }

    /// Push an error diagnostic.
    #[allow(dead_code)]
    fn err(&mut self, span: Span, message: impl Into<String>) {
        self.diagnostics.push(Diagnostic::error(span, message));
    }

    /// Push an error diagnostic with a fix-it hint.
    pub(super) fn err_hint(&mut self, span: Span, message: impl Into<String>, hint: impl Into<String>) {
        self.diagnostics.push(Diagnostic::error(span, message).with_hint(hint));
    }

    /// Push a warning diagnostic.
    #[allow(dead_code)]
    fn warn(&mut self, span: Span, message: impl Into<String>) {
        self.diagnostics.push(Diagnostic::warning(span, message));
    }

    fn collect_signatures(&mut self, item: &Item) {
        match item {
            Item::FnDef(f) => {
                let params = f.params.iter().map(|p| HType::from_type_expr(&p.ty)).collect();
                let ret    = f.return_type.as_ref().map(HType::from_type_expr).unwrap_or(HType::Void);
                self.fns.insert(f.name.clone(), FnSig { params, return_type: ret });
            }
            Item::StructDef(s) => {
                let fields = s.fields.iter()
                .map(|f| (f.name.clone(), HType::from_type_expr(&f.ty)))
                .collect();
                self.structs.insert(s.name.clone(), fields);
            }
            Item::EnumDef(e) => {
                let variants = e.variants.iter().map(|v| v.name.clone()).collect();
                self.enums.insert(e.name.clone(), variants);
            }
            Item::ImplBlock(imp) => {
                for method in &imp.methods {
                    let full_name = format!("{}_{}", imp.type_name, method.name);
                    let params = method.params.iter()
                    .filter(|p| p.name != "self")
                    .map(|p| HType::from_type_expr(&p.ty))
                    .collect();
                    let ret = method.return_type.as_ref().map(HType::from_type_expr).unwrap_or(HType::Void);
                    self.fns.insert(full_name, FnSig { params, return_type: ret });
                }
            }
            Item::ModDecl { name, inline: Some(items), .. } => {
                self.collect_mod_signatures(name, items);
            }
            Item::ConstDef { name, ty, value, .. } => {
                let inferred = ty.as_ref().map(HType::from_type_expr).unwrap_or_else(|| self.infer_expr(value));
                self.consts.insert(name.clone(), inferred);
            }
            _ => {}
        }
    }

    /// Recursively collect signatures from an inline module's items,
    /// registering each fn under both its namespaced path
    /// (`mod_name::fn_name`, for `module::fn(...)` call sites) and its
    /// bare name (so sibling functions inside the module can call each
    /// other without the prefix — mirrors the interpreter's behavior in
    /// `register_mod_items`).
    fn collect_mod_signatures(&mut self, mod_name: &str, items: &[Item]) {
        for item in items {
            match item {
                Item::FnDef(f) => {
                    let params = f.params.iter().map(|p| HType::from_type_expr(&p.ty)).collect::<Vec<_>>();
                    let ret    = f.return_type.as_ref().map(HType::from_type_expr).unwrap_or(HType::Void);
                    let namespaced = format!("{}::{}", mod_name, f.name);
                    self.fns.insert(namespaced, FnSig { params: params.clone(), return_type: ret.clone() });
                    self.fns.insert(f.name.clone(), FnSig { params, return_type: ret });
                }
                Item::StructDef(s) => {
                    let fields = s.fields.iter()
                        .map(|f| (f.name.clone(), HType::from_type_expr(&f.ty)))
                        .collect();
                    self.structs.insert(s.name.clone(), fields);
                }
                Item::ModDecl { name: sub_name, inline: Some(sub_items), .. } => {
                    let nested = format!("{}::{}", mod_name, sub_name);
                    self.collect_mod_signatures(&nested, sub_items);
                }
                Item::ConstDef { name, ty, value, .. } => {
                    let inferred = ty.as_ref().map(HType::from_type_expr).unwrap_or_else(|| self.infer_expr(value));
                    self.consts.insert(name.clone(), inferred);
                }
                _ => {}
            }
        }
    }

}
