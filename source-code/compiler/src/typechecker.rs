use hsharp_parser::ast::*;
use hsharp_parser::span::Span;
use std::collections::HashMap;

// ── §1: Diagnostics — full errors with location, matching hhc's format ─────

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Severity {
    Error,
    Warning,
}

/// A single type-checker diagnostic: a message tied to a source location,
/// with optional fix-it hints. `check_module` now collects ALL of these
/// (instead of bailing on the first error) and returns them to the caller,
/// who renders them with `print_diagnostics` — producing the same
/// `-- TYPE ERROR (file) -------` / `--> file:line:col` format that `hhc`
/// already prints for syntax errors. This is the fix for the
/// `✗ type check failed [8s]`-with-no-detail problem: `hsharp build` should
/// call `print_diagnostics(&diags, &source, &file)` for every diagnostic
/// before reporting overall pass/fail.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub severity: Severity,
    pub span:     Span,
    pub message:  String,
    pub hints:    Vec<String>,
}

impl Diagnostic {
    pub fn error(span: Span, message: impl Into<String>) -> Self {
        Self { severity: Severity::Error, span, message: message.into(), hints: Vec::new() }
    }
    pub fn warning(span: Span, message: impl Into<String>) -> Self {
        Self { severity: Severity::Warning, span, message: message.into(), hints: Vec::new() }
    }
    pub fn with_hint(mut self, hint: impl Into<String>) -> Self {
        self.hints.push(hint.into());
        self
    }
}

/// Render diagnostics in the same visual format as `hhc`'s parse errors:
///
/// ```text
/// -- TYPE ERROR (src/main.h#) -------
/// --> src/main.h#:47:12
///
///   46 |     let x: int
///   47 |     let x: int = "hello"
///                          ^^^^^^^
///   48 | end
///
/// Error: type mismatch: expected `int`, found `string`
///
///   Hint: convert with to_string()/to_int(), or fix the declared type
/// ```
///
/// `source` is the full text of `file` (read by the caller — this function
/// does no I/O so it works the same whether the source came from disk, a
/// REPL buffer, or an in-memory test fixture).
pub fn print_diagnostics(diags: &[Diagnostic], source: &str, file: &str) {
    let lines: Vec<&str> = source.lines().collect();

    for diag in diags {
        let kind = match diag.severity {
            Severity::Error   => "TYPE ERROR",
            Severity::Warning => "WARNING",
        };
        let label = match diag.severity {
            Severity::Error   => "Error",
            Severity::Warning => "Warning",
        };

        println!("-- {} ({}) -------", kind, file);
        println!("--> {}:{}:{}", file, diag.span.start.line, diag.span.start.col);
        println!();

        let line_no   = diag.span.start.line;
        let col       = diag.span.start.col;
        let width     = (diag.span.end.col.max(col + 1)).saturating_sub(col).max(1);
        let gutter_w  = line_no.to_string().len().max(
            (line_no + 1).to_string().len()
        ) + 1;

        // Line before (context), if any
        if line_no >= 2 {
            if let Some(prev) = lines.get(line_no - 2) {
                println!("  {:>width$} | {}", line_no - 1, prev, width = gutter_w);
            }
        }
        // The offending line itself
        if let Some(this_line) = lines.get(line_no - 1) {
            println!("  {:>width$} | {}", line_no, this_line, width = gutter_w);
        }
        // Caret underline
        let pad = " ".repeat(gutter_w + 3 + col.saturating_sub(1));
        println!("{}{}", pad, "^".repeat(width));
        // Line after (context), if any
        if let Some(next) = lines.get(line_no) {
            println!("  {:>width$} | {}", line_no + 1, next, width = gutter_w);
        }
        println!();

        println!("{}: {}", label, diag.message);
        for hint in &diag.hints {
            println!();
            println!("  Hint: {}", hint);
        }
        println!();
    }

    let errs = diags.iter().filter(|d| d.severity == Severity::Error).count();
    let warns = diags.iter().filter(|d| d.severity == Severity::Warning).count();
    if errs > 0 {
        println!("error: {} error(s), {} warning(s)", errs, warns);
    } else if warns > 0 {
        println!("warning: {} warning(s)", warns);
    }
}


/// Legacy error type, kept for backward compatibility with any external
/// code that still matches on it. `check_module` no longer constructs these
/// — use `Diagnostic` (above) instead, which carries a `Span`.
#[allow(dead_code)]
#[derive(Debug, Clone, thiserror::Error)]
pub enum TypeError {
    #[error("undefined variable `{0}`")]
    UndefinedVar(String),
    #[error("std library not found: {0}")]
    StdNotFound(String),
    #[error("type mismatch: expected `{expected}`, found `{found}`")]
    TypeMismatch { expected: String, found: String },
    #[error("undefined function `{0}`")]
    UndefinedFn(String),
    #[error("undefined type `{0}`")]
    UndefinedType(String),
    #[error("wrong number of arguments to `{name}`: expected {expected}, found {found}")]
    ArgCount { name: String, expected: usize, found: usize },
    #[error("cannot assign to immutable variable `{0}`")]
    ImmutableAssign(String),
    #[error("return type mismatch in `{fn_name}`: expected `{expected}`, found `{found}`")]
    ReturnMismatch { fn_name: String, expected: String, found: String },
}

#[derive(Debug, Clone, PartialEq)]
pub enum HType {
    Int, Uint,
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
    F32, F64,
    Bool, Str, Bytes, Void, Any,
    Optional(Box<HType>),
    Array(Box<HType>),
    Tuple(Vec<HType>),
    Named(String),
    Fn(Vec<HType>, Box<HType>),
    Ref(Box<HType>),
    RefMut(Box<HType>),
}

impl HType {
    pub fn from_type_expr(te: &TypeExpr) -> Self {
        match te {
            TypeExpr::Named(n) => match n.as_str() {
                "int"    => HType::Int,
                "uint"   => HType::Uint,
                "i8"     => HType::I8,  "i16"  => HType::I16,
                "i32"    => HType::I32, "i64"  => HType::I64,
                "i128"   => HType::I128,
                "u8"     => HType::U8,  "u16"  => HType::U16,
                "u32"    => HType::U32, "u64"  => HType::U64,
                "u128"   => HType::U128,
                "f32"    => HType::F32, "f64"  => HType::F64,
                "bool"   => HType::Bool,
                "string" => HType::Str,
                "bytes"  => HType::Bytes,
                "any"    => HType::Any,
                _        => HType::Named(n.clone()),
            },
            TypeExpr::Void        => HType::Void,
            TypeExpr::Optional(i) => HType::Optional(Box::new(Self::from_type_expr(i))),
            TypeExpr::Array(i)    => HType::Array(Box::new(Self::from_type_expr(i))),
            TypeExpr::Tuple(ts)   => HType::Tuple(ts.iter().map(Self::from_type_expr).collect()),
            TypeExpr::Ref(i)      => HType::Ref(Box::new(Self::from_type_expr(i))),
            TypeExpr::RefMut(i)   => HType::RefMut(Box::new(Self::from_type_expr(i))),
            TypeExpr::Fn(p, r)    => HType::Fn(p.iter().map(Self::from_type_expr).collect(), Box::new(Self::from_type_expr(r))),
            TypeExpr::Generic(n, _) => HType::Named(n.clone()),
            TypeExpr::Slice(i, _) => HType::Array(Box::new(Self::from_type_expr(i))),
            TypeExpr::I8   => HType::I8,   TypeExpr::I16  => HType::I16,
            TypeExpr::I32  => HType::I32,  TypeExpr::I64  => HType::I64,
            TypeExpr::I128 => HType::I128,
            TypeExpr::U8   => HType::U8,   TypeExpr::U16  => HType::U16,
            TypeExpr::U32  => HType::U32,  TypeExpr::U64  => HType::U64,
            TypeExpr::U128 => HType::U128,
            TypeExpr::F32  => HType::F32,  TypeExpr::F64  => HType::F64,
            TypeExpr::Bool   => HType::Bool,
            TypeExpr::String => HType::Str,
            TypeExpr::Bytes  => HType::Bytes,
        }
    }

    pub fn is_numeric(&self) -> bool {
        matches!(self,
                 HType::Int | HType::Uint |
                 HType::I8 | HType::I16 | HType::I32 | HType::I64 | HType::I128 |
                 HType::U8 | HType::U16 | HType::U32 | HType::U64 | HType::U128 |
                 HType::F32 | HType::F64)
    }

    pub fn compatible_with(&self, other: &HType) -> bool {
        if self == other { return true; }
        if matches!(self, HType::Any) || matches!(other, HType::Any) { return true; }
        if self.is_numeric() && other.is_numeric() { return true; }
        // `nil` infers as `any?` (Optional(Any)) — it's compatible with any
        // declared optional type, e.g. `int?`, `string?`, `MyStruct?`.
        // Likewise Optional(T) is compatible with Optional(U) if T and U are.
        if let (HType::Optional(a), HType::Optional(b)) = (self, other) {
            return a.compatible_with(b);
        }
        false
    }

    pub fn display(&self) -> String {
        match self {
            HType::Int    => "int".into(),
            HType::Uint   => "uint".into(),
            HType::I8     => "i8".into(),   HType::I16  => "i16".into(),
            HType::I32    => "i32".into(),  HType::I64  => "i64".into(),
            HType::I128   => "i128".into(),
            HType::U8     => "u8".into(),   HType::U16  => "u16".into(),
            HType::U32    => "u32".into(),  HType::U64  => "u64".into(),
            HType::U128   => "u128".into(),
            HType::F32    => "f32".into(),  HType::F64  => "f64".into(),
            HType::Bool   => "bool".into(),
            HType::Str    => "string".into(),
            HType::Bytes  => "bytes".into(),
            HType::Void   => "void".into(),
            HType::Any    => "any".into(),
            HType::Optional(i) => format!("{}?", i.display()),
            HType::Array(i)    => format!("[{}]", i.display()),
            HType::Tuple(ts)   => format!("({})", ts.iter().map(|t| t.display()).collect::<Vec<_>>().join(", ")),
            HType::Named(n)    => n.clone(),
            HType::Fn(p, r)    => format!("fn({}) -> {}", p.iter().map(|t| t.display()).collect::<Vec<_>>().join(", "), r.display()),
            HType::Ref(i)      => format!("&{}", i.display()),
            HType::RefMut(i)   => format!("&mut {}", i.display()),
        }
    }
}

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
        // v0.7: std library path check is OPTIONAL — only warn, don't block compilation.
        for (import_kind, _alias, span) in &module.imports {
            if let ImportKind::Std { path, .. } = import_kind {
                let lib = path.last().cloned().unwrap_or_default();
                let std_path = format!("/usr/lib/HackerOS/H#/std/{}.h#", lib);
                if std::path::Path::new("/usr/lib/HackerOS").exists()
                    && !std::path::Path::new(&std_path).exists()
                    {
                        self.diagnostics.push(
                            Diagnostic::warning(
                                span.clone(),
                                                format!("std module `{}` not found at {} — using built-in fallback", lib, std_path),
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
    fn err_hint(&mut self, span: Span, message: impl Into<String>, hint: impl Into<String>) {
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
                _ => {}
            }
        }
    }

    fn check_item(&mut self, item: &Item) {
        match item {
            Item::FnDef(f) => self.check_fn(f),
            Item::ImplBlock(imp) => {
                for method in &imp.methods { self.check_fn(method); }
            }
            Item::ModDecl { inline: Some(items), .. } => {
                for sub_item in items { self.check_item(sub_item); }
            }
            _ => {}
        }
    }

    fn check_fn(&mut self, f: &FnDef) {
        // Collect #[test] functions
        if f.attrs.iter().any(|a| a.name == "test") {
            self.test_fns.push(f.name.clone());
        }
        // Collect #[inline] functions
        if f.attrs.iter().any(|a| a.name == "inline" || a.name == "always_inline") {
            self.inline_fns.insert(f.name.clone());
        }
        // Collect #[must_use] functions
        if f.attrs.iter().any(|a| a.name == "must_use") {
            self.must_use_fns.insert(f.name.clone());
        }
        // Collect #[deprecated]
        if let Some(attr) = f.attrs.iter().find(|a| a.name == "deprecated") {
            let msg = attr.args.iter().find_map(|a| {
                if let AttrArg::KeyValue(k, v) = a { if k == "since" || k == "note" { return Some(v.clone()); } }
                None
            }).unwrap_or_default();
            self.deprecated_items.insert(f.name.clone(), msg);
        }

        self.push_scope();
        let ret_ty = f.return_type.as_ref().map(HType::from_type_expr).unwrap_or(HType::Void);
        self.current_fn_return = Some(ret_ty.clone());

        for param in &f.params {
            let ty = HType::from_type_expr(&param.ty);
            self.define(&param.name, ty, param.mutable);
        }

        for stmt in &f.body { self.check_stmt(stmt, &f.name); }

        // §3: return-path reachability. If `f` declares a non-void return
        // type, every path through its body must end in a `return <expr>`
        // (or, for the common "implicit tail expression" style, the last
        // statement of the body — and of every nested if/match branch —
        // must itself be a `return`). A function that can "fall off the
        // end" without returning is a silent bug: at runtime it currently
        // returns a zero-initialized value of the declared type with no
        // warning at all.
        if !matches!(ret_ty, HType::Void) && !block_always_returns(&f.body) {
            let span = f.body.last().map(|s| stmt_span(s)).unwrap_or_else(|| f.span.clone());
            self.err_hint(
                span,
                format!("function `{}` has return type `{}` but does not return on all paths", f.name, ret_ty.display()),
                    format!("add a `return <{}>` at the end of the function, or in every branch of the final if/match", ret_ty.display()),
            );
        }

        self.pop_scope();
        self.current_fn_return = None;
    }

    fn check_stmt(&mut self, stmt: &Stmt, fn_name: &str) {
        match stmt {
            Stmt::Let { name, ty, mutable, value, .. } => {
                let inferred = value.as_ref().map(|e| self.infer_expr(e));
                let declared = ty.as_ref().map(HType::from_type_expr);
                let final_ty = declared.or(inferred).unwrap_or(HType::Any);
                self.define(name, final_ty, *mutable);
            }
            Stmt::Return(expr, span) => {
                if let Some(ret_ty) = &self.current_fn_return.clone() {
                    let expr_ty = expr.as_ref().map(|e| self.infer_expr(e)).unwrap_or(HType::Void);
                    if !expr_ty.compatible_with(ret_ty) {
                        self.err_hint(
                            span.clone(),
                                      format!("return type mismatch in `{}`: expected `{}`, found `{}`", fn_name, ret_ty.display(), expr_ty.display()),
                                          format!("convert the value to `{}` before returning, or change the function's declared return type", ret_ty.display()),
                        );
                    }
                }
            }
            Stmt::Expr(e, _) => { self.infer_expr(e); }
            Stmt::Item(item) => self.check_item(item),
            _ => {}
        }
    }

    /// Public wrapper around `infer_expr`, used by `monomorphize.rs` (§2)
    /// to determine call-site type arguments for generic functions. Takes
    /// `&mut self` because `infer_expr` may push diagnostics for nested
    /// sub-expressions (e.g. a generic call's arguments might themselves
    /// contain a struct-field-access error) — those diagnostics are still
    /// useful and are retained in `self.diagnostics`.
    pub fn infer_expr_pub(&mut self, expr: &Expr) -> HType {
        self.infer_expr(expr)
    }

    fn infer_expr(&mut self, expr: &Expr) -> HType {
        match expr {
            Expr::Literal(lit, _) => match lit {
                Literal::Int(_)           => HType::Int,
                Literal::Float(_)         => HType::F64,
                Literal::String(_)        => HType::Str,
                Literal::Interpolated(_)  => HType::Str,
                Literal::Bool(_)          => HType::Bool,
                Literal::Nil              => HType::Optional(Box::new(HType::Any)),
                Literal::Bytes(_)         => HType::Bytes,
            },
            Expr::Ident(name, _) => {
                if name.starts_with("__bind:") || name.starts_with("__closure_") { return HType::Any; }
                if let Some(v) = self.lookup(name) { v.ty.clone() }
                else if self.fns.contains_key(name) { HType::Any }
                else { HType::Any } // lenient — don't error on unknown idents
            }
            Expr::BinOp(lhs, op, rhs, _) => {
                let lt = self.infer_expr(lhs);
                let rt = self.infer_expr(rhs);
                match op {
                    BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::Gt |
                    BinOp::LtEq | BinOp::GtEq | BinOp::And | BinOp::Or => HType::Bool,
                    BinOp::Add if matches!(lt, HType::Str) || matches!(rt, HType::Str) => HType::Str,
                    _ => if lt.is_numeric() && rt.is_numeric() { lt } else { HType::Any },
                }
            }
            Expr::UnOp(op, inner, _) => {
                let ty = self.infer_expr(inner);
                match op {
                    UnOp::Not    => HType::Bool,
                    UnOp::Neg    => ty,
                    UnOp::Ref    => HType::Ref(Box::new(ty)),
                    UnOp::RefMut => HType::RefMut(Box::new(ty)),
                    _            => ty,
                }
            }
            Expr::Call(callee, _args, _) => {
                if let Expr::Ident(name, _) = callee.as_ref() {
                    if let Some(sig) = self.fns.get(name).cloned() {
                        return sig.return_type.clone();
                    }
                }
                if let Expr::Path(segments, _) = callee.as_ref() {
                    // Try the fully-qualified name first ("json::parse"),
                    // then fall back to just the last segment (for modules
                    // that were namespace-flattened at expansion time).
                    let full = segments.join("::");
                    if let Some(sig) = self.fns.get(&full).cloned() {
                        return sig.return_type.clone();
                    }
                    if let Some(last) = segments.last() {
                        if let Some(sig) = self.fns.get(last).cloned() {
                            return sig.return_type.clone();
                        }
                    }
                }
                HType::Any
            }
            Expr::Path(_, _) => HType::Any,
            Expr::MethodCall(_, _, _, _) => HType::Any,
            Expr::FieldAccess(base, field, span) => {
                let base_ty = self.infer_expr(base);
                // Unwrap references — `&Foo` / `&mut Foo` field access works
                // the same as `Foo` field access.
                let named = match &base_ty {
                    HType::Named(n) => Some(n.clone()),
                    HType::Ref(inner) | HType::RefMut(inner) => {
                        if let HType::Named(n) = inner.as_ref() { Some(n.clone()) } else { None }
                    }
                    _ => None,
                };
                match named.and_then(|n| self.structs.get(&n).map(|f| (n, f.clone()))) {
                    Some((struct_name, fields)) => {
                        match fields.iter().find(|(fname, _)| fname == field) {
                            Some((_, fty)) => fty.clone(),
                            None => {
                                let available: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                                self.err_hint(
                                    span.clone(),
                                              format!("struct `{}` has no field `{}`", struct_name, field),
                                                  if available.is_empty() {
                                                      format!("`{}` has no fields", struct_name)
                                                  } else {
                                                      format!("available fields: {}", available.join(", "))
                                                  },
                                );
                                HType::Any
                            }
                        }
                    }
                    // Unknown / builtin / non-struct type — stay lenient.
                    None => HType::Any,
                }
            }
            Expr::IndexAccess(arr, _, _) => {
                if let HType::Array(inner) = self.infer_expr(arr) { *inner }
                else { HType::Any }
            }
            Expr::ArrayLit(elems, _) => {
                let inner = elems.first().map(|e| self.infer_expr(e)).unwrap_or(HType::Any);
                HType::Array(Box::new(inner))
            }
            Expr::TupleLit(elems, _) => {
                HType::Tuple(elems.iter().map(|e| self.infer_expr(e)).collect())
            }
            Expr::If { then_body, .. } => {
                then_body.last().map(|s| match s {
                    Stmt::Expr(e, _) => self.infer_expr(e),
                                     _ => HType::Void,
                }).unwrap_or(HType::Void)
            }
            Expr::Cast(inner, ty, span) => {
                let from = self.infer_expr(inner);
                let to   = HType::from_type_expr(ty);
                if !cast_allowed(&from, &to) {
                    self.err_hint(
                        span.clone(),
                                  format!("invalid cast: cannot cast `{}` as `{}`", from.display(), to.display()),
                                      "valid casts: numeric<->numeric, numeric<->bool, any<->concrete type".to_string(),
                    );
                }
                to
            }
            Expr::Return(_, _)    => HType::Void,
            Expr::SelfExpr(_)     => HType::Named("Self".into()),
            Expr::Try(inner, _)   => {
                let ty = self.infer_expr(inner);
                if let HType::Optional(i) = ty { *i } else { ty }
            }
            Expr::Assign(_, rhs, _) => self.infer_expr(rhs),
            Expr::CompoundAssign(lhs, _, _rhs, _) => self.infer_expr(lhs),
            Expr::Range(_, _, _, _) => HType::Array(Box::new(HType::Int)),
            Expr::Closure { return_type, .. } => {
                return_type.as_ref().map(HType::from_type_expr).unwrap_or(HType::Any)
            }
            Expr::Match { subject, arms, span } => {
                let subj_ty = self.infer_expr(subject);
                self.check_match_exhaustive(&subj_ty, arms, span);
                arms.first().and_then(|arm| arm.body.last()).map(|s| match s {
                    Stmt::Expr(e, _) => self.infer_expr(e),
                                                                 _ => HType::Any,
                }).unwrap_or(HType::Any)
            }
            _ => HType::Any,
        }
    }

    fn push_scope(&mut self) { self.scopes.push(HashMap::new()); }
    fn pop_scope(&mut self)  { self.scopes.pop(); }

    fn define(&mut self, name: &str, ty: HType, mutable: bool) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), VarInfo { ty, mutable });
        }
    }

    fn lookup(&self, name: &str) -> Option<&VarInfo> {
        for scope in self.scopes.iter().rev() {
            if let Some(v) = scope.get(name) { return Some(v); }
        }
        None
    }

    /// §3: match exhaustiveness.
    ///
    /// - For `bool` subjects: arms must cover both `true` and `false`
    ///   (literally, or via a catch-all `Pattern::Wildcard`/`Pattern::Ident`).
    /// - For enum subjects (subject type is `HType::Named(enum_name)` where
    ///   `enum_name` is a known enum): arms must cover every
    ///   `EnumVariant::name`, again allowing a catch-all to satisfy any
    ///   remaining variants.
    /// - For any other subject type (int, string, struct, Any, ...): no
    ///   exhaustiveness check is performed — H# doesn't (yet) have a closed
    ///   set of values for these, so a catch-all is effectively mandatory
    ///   but we don't enforce it (would be a separate, noisier lint).
    ///
    /// A missing arm currently means "falls through and does nothing" at
    /// runtime — exactly the kind of silent bug exhaustiveness checking
    /// exists to catch.
    fn check_match_exhaustive(&mut self, subject_ty: &HType, arms: &[MatchArm], match_span: &Span) {
        let has_catchall = arms.iter().any(|arm| {
            arm.guard.is_none() && matches!(arm.pattern, Pattern::Wildcard(_) | Pattern::Ident(_, _))
        });
        if has_catchall { return; }

        match subject_ty {
            HType::Bool => {
                let mut has_true  = false;
                let mut has_false = false;
                for arm in arms {
                    if arm.guard.is_some() { continue; } // guarded arms don't count toward exhaustiveness
                    collect_bool_pattern(&arm.pattern, &mut has_true, &mut has_false);
                }
                if !(has_true && has_false) {
                    let mut missing = Vec::new();
                    if !has_true  { missing.push("true"); }
                    if !has_false { missing.push("false"); }
                    self.err_hint(
                        match_span.clone(),
                                  format!("match on `bool` is not exhaustive: missing {}", missing.join(" and ")),
                                      "add the missing arm(s), or a `_ => ...` catch-all".to_string(),
                    );
                }
            }
            HType::Named(enum_name) => {
                let Some(variants) = self.enums.get(enum_name).cloned() else { return };
                let mut covered: std::collections::HashSet<String> = Default::default();
                for arm in arms {
                    if arm.guard.is_some() { continue; }
                    collect_enum_pattern_variants(&arm.pattern, &mut covered);
                }
                let missing: Vec<&str> = variants.iter()
                .filter(|v| !covered.contains(*v))
                .map(|v| v.as_str())
                .collect();
                if !missing.is_empty() {
                    self.err_hint(
                        match_span.clone(),
                                  format!("match on `{}` is not exhaustive: missing variant(s) {}", enum_name, missing.join(", ")),
                                      "add the missing arm(s), or a `_ => ...` catch-all".to_string(),
                    );
                }
            }
            // int/string/struct/Any/etc: not (yet) exhaustiveness-checked.
            _ => {}
        }
    }
}

/// §3: is `from as to` a valid cast?
///
/// Allowed:
///   - numeric <-> numeric (any int/float width combination — narrowing
///     casts are allowed, matching C/Rust `as` semantics: the programmer
///     is opting into possible truncation)
///   - numeric <-> bool (0/1 <-> false/true, like C)
///   - anything <-> `any` (the escape hatch / dynamic type)
///   - `T as T` (no-op cast, sometimes used for clarity)
///
/// NOT allowed:
///   - string <-> numeric (must go through `to_int()`/`to_string()`, which
///     can fail/format — not a bit-reinterpretation cast)
///   - struct <-> anything (no `#[repr(C)]` layout guarantees yet — see
///     roadmap §5 on extern/struct layout)
fn cast_allowed(from: &HType, to: &HType) -> bool {
    if from == to { return true; }
    if matches!(from, HType::Any) || matches!(to, HType::Any) { return true; }

    let from_num_or_bool = from.is_numeric() || matches!(from, HType::Bool);
    let to_num_or_bool   = to.is_numeric()   || matches!(to, HType::Bool);
    if from_num_or_bool && to_num_or_bool { return true; }

    // Pointer-ish casts (ref <-> ref) are allowed — `unsafe` blocks rely on
    // re-interpreting pointers; the typechecker doesn't try to prove memory
    // safety inside `unsafe`.
    if matches!(from, HType::Ref(_) | HType::RefMut(_)) && matches!(to, HType::Ref(_) | HType::RefMut(_)) {
        return true;
    }

    false
}

/// Walk a pattern, recording whether it matches `true` and/or `false`
/// (for bool exhaustiveness). `Pattern::Or` recurses into each alternative.
fn collect_bool_pattern(pat: &Pattern, has_true: &mut bool, has_false: &mut bool) {
    match pat {
        Pattern::Literal(Literal::Bool(true), _)  => *has_true  = true,
        Pattern::Literal(Literal::Bool(false), _) => *has_false = true,
        Pattern::Or(pats, _) => for p in pats { collect_bool_pattern(p, has_true, has_false); },
        Pattern::Wildcard(_) | Pattern::Ident(_, _) => { *has_true = true; *has_false = true; }
        _ => {}
    }
}

/// Walk a pattern, recording which enum variant names it covers (for enum
/// exhaustiveness). `Pattern::Enum { variant, .. }` and a bare
/// `Pattern::Ident(name, _)` that happens to match a variant's name both
/// count (the latter covers the common style of writing unit variants as
/// plain identifiers without `Enum { .. }` wrapping).
fn collect_enum_pattern_variants(pat: &Pattern, covered: &mut std::collections::HashSet<String>) {
    match pat {
        Pattern::Enum { variant, .. } => { covered.insert(variant.clone()); }
        Pattern::Ident(name, _)       => { covered.insert(name.clone()); }
        Pattern::Or(pats, _)          => for p in pats { collect_enum_pattern_variants(p, covered); },
        _ => {}
    }
}

/// §3: return-path reachability.
///
/// Returns `true` if every execution path through `stmts` ends in a
/// `Stmt::Return` (directly, or via an `if`/`elsif`/`else` where every
/// branch — including a mandatory `else` — itself always-returns, or a
/// `match` where every arm always-returns).
///
/// A `while`/`for` loop is NOT considered to always-return even if its body
/// does, because the loop might execute zero times (or the typechecker
/// can't easily prove it executes at least once) — matching how Rust treats
/// loops for this analysis (a `loop { ... }` with no `break` is the
/// exception Rust special-cases; H# doesn't have bare infinite `loop` as a
/// distinct construct here, so we keep this simple and conservative).
fn block_always_returns(stmts: &[Stmt]) -> bool {
    let Some(last) = stmts.last() else { return false };
    stmt_always_returns(last)
}

fn stmt_always_returns(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Return(_, _) => true,
        Stmt::Expr(Expr::If { then_body, elsif_branches, else_body, .. }, _) => {
            let Some(else_body) = else_body else { return false }; // no else => can fall through
            block_always_returns(then_body)
            && elsif_branches.iter().all(|(_, body)| block_always_returns(body))
            && block_always_returns(else_body)
        }
        Stmt::Expr(Expr::Match { arms, .. }, _) => {
            !arms.is_empty() && arms.iter().all(|arm| block_always_returns(&arm.body))
        }
        // `unsafe is ... end` blocks: reachability follows the inner body.
        Stmt::Expr(Expr::Unsafe(body, _, _), _) => block_always_returns(body),
        _ => false,
    }
}

/// Best-effort span for a statement (used to point reachability errors at
/// "the end of the function" when there's at least one statement to anchor
/// to).
fn stmt_span(stmt: &Stmt) -> Span {
    match stmt {
        Stmt::Let { span, .. } | Stmt::Return(_, span) | Stmt::Break(_, span) |
        Stmt::Continue(span) => span.clone(),
        Stmt::Expr(e, _) => e.span().clone(),
        Stmt::Import(_, _, span) => span.clone(),
        Stmt::Item(item) => item_span(item),
    }
}

fn item_span(item: &Item) -> Span {
    match item {
        Item::FnDef(f)     => f.span.clone(),
        Item::StructDef(s) => s.span.clone(),
        Item::EnumDef(e)   => e.span.clone(),
        Item::TraitDef(t)  => t.span.clone(),
        Item::ImplBlock(i) => i.span.clone(),
        Item::TypeAlias { span, .. } => span.clone(),
        Item::Extern(e)    => e.span.clone(),
        Item::ModDecl { span, .. } => span.clone(),
    }
}
