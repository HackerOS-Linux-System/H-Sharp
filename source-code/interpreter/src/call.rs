use hsharp_parser::ast::*;
use std::collections::HashMap;
use std::net::ToSocketAddrs;
use serde_json::Value as Json;
use sha2::{Sha256, Sha512, Digest as Sha2Digest};
use sha1::Sha1;
use md5::Md5;
use hmac::{Hmac, Mac};
use crate::value::{Value, RuntimeError, Interpreter, AsyncTaskState, Env};
use crate::helpers::{
    values_equal,
    json_to_value, value_to_json,
    resolve_stdlib_alias, builtin_exists,
    compare_values,
};


impl Interpreter {
    pub fn call_path(&mut self, segments: &[String], args: Vec<Value>) -> Result<Value, RuntimeError> {
        // Enum variant construction: `Type::Variant` or `Type::Variant(args)`.
        // Checked first and unconditionally whenever segments[0] names a
        // known enum — this can never collide with anything else
        // meaningful, since an enum type name and a stdlib module alias
        // occupy different namespaces by construction (you can't `use` an
        // enum the way you `use "std -> x"`).
        if segments.len() == 2 {
            if let Some(edef) = self.enums.get(&segments[0]).cloned() {
                if edef.variants.iter().any(|v| v.name == segments[1]) {
                    return Ok(self.make_enum_value(&segments[0], &segments[1], args));
                }
            }
        }
        let full = segments.join("::");
        if self.fns.contains_key(&full) {
            return self.call_fn(&full, args);
        }
        // Static method call on a type with no instance, e.g. `Point::new(...)`
        // or `HashMap::new()` — these are registered in `self.methods` under
        // `TypeName_method` by `register_impl_methods`, separately from
        // `self.fns`, so they need their own lookup here. Only applies to
        // genuine 2-segment `Type::method` paths (not deeper module paths).
        if segments.len() == 2 {
            let method_key = format!("{}_{}", segments[0], segments[1]);
            if let Some(f) = self.methods.get(&method_key).cloned() {
                return self.call_static_method(&f, args);
            }
        }
        if let Some(alias) = resolve_stdlib_alias(&full) {
            return self.call_fn(alias, args);
        }
        let snake = segments.join("_");
        if self.fns.contains_key(&snake) {
            return self.call_fn(&snake, args);
        }
        if let Some(last) = segments.last() {
            if self.fns.contains_key(last) {
                return self.call_fn(last, args);
            }
            // Best-effort: try the snake_case guess, then the bare last
            // segment, in case either happens to be a real builtin name
            // not yet listed in the alias table.
            if builtin_exists(&snake) {
                return self.call_fn(&snake, args);
            }
            return self.call_fn(last, args);
        }
        Err(RuntimeError::UndefinedFn(full))
    }

    /// Run a static `impl` method (one whose first parameter isn't `self`,
    /// e.g. `Point::new(x, y)`) — no receiver to bind, just ordinary
    /// positional parameter binding.
    pub fn call_static_method(&mut self, f: &FnDef, args: Vec<Value>) -> Result<Value, RuntimeError> {
        self.env.push();
        for (param, val) in f.params.iter().zip(args) {
            self.env.define(&param.name, val, param.mutable);
        }
        let result = self.exec_block(&f.body)?;
        self.env.pop();
        Ok(match result {
            Some(Value::Return(v)) => *v,
            Some(v) => v,
            None => Value::Nil,
        })
    }

    /// Construct an enum variant value as a `Value::Struct` whose `name` is
    /// the fully-qualified `"Type::Variant"` string and whose `fields` hold
    /// any tuple-variant payload under numeric string keys (`"0"`, `"1"`,
    /// ...), mirroring how plain tuples already expose `.0`/`.1` access.
    /// This reuses the existing Struct representation rather than adding a
    /// new `Value` variant, so all the generic struct machinery (field
    /// access, equality via field comparison, etc.) works for free. Unit
    /// variants (`Color::Red`) simply get empty `fields`.
    pub fn make_enum_value(&self, enum_name: &str, variant_name: &str, args: Vec<Value>) -> Value {
        let mut fields = HashMap::new();
        for (i, v) in args.into_iter().enumerate() {
            fields.insert(i.to_string(), v);
        }
        Value::Struct { name: format!("{}::{}", enum_name, variant_name), fields }
    }

    /// Register an `impl Type is ... end` block's methods so `value.method(...)`
    /// dispatch (in `call_method`) can find and execute real H#-defined
    /// method bodies instead of only the built-in Rust method table.
    pub fn register_impl_methods(&mut self, type_name: &str, methods: &[FnDef]) {
        for m in methods {
            let key = format!("{}_{}", type_name, m.name);
            self.methods.insert(key, m.clone());
        }
    }

    /// Try to find and run a user-defined `impl` method for a struct value.
    /// Returns `None` if no matching method was registered (caller should
    /// fall back to the builtin method table in that case). On success,
    /// returns `(return_value, mutated_self)` — `mutated_self` reflects any
    /// changes the method body made to `self`'s fields (e.g. `self.x = 5`),
    /// which the caller should write back to the receiver's binding since
    /// this interpreter passes `Value` by clone rather than by reference.
    pub fn try_user_method(&mut self, obj: &Value, method: &str, args: &[Value]) -> Option<Result<(Value, Value), RuntimeError>> {
        let type_name = match obj {
            Value::Struct { name, .. } => name.clone(),
            _ => return None,
        };
        let key = format!("{}_{}", type_name, method);
        let f = self.methods.get(&key)?.clone();

        self.env.push();
        // Bind `self` to the receiver (always mutable inside the method,
        // so `self.field = val` works regardless of how the impl declared
        // its `self` parameter).
        self.env.define("self", obj.clone(), true);
        for (param, val) in f.params.iter().filter(|p| p.name != "self").zip(args.iter().cloned()) {
            self.env.define(&param.name, val, param.mutable);
        }
        let result = self.exec_block(&f.body);
        let mutated_self = self.env.get("self").unwrap_or_else(|| obj.clone());
        self.env.pop();

        Some(result.map(|r| {
            let ret = match r {
                Some(Value::Return(v)) => *v,
                Some(v) => v,
                None => Value::Nil,
            };
            (ret, mutated_self)
        }))
    }

    /// Invoke an already-materialized `Value::Fn` (e.g. a closure passed as
    /// an argument to a builtin like `iter::map`) with the given positional
    /// arguments. This is the same call mechanism `Expr::Call` uses when its
    /// callee evaluates to a closure value, factored out so Rust-side
    /// builtins (iter_map, iter_filter, sort_by, etc.) can invoke H#
    /// closures passed to them.
    pub fn invoke_fn_value(&mut self, params: &[Param], body: &[Stmt], env: Env, args: Vec<Value>) -> Result<Value, RuntimeError> {
        let saved = self.env.clone();
        self.env = env;
        self.env.push();
        for (param, val) in params.iter().zip(args) {
            self.env.define(&param.name, val, param.mutable);
        }
        let result = self.exec_block(body);
        self.env.pop();
        self.env = saved;
        result.map(|r| match r {
            Some(Value::Return(v)) => *v,
            Some(v) => v,
            None => Value::Nil,
        })
    }

    pub fn call_fn(&mut self, name: &str, args: Vec<Value>) -> Result<Value, RuntimeError> {
        // ── std/*.h# → native runtime bridge ────────────────────────────
        // Every `std/*.h#` wrapper function (once actually loaded by a
        // real `use "std -> x"` — see `interp.rs::load_std_module`) calls
        // down into a `__builtin_*`-prefixed intrinsic for anything that
        // needs a genuine native primitive (real file I/O, real SHA-256,
        // real JSON parsing, ...). Those `__builtin_*` names aren't
        // ordinary H# functions and were never given their own match arm
        // below — this is the one place that recognizes the prefix and
        // redirects to whichever real dispatch name backs it.
        if name.starts_with("__builtin_") {
            if let Some(real) = crate::helpers::resolve_builtin_dunder(name) {
                return self.call_fn(real, args);
            }
            return Err(RuntimeError::Custom(crate::helpers::unimplemented_builtin_message(name)));
        }

                    // Check if name is a closure/fn stored in environment (e.g. let triple = |n| n*3)
        if let Some(val) = self.env.get(name) {
            match val {
                Value::Fn { params, body, env: captured_env, is_async, .. } => {
                    let saved = self.env.clone();
                    self.env = captured_env;
                    self.env.push();
                    for (param, val) in params.iter().zip(args.iter()) {
                        self.env.define(&param.name, val.clone(), param.mutable);
                    }
                    let result = self.exec_block(&body)?;
                    self.env.pop();
                    self.env = saved;
                    let resolved = match result {
                        Some(Value::Return(v)) => *v,
                        Some(v) => v,
                        None => Value::Nil,
                    };
                    if is_async {
                        return Ok(Value::AsyncTask(Box::new(AsyncTaskState::Ready(resolved))));
                    }
                    return Ok(resolved);
                }
                _ => {}
            }
        }

        // Builtins
        match name {
            // ── Regex (v0.6) ─────────────────────────────────────────────────
            "re_match" | "regex_match" => {
                let pattern = args.first().map(|v| v.to_string()).unwrap_or_default();
                let text    = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                // Use grep as portable regex engine
                use std::io::Write;
                let mut grep_m = std::process::Command::new("grep")
                    .args(["-qP", &pattern])
                    .stdin(std::process::Stdio::piped())
                    .spawn()
                    .map_err(|_| RuntimeError::TypeError("regex_match: `grep` not found on this system".to_string()))?;
                if let Some(stdin) = grep_m.stdin.as_mut() {
                    let _ = stdin.write_all(text.as_bytes());
                }
                let ok = grep_m.wait().map(|s| s.success()).unwrap_or(false);
                return Ok(Value::Bool(ok));
            }
            "re_find" | "regex_find" => {
                let pattern = args.first().map(|v| v.to_string()).unwrap_or_default();
                let text    = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                use std::io::Write;
                // SAFETY/ROBUSTNESS FIX: every one of these used to fall
                // back to `std::process::exit(1)` (or, worse, a second
                // spawn of the `true` binary that itself `.unwrap()`s) when
                // `grep`/`sed` couldn't be spawned. On a normal machine
                // that's merely abrupt; on `wasm32-unknown-unknown`
                // (the WASM playground) `std::process::exit` compiles to
                // an *uncatchable* WASM trap — not even `catch_unwind` can
                // intercept it — so a program calling `regex_find` in a
                // browser tab that has no `grep` to spawn (always, there's
                // no OS under a browser tab) would crash the whole page
                // with an uncaught JS exception instead of getting a
                // normal H# runtime error. Returning `Err` here goes
                // through the same `Result` channel as every other runtime
                // error, on every target, with no special-casing needed.
                let mut gf = std::process::Command::new("grep")
                    .args(["-oP", &pattern])
                    .stdin(std::process::Stdio::piped())
                    .stdout(std::process::Stdio::piped())
                    .spawn()
                    .map_err(|_| RuntimeError::TypeError("regex_find: `grep` not found on this system".to_string()))?;
                if let Some(s) = gf.stdin.as_mut() { let _ = s.write_all(text.as_bytes()); }
                let gfo = gf.wait_with_output()
                    .map_err(|_| RuntimeError::TypeError("regex_find: failed to read `grep`'s output".to_string()))?;
                return Ok(Value::Str(String::from_utf8_lossy(&gfo.stdout).trim().to_string()));
            }
            "re_find_all" | "regex_find_all" => {
                let pattern = args.first().map(|v| v.to_string()).unwrap_or_default();
                let text    = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                use std::io::Write;
                let mut gfa = std::process::Command::new("grep")
                    .args(["-oP", &pattern])
                    .stdin(std::process::Stdio::piped())
                    .stdout(std::process::Stdio::piped())
                    .spawn()
                    .map_err(|_| RuntimeError::TypeError("regex_find_all: `grep` not found on this system".to_string()))?;
                if let Some(s) = gfa.stdin.as_mut() { let _ = s.write_all(text.as_bytes()); }
                let gfao = gfa.wait_with_output()
                    .map_err(|_| RuntimeError::TypeError("regex_find_all: failed to read `grep`'s output".to_string()))?;
                let results: Vec<Value> = String::from_utf8_lossy(&gfao.stdout)
                    .lines().filter(|l| !l.is_empty())
                    .map(|l| Value::Str(l.to_string())).collect();
                return Ok(Value::Array(results));
            }
            "re_replace" | "regex_replace" => {
                let pattern = args.first().map(|v| v.to_string()).unwrap_or_default();
                let repl    = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let text    = args.get(2).map(|v| v.to_string()).unwrap_or_default();
                use std::io::Write;
                // SECURITY FIX: this used to always splice `pattern`/`repl`
                // into the sed script with a hardcoded `|` delimiter —
                // `format!("s|{}|{}|g", pattern, repl)`. Two real problems,
                // not just cosmetic ones:
                //   1. If `pattern`/`repl` happened to contain a literal
                //      `|`, the resulting script has the wrong number of
                //      delimiters — at best a sed syntax error, at worst
                //      (depending on exactly where the extra `|` lands)
                //      sed parses the tail as a *second* command appended
                //      to the first.
                //   2. sed's `s///` supports an `e` flag that runs the
                //      substitution result as a shell command. Since
                //      nothing here validated that `repl` couldn't itself
                //      supply that flag (e.g. `repl = "x/e"` turning
                //      `s|pat|x/e|g` into a script sed reads differently
                //      than intended), a caller building `pattern`/`repl`
                //      from untrusted input had a real command-injection
                //      surface here, not merely "unexpected behavior".
                // Fixed by (a) picking a delimiter guaranteed absent from
                // *both* strings instead of hardcoding one, and (b)
                // refusing to proceed at all if `pattern`/`repl` contain a
                // newline or NUL — either can inject an additional sed
                // script line/command regardless of which delimiter is
                // chosen, so no delimiter choice alone makes those safe.
                if pattern.contains(['\n', '\0']) || repl.contains(['\n', '\0']) {
                    return Err(RuntimeError::TypeError(
                        "regex_replace: pattern/replacement may not contain a newline or NUL byte".to_string()
                    ));
                }
                const DELIM_CANDIDATES: &[char] = &['|', '#', '~', '\u{1}', '\u{2}', '\u{3}'];
                let delim = DELIM_CANDIDATES.iter().find(|&&d| {
                    !pattern.contains(d) && !repl.contains(d)
                });
                let delim = match delim {
                    Some(d) => *d,
                    None => return Err(RuntimeError::TypeError(
                        "regex_replace: couldn't find a safe delimiter character not present in the pattern or replacement".to_string()
                    )),
                };
                let sed_script = format!("s{d}{p}{d}{r}{d}g", d = delim, p = pattern, r = repl);
                let mut sed_c = std::process::Command::new("sed")
                    .args(["-E", &sed_script])
                    .stdin(std::process::Stdio::piped())
                    .stdout(std::process::Stdio::piped())
                    .spawn()
                    .map_err(|_| RuntimeError::TypeError("regex_replace: `sed` not found on this system".to_string()))?;
                if let Some(s) = sed_c.stdin.as_mut() { let _ = s.write_all(text.as_bytes()); }
                let sed_out = sed_c.wait_with_output()
                    .map_err(|_| RuntimeError::TypeError("regex_replace: failed to read `sed`'s output".to_string()))?;
                return Ok(Value::Str(String::from_utf8_lossy(&sed_out.stdout).trim_end().to_string()));
            }
            // ── (text, pattern) argument-order wrappers ───────────────────────
            // std/regex.h#'s documented H# API takes the subject text first
            // (`is_match(s, pattern)`, `find(s, pattern)`, etc.), matching
            // common scripting-language convention — but the underlying
            // grep/sed-based builtins above were written expecting
            // (pattern, text)/(pattern, repl, text). These wrappers just
            // swap argument order before delegating, so `re::is_match(text,
            // pattern)` from H# code resolves correctly via the alias table.
            "re_match_ta" => {
                let text = args.first().cloned().unwrap_or(Value::Nil);
                let pat  = args.get(1).cloned().unwrap_or(Value::Nil);
                return self.call_fn("re_match", vec![pat, text]);
            }
            "re_find_ta" => {
                let text = args.first().cloned().unwrap_or(Value::Nil);
                let pat  = args.get(1).cloned().unwrap_or(Value::Nil);
                return self.call_fn("re_find", vec![pat, text]);
            }
            "re_find_all_ta" => {
                let text = args.first().cloned().unwrap_or(Value::Nil);
                let pat  = args.get(1).cloned().unwrap_or(Value::Nil);
                return self.call_fn("re_find_all", vec![pat, text]);
            }
            "re_replace_ta" => {
                let text = args.first().cloned().unwrap_or(Value::Nil);
                let pat  = args.get(1).cloned().unwrap_or(Value::Nil);
                let repl = args.get(2).cloned().unwrap_or(Value::Nil);
                return self.call_fn("re_replace", vec![pat, repl, text]);
            }
            "re_replace_all_ta" => {
                let text = args.first().cloned().unwrap_or(Value::Nil);
                let pat  = args.get(1).cloned().unwrap_or(Value::Nil);
                let repl = args.get(2).cloned().unwrap_or(Value::Nil);
                // "replace all" and "replace" are the same operation here
                // since the sed `g` flag already replaces every match.
                return self.call_fn("re_replace", vec![pat, repl, text]);
            }
            "re_split_ta" => {
                let text    = args.first().map(|v| v.to_string()).unwrap_or_default();
                let pattern = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let mut p = std::process::Command::new("grep")
                    .args(["-ozP", &pattern])
                    .stdin(std::process::Stdio::piped())
                    .stdout(std::process::Stdio::piped())
                    .spawn();
                // Simplest portable approach: use Rust's own splitting once
                // we have a way to test the pattern per-position is complex
                // without a real regex engine, so fall back to a basic
                // whitespace-pattern-aware split for the common `\s+` case
                // and a literal split otherwise.
                let _ = &mut p;
                if pattern == r"\s+" || pattern == r"\s*" {
                    let parts: Vec<Value> = text.split_whitespace().map(|s| Value::Str(s.to_string())).collect();
                    return Ok(Value::Array(parts));
                }
                // Literal-substring split fallback for simple patterns.
                let parts: Vec<Value> = text.split(pattern.as_str()).map(|s| Value::Str(s.to_string())).collect();
                return Ok(Value::Array(parts));
            }
            // ── SQLite (v0.6) ─────────────────────────────────────────────────
            "sqlite_open" | "db_open" => {
                let path = args.first().map(|v| v.to_string()).unwrap_or_else(|| "./db.sqlite".to_string());
                // Return the path as a db handle (string-based for portability)
                return Ok(Value::Str(format!("sqlite://{}", path)));
            }
            "sqlite_exec" | "db_exec" => {
                let db   = args.first().map(|v| v.to_string()).unwrap_or_default();
                let sql  = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let path = db.strip_prefix("sqlite://").unwrap_or(&db);
                let out  = std::process::Command::new("sqlite3")
                    .arg(path).arg(&sql)
                    .output();
                return Ok(match out {
                    Ok(o) if o.status.success() => Value::Str(String::from_utf8_lossy(&o.stdout).to_string()),
                    Ok(o) => Value::Str(format!("db error: {}", String::from_utf8_lossy(&o.stderr))),
                    Err(e) => Value::Str(format!("sqlite3 not found: {}", e)),
                });
            }
            "sqlite_query" | "db_query" => {
                let db   = args.first().map(|v| v.to_string()).unwrap_or_default();
                let sql  = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let path = db.strip_prefix("sqlite://").unwrap_or(&db);
                let out  = std::process::Command::new("sqlite3")
                    .args(["-separator", ",", path, &sql])
                    .output();
                let rows: Vec<Value> = match out {
                    Ok(o) => String::from_utf8_lossy(&o.stdout)
                        .lines()
                        .filter(|l| !l.is_empty())
                        .map(|l| {
                            let cols: Vec<Value> = l.split(',')
                                .map(|c| Value::Str(c.trim().to_string()))
                                .collect();
                            Value::Array(cols)
                        })
                        .collect(),
                    Err(_) => vec![],
                };
                return Ok(Value::Array(rows));
            }
            "sqlite_close" | "db_close" => {
                return Ok(Value::Nil); // SQLite files don't need explicit close
            }
            // ── Profiler (v0.6) ───────────────────────────────────────────────
            "prof_start" | "profile_start" => {
                let label = args.first().map(|v| v.to_string()).unwrap_or_else(|| "default".to_string());
                // Store start time in a global map (use env for now)
                let start_ns = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .map(|d| d.as_nanos() as i64)
                    .unwrap_or(0);
                self.env.define(&format!("__prof_{}", label), Value::Int(start_ns), true);
                return Ok(Value::Int(start_ns));
            }
            "prof_end" | "profile_end" => {
                let label = args.first().map(|v| v.to_string()).unwrap_or_else(|| "default".to_string());
                let end_ns = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .map(|d| d.as_nanos() as i64)
                    .unwrap_or(0);
                let start_ns = self.env.get(&format!("__prof_{}", label))
                    .and_then(|v| if let Value::Int(n) = v { Some(n) } else { None })
                    .unwrap_or(end_ns);
                let elapsed_ms = (end_ns - start_ns) / 1_000_000;
                let msg = format!("[prof] {} = {}ms", label, elapsed_ms);
                return Ok(Value::Str(msg));
            }
            "prof_report" => {
                // Print all profiler entries
                let report: Vec<String> = self.env.all_vars()
                    .iter()
                    .filter(|(k, _)| k.starts_with("__prof_"))
                    .map(|(k, v)| format!("  {}: started at {:?}", k.trim_start_matches("__prof_"), v.to_string()))
                    .collect();
                return Ok(Value::Str(format!("[profiler report]
{}", report.join("
"))));
            }
            // ── Large project tooling ─────────────────────────────────────────
            "module_info" => {
                return Ok(Value::Str(format!("module: {} functions registered", self.fns.len())));
            }
            "heap_size" | "memory_usage" => {
                // Read /proc/self/status for VmRSS
                let mem = std::fs::read_to_string("/proc/self/status").ok()
                    .and_then(|s| s.lines()
                        .find(|l| l.starts_with("VmRSS:"))
                        .map(|l| l.split_whitespace().nth(1).unwrap_or("0").parse::<i64>().unwrap_or(0)))
                    .unwrap_or(0);
                return Ok(Value::Int(mem));
            }
            // ── io (real stdin — but only when output isn't captured;
            // captured mode is used by the playground/tests, which have
            // no real stdin to read from, so blocking there would just
            // hang instead of erroring) ─────────────────────────────────
            "io_read_line" => {
                if self.captured_output {
                    return Ok(Value::Str(String::new()));
                }
                use std::io::Write;
                let _ = std::io::stdout().flush();
                let mut line = String::new();
                let n = std::io::stdin().read_line(&mut line).unwrap_or(0);
                if n == 0 { return Ok(Value::Str(String::new())); } // real EOF
                if line.ends_with('\n') { line.pop(); if line.ends_with('\r') { line.pop(); } }
                return Ok(Value::Str(line));
            }
            "io_read_char" => {
                if self.captured_output {
                    return Ok(Value::Str(String::new()));
                }
                use std::io::Read;
                let mut buf = [0u8; 1];
                let n = std::io::stdin().read(&mut buf).unwrap_or(0);
                if n == 0 { return Ok(Value::Str(String::new())); }
                return Ok(Value::Str((buf[0] as char).to_string()));
            }
            "io_write_no_nl" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                use std::io::Write;
                if self.captured_output {
                    self.stdout.push_str(&s);
                } else {
                    print!("{}", s);
                    let _ = std::io::stdout().flush();
                }
                return Ok(Value::Nil);
            }
            "io_flush" => {
                use std::io::Write;
                let _ = std::io::stdout().flush();
                return Ok(Value::Nil);
            }
            // ── sys (real /proc parsing on Linux; honest 0/false
            // fallback elsewhere — there is no cross-platform sysinfo
            // crate dependency available to verify in this environment) ──
            "sys_cpu_count" => {
                let n = std::fs::read_to_string("/proc/cpuinfo")
                    .map(|s| s.lines().filter(|l| l.starts_with("processor")).count() as i64)
                    .unwrap_or(1);
                return Ok(Value::Int(n.max(1)));
            }
            "sys_memory_total" | "sys_memory_free" => {
                let key = if name == "sys_memory_total" { "MemTotal:" } else { "MemAvailable:" };
                let kb = std::fs::read_to_string("/proc/meminfo").ok()
                    .and_then(|s| s.lines().find(|l| l.starts_with(key))
                        .and_then(|l| l.split_whitespace().nth(1))
                        .and_then(|n| n.parse::<i64>().ok()))
                    .unwrap_or(0);
                return Ok(Value::Int(kb * 1024)); // bytes
            }
            "sys_uptime" => {
                let secs = std::fs::read_to_string("/proc/uptime").ok()
                    .and_then(|s| s.split_whitespace().next().map(|s| s.to_string()))
                    .and_then(|s| s.parse::<f64>().ok())
                    .unwrap_or(0.0);
                return Ok(Value::Int(secs as i64));
            }
            "sys_load_avg" => {
                let load = std::fs::read_to_string("/proc/loadavg").ok()
                    .and_then(|s| s.split_whitespace().next().map(|s| s.to_string()))
                    .and_then(|s| s.parse::<f64>().ok())
                    .unwrap_or(0.0);
                return Ok(Value::Float(load));
            }
            "sys_disk_total" | "sys_disk_free" => {
                // `df -k <path>` — portable across Unixes without a
                // `statvfs` FFI binding this crate doesn't have.
                let path = args.first().map(|v| v.to_string()).unwrap_or_else(|| "/".to_string());
                let out = std::process::Command::new("df").args(["-k", &path]).output();
                let kb = out.ok().and_then(|o| {
                    let text = String::from_utf8_lossy(&o.stdout).to_string();
                    let line = text.lines().nth(1)?.to_string();
                    let cols: Vec<&str> = line.split_whitespace().collect();
                    // df -k: Filesystem 1K-blocks Used Available Use% Mounted
                    let idx = if name == "sys_disk_total" { 1 } else { 3 };
                    cols.get(idx)?.parse::<i64>().ok()
                }).unwrap_or(0);
                return Ok(Value::Int(kb * 1024));
            }
            "sys_page_size" => {
                let out = std::process::Command::new("getconf").arg("PAGESIZE").output();
                let sz = out.ok()
                    .and_then(|o| String::from_utf8_lossy(&o.stdout).trim().parse::<i64>().ok())
                    .unwrap_or(4096);
                return Ok(Value::Int(sz));
            }
            "sys_get_uid" | "sys_get_gid" | "sys_get_ppid" => {
                let n = match name {
                    "sys_get_uid" => std::process::Command::new("id").arg("-u").output().ok()
                        .and_then(|o| String::from_utf8_lossy(&o.stdout).trim().parse::<i64>().ok()).unwrap_or(0),
                    "sys_get_gid" => std::process::Command::new("id").arg("-g").output().ok()
                        .and_then(|o| String::from_utf8_lossy(&o.stdout).trim().parse::<i64>().ok()).unwrap_or(0),
                    // No getppid(2) FFI binding in this crate — shells
                    // out to `ps` instead, which is a bit heavier but
                    // dependency-free and portable across Unixes.
                    _ => std::process::Command::new("ps").args(["-o", "ppid=", "-p", &std::process::id().to_string()]).output().ok()
                        .and_then(|o| String::from_utf8_lossy(&o.stdout).trim().parse::<i64>().ok()).unwrap_or(0),
                };
                return Ok(Value::Int(n));
            }
            "sys_is_64bit" => { return Ok(Value::Bool(std::mem::size_of::<usize>() == 8)); }
            "sys_is_little_endian" => { return Ok(Value::Bool(cfg!(target_endian = "little"))); }
            "sys_sysname" | "sys_machine" => {
                let flag = if name == "sys_sysname" { "-s" } else { "-m" };
                let out = std::process::Command::new("uname").arg(flag).output();
                let v = out.ok().map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string()).unwrap_or_default();
                return Ok(Value::Str(v));
            }
            "print" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                if self.captured_output {
                    self.stdout.push_str(&s);
                } else {
                    print!("{}", s);
                }
                return Ok(Value::Nil);
            }
            // H# 0.1: write() is the primary output function
            "write" | "writeln" | "println" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                if self.captured_output {
                    self.stdout.push_str(&s);
                    self.stdout.push('\n');
                } else {
                    println!("{}", s);
                }
                return Ok(Value::Nil);
            }
            "panic" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Err(RuntimeError::Panic(s));
            }
            "exit" => {
                let code = match args.first() {
                    Some(Value::Int(n)) => *n as i32,
                    _ => 0,
                };
                return Err(RuntimeError::Exit(code));
            }
            "len" => {
                return Ok(match args.first() {
                    Some(Value::Array(a)) => Value::Int(a.len() as i64),
                    Some(Value::Str(s)) => Value::Int(s.len() as i64),
                    Some(Value::Bytes(b)) => Value::Int(b.len() as i64),
                    _ => Value::Int(0),
                });
            }
            "assert" => {
                let cond = args.first().map(|v| v.is_truthy()).unwrap_or(false);
                if !cond {
                    let msg = args.get(1).map(|v| v.to_string()).unwrap_or_else(|| "assertion failed".into());
                    return Err(RuntimeError::Panic(msg));
                }
                return Ok(Value::Nil);
            }
            "to_string" => {
                return Ok(Value::Str(args.first().map(|v| v.to_string()).unwrap_or_default()));
            }
            // ── char <-> codepoint (backs std/conv.h#) ─────────────────────
            "str_to_char_code" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let cp = s.chars().next().map(|c| c as i64).unwrap_or(0);
                return Ok(Value::Int(cp));
            }
            "char_code_to_str" => {
                let n = args.first().map(|v| v.to_int()).unwrap_or(0);
                let s = u32::try_from(n).ok().and_then(char::from_u32).map(|c| c.to_string()).unwrap_or_default();
                return Ok(Value::Str(s));
            }
            "parse_int" => {
                let s = match args.first() {
                    Some(Value::Str(s)) => s.clone(),
                    _ => return Ok(Value::Nil),
                };
                return Ok(s.parse::<i64>().map(Value::Int).unwrap_or(Value::Nil));
            }
            // Free-function form of the `(Value::Str, "parse_float")`
            // method-call arm in `call_method` below — added so
            // `std/conv.h#`'s `str_to_float` can reach it via
            // `__builtin_conv_str_to_float`, the same way `parse_int`
            // already had both a free-function and (elsewhere) a method
            // form.
            "parse_float" => {
                let s = match args.first() {
                    Some(Value::Str(s)) => s.clone(),
                    _ => return Ok(Value::Nil),
                };
                return Ok(s.trim().parse::<f64>().map(Value::Float).unwrap_or(Value::Nil));
            }
            // ── v0.3 Real stdlib — no stubs ────────────────────────────
            "trim" | "str_trim" => {
                return Ok(Value::Str(args.first().map(|v| v.to_string()).unwrap_or_default().trim().to_string()));
            }
            "to_upper" | "upper" => {
                return Ok(Value::Str(args.first().map(|v| v.to_string()).unwrap_or_default().to_uppercase()));
            }
            "to_lower" | "lower" => {
                return Ok(Value::Str(args.first().map(|v| v.to_string()).unwrap_or_default().to_lowercase()));
            }
            "contains" | "str_contains" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let p = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(s.contains(p.as_str())));
            }
            "starts_with" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let p = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(s.starts_with(p.as_str())));
            }
            "ends_with" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let p = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(s.ends_with(p.as_str())));
            }
            "replace" | "str_replace" | "str_replace_all" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let f = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let t = args.get(2).map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Str(s.replace(f.as_str(), t.as_str())));
            }
            "str_split_whitespace" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let parts: Vec<Value> = s.split_whitespace().map(|p| Value::Str(p.to_string())).collect();
                return Ok(Value::Array(parts));
            }
            "split" | "str_split" => {
                let s   = args.first().map(|v| v.to_string()).unwrap_or_default();
                let sep = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let parts = s.split(sep.as_str()).map(|p| Value::Str(p.to_string())).collect();
                return Ok(Value::Array(parts));
            }
            "str_join" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let sep = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let parts: Vec<String> = arr.iter().map(|v| v.to_string()).collect();
                return Ok(Value::Str(parts.join(&sep)));
            }
            "conv_str_to_int" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Int(s.trim().parse::<i64>().unwrap_or(0)));
            }
            "conv_int_to_hex" => {
                let n = args.first().map(|v| v.to_int()).unwrap_or(0);
                return Ok(Value::Str(format!("{:x}", n)));
            }
            "conv_to_bytes" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bytes(s.into_bytes()));
            }
            "now_unix" | "time_unix" => {
                use std::time::{SystemTime, UNIX_EPOCH};
                let secs = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs() as i64).unwrap_or(0);
                return Ok(Value::Int(secs));
            }
            "now_ms" | "time_ms" => {
                use std::time::{SystemTime, UNIX_EPOCH};
                let ms = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_millis() as i64).unwrap_or(0);
                return Ok(Value::Int(ms));
            }
            "sleep_ms" => {
                let ms = args.first().map(|v| v.to_int()).unwrap_or(0) as u64;
                std::thread::sleep(std::time::Duration::from_millis(ms));
                return Ok(Value::Nil);
            }
            "shell" | "cmd" => {
                let cmd = args.first().map(|v| v.to_string()).unwrap_or_default();
                let out = std::process::Command::new("sh").arg("-c").arg(cmd.as_str()).output();
                return Ok(match out {
                    Ok(o) => Value::Str(String::from_utf8_lossy(&o.stdout).trim_end().to_string()),
                    Err(e) => Value::Str(format!("shell error: {}", e)),
                });
            }
            "getpid" | "pid" => { return Ok(Value::Int(std::process::id() as i64)); }
            "random_hex" => {
                let n = args.first().map(|v| v.to_int()).unwrap_or(8).max(0) as usize;
                let mut bytes = vec![0u8; n];
                if let Ok(mut f) = std::fs::File::open("/dev/urandom") {
                    use std::io::Read; let _ = f.read_exact(&mut bytes);
                }
                return Ok(Value::Str(bytes.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "hex_encode" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Str(s.as_bytes().iter().map(|b| format!("{:02x}", b)).collect()));
            }
            // Bytes-aware variant — `hex_encode` above stringifies its
            // argument first, which for `Value::Bytes` produces the
            // `"<bytes len=N>"` placeholder (same issue `sha256_bytes`
            // was added to fix). Backs `std/sec.h#`'s `hex_encode(data:
            // bytes)`.
            "hex_encode_bytes" => {
                let data: Vec<u8> = match args.first() {
                    Some(Value::Bytes(b)) => b.clone(),
                    Some(Value::Str(s)) => s.clone().into_bytes(),
                    _ => Vec::new(),
                };
                return Ok(Value::Str(data.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "hex_decode" => {
                let h = args.first().map(|v| v.to_string()).unwrap_or_default();
                let bytes: Vec<u8> = (0..h.len()).step_by(2)
                    .filter_map(|i| h.get(i..i+2).and_then(|b| u8::from_str_radix(b, 16).ok()))
                    .collect();
                return Ok(Value::Str(String::from_utf8_lossy(&bytes).to_string()));
            }
            "random_int" => {
                let min = args.first().map(|v| v.to_int()).unwrap_or(0);
                let max = args.get(1).map(|v| v.to_int()).unwrap_or(100);
                let mut buf = [0u8; 8];
                if let Ok(mut f) = std::fs::File::open("/dev/urandom") {
                    use std::io::Read; let _ = f.read_exact(&mut buf);
                }
                let r = (i64::from_le_bytes(buf).unsigned_abs() as i64).abs();
                return Ok(Value::Int(if max > min { min + r % (max - min) } else { min }));
            }
            "random_string" => {
                let n = args.first().map(|v| v.to_int()).unwrap_or(8).max(0) as usize;
                let cs = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
                let mut bytes = vec![0u8; n];
                if let Ok(mut f) = std::fs::File::open("/dev/urandom") {
                    use std::io::Read; let _ = f.read_exact(&mut bytes);
                }
                return Ok(Value::Str(bytes.iter().map(|&b| cs[b as usize % cs.len()] as char).collect()));
            }
            // Real *raw* random bytes (not the alphanumeric-string form
            // above) — backs `std/crypto.h#`'s `random_bytes(n) -> bytes`.
            "crypto_random_bytes" => {
                let n = args.first().map(|v| v.to_int()).unwrap_or(0).max(0) as usize;
                let mut bytes = vec![0u8; n];
                if let Ok(mut f) = std::fs::File::open("/dev/urandom") {
                    use std::io::Read; let _ = f.read_exact(&mut bytes);
                }
                return Ok(Value::Bytes(bytes));
            }
            "crypto_bytes_eq" => {
                let a: Vec<u8> = match args.first() { Some(Value::Bytes(b)) => b.clone(), _ => Vec::new() };
                let b: Vec<u8> = match args.get(1) { Some(Value::Bytes(b)) => b.clone(), _ => Vec::new() };
                // Genuinely constant-time (doesn't short-circuit on the
                // first mismatch) — the whole point of this function
                // over `==` is resisting timing side-channels on MAC
                // comparison.
                let mut diff: u8 = (a.len() != b.len()) as u8;
                for i in 0..a.len().max(b.len()) {
                    diff |= a.get(i).unwrap_or(&0) ^ b.get(i).unwrap_or(&0);
                }
                return Ok(Value::Bool(diff == 0));
            }
            "crypto_xor_bytes" => {
                let a: Vec<u8> = match args.first() { Some(Value::Bytes(b)) => b.clone(), _ => Vec::new() };
                let b: Vec<u8> = match args.get(1) { Some(Value::Bytes(b)) => b.clone(), _ => Vec::new() };
                if a.len() != b.len() || a.is_empty() {
                    return Ok(Value::Bytes(Vec::new()));
                }
                let out: Vec<u8> = a.iter().zip(b.iter()).map(|(x, y)| x ^ y).collect();
                return Ok(Value::Bytes(out));
            }
            "hostname" => {
                let h = std::fs::read_to_string("/etc/hostname").map(|s| s.trim().to_string()).unwrap_or_else(|_| "unknown".into());
                return Ok(Value::Str(h));
            }
            // ── Math (v0.8) ──────────────────────────────────────────────────
            "math_sin"   => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).sin())),
            "math_cos"   => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).cos())),
            "math_tan"   => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).tan())),
            "math_asin"  => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).asin())),
            "math_acos"  => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).acos())),
            "math_atan"  => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).atan())),
            "math_atan2" => {
                let y = args.first().map(|v| v.to_float()).unwrap_or(0.0);
                let x = args.get(1).map(|v| v.to_float()).unwrap_or(0.0);
                return Ok(Value::Float(y.atan2(x)));
            }
            "math_sqrt"  => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).sqrt())),
            "math_pow"   => {
                let base = args.first().map(|v| v.to_float()).unwrap_or(0.0);
                let exp  = args.get(1).map(|v| v.to_float()).unwrap_or(0.0);
                return Ok(Value::Float(base.powf(exp)));
            }
            "math_floor" => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).floor())),
            "math_ceil"  => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).ceil())),
            "math_round" => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).round())),
            "math_trunc" => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).trunc())),
            // `std/conv.h#`'s `float_to_int` needs an actual int back
            // (math_trunc above intentionally stays float-in-float-out,
            // matching every other math_* function) — this is that
            // conversion.
            "conv_float_to_int" => {
                let f = args.first().map(|v| v.to_float()).unwrap_or(0.0);
                return Ok(Value::Int(f.trunc() as i64));
            }
            "math_log"   => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).ln())),
            "math_log2"  => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).log2())),
            "math_log10" => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).log10())),
            "math_exp"   => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).exp())),
            "math_abs" => {
                let v = args.first().cloned().unwrap_or(Value::Int(0));
                return Ok(match v {
                    Value::Int(n)   => Value::Int(n.abs()),
                    Value::Float(f) => Value::Float(f.abs()),
                    _ => v,
                });
            }
            "math_fabs" => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).abs())),
            "math_ipow" => {
                let base = args.first().map(|v| v.to_int()).unwrap_or(0);
                let exp  = args.get(1).map(|v| v.to_int()).unwrap_or(0).max(0) as u32;
                return Ok(Value::Int(base.pow(exp)));
            }
            "math_min" => {
                let a = args.first().cloned().unwrap_or(Value::Int(0));
                let b = args.get(1).cloned().unwrap_or(Value::Int(0));
                return Ok(match (&a, &b) {
                    (Value::Int(x), Value::Int(y)) => Value::Int(*x.min(y)),
                    _ => if a.to_float() < b.to_float() { a } else { b },
                });
            }
            "math_max" => {
                let a = args.first().cloned().unwrap_or(Value::Int(0));
                let b = args.get(1).cloned().unwrap_or(Value::Int(0));
                return Ok(match (&a, &b) {
                    (Value::Int(x), Value::Int(y)) => Value::Int(*x.max(y)),
                    _ => if a.to_float() > b.to_float() { a } else { b },
                });
            }
            "math_fmin" => {
                let a = args.first().map(|v| v.to_float()).unwrap_or(0.0);
                let b = args.get(1).map(|v| v.to_float()).unwrap_or(0.0);
                return Ok(Value::Float(a.min(b)));
            }
            "math_fmax" => {
                let a = args.first().map(|v| v.to_float()).unwrap_or(0.0);
                let b = args.get(1).map(|v| v.to_float()).unwrap_or(0.0);
                return Ok(Value::Float(a.max(b)));
            }
            "math_clamp" => {
                let v  = args.first().map(|v| v.to_int()).unwrap_or(0);
                let lo = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                let hi = args.get(2).map(|v| v.to_int()).unwrap_or(0);
                return Ok(Value::Int(v.max(lo).min(hi)));
            }
            "math_fclamp" => {
                let v  = args.first().map(|v| v.to_float()).unwrap_or(0.0);
                let lo = args.get(1).map(|v| v.to_float()).unwrap_or(0.0);
                let hi = args.get(2).map(|v| v.to_float()).unwrap_or(0.0);
                return Ok(Value::Float(v.max(lo).min(hi)));
            }
            "math_gcd" => {
                let mut a = args.first().map(|v| v.to_int()).unwrap_or(0).abs();
                let mut b = args.get(1).map(|v| v.to_int()).unwrap_or(0).abs();
                while b != 0 { let t = b; b = a % b; a = t; }
                return Ok(Value::Int(a));
            }
            "math_lcm" => {
                let a = args.first().map(|v| v.to_int()).unwrap_or(0);
                let b = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                if a == 0 || b == 0 { return Ok(Value::Int(0)); }
                let mut x = a.abs();
                let mut y = b.abs();
                while y != 0 { let t = y; y = x % y; x = t; }
                return Ok(Value::Int((a / x * b).abs()));
            }
            "math_pi"  => return Ok(Value::Float(std::f64::consts::PI)),
            "math_e"   => return Ok(Value::Float(std::f64::consts::E)),
            "math_tau" => return Ok(Value::Float(std::f64::consts::TAU)),
            // ── JSON (v0.8) ──────────────────────────────────────────────────
            "json_parse" => {
                let raw = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(match serde_json::from_str::<Json>(&raw) {
                    Ok(j)  => json_to_value(&j),
                    Err(_) => Value::Nil,
                });
            }
            "json_parse_array" => {
                let raw = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(match serde_json::from_str::<Json>(&raw) {
                    Ok(Json::Array(items)) => Value::Array(items.iter().map(json_to_value).collect()),
                    _ => Value::Array(Vec::new()),
                });
            }
            "json_stringify" => {
                let v = args.first().cloned().unwrap_or(Value::Nil);
                let j = value_to_json(&v);
                return Ok(Value::Str(serde_json::to_string(&j).unwrap_or_default()));
            }
            "json_stringify_pretty" => {
                let v = args.first().cloned().unwrap_or(Value::Nil);
                let j = value_to_json(&v);
                return Ok(Value::Str(serde_json::to_string_pretty(&j).unwrap_or_default()));
            }
            "json_empty_object" => {
                return Ok(Value::Struct { name: "__json".to_string(), fields: HashMap::new() });
            }
            "json_get_str" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(fields.get(&key).map(|v| Value::Str(v.to_string())).unwrap_or(Value::Str(String::new())));
                }
                return Ok(Value::Str(String::new()));
            }
            "json_get_int" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Int(fields.get(&key).map(|v| v.to_int()).unwrap_or(0)));
                }
                return Ok(Value::Int(0));
            }
            "json_get_float" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Float(fields.get(&key).map(|v| v.to_float()).unwrap_or(0.0)));
                }
                return Ok(Value::Float(0.0));
            }
            "json_get_bool" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Bool(matches!(fields.get(&key), Some(Value::Bool(true)))));
                }
                return Ok(Value::Bool(false));
            }
            "json_get_obj" | "json_get_arr" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(fields.get(&key).cloned().unwrap_or(Value::Nil));
                }
                return Ok(Value::Nil);
            }
            "json_has_key" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Bool(fields.contains_key(&key)));
                }
                return Ok(Value::Bool(false));
            }
            "json_is_null" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Bool(matches!(fields.get(&key), Some(Value::Nil) | None)));
                }
                return Ok(Value::Bool(true));
            }
            "json_set" => {
                // NOTE: H# values are passed by value in this interpreter
                // (no shared mutable references), so `json::set_str(obj, ...)`
                // cannot mutate the caller's `obj` binding in place the way
                // a reference-based runtime could. This builtin returns the
                // *updated* struct; H# code must re-bind it, e.g.:
                //   obj = json::set_str(obj, "key", "val")
                // The fluent `json::object([...])` constructor is the
                // recommended way to build objects instead.
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let val = args.get(2).cloned().unwrap_or(Value::Nil);
                if let Some(Value::Struct { name, mut fields }) = args.first().cloned() {
                    fields.insert(key, val);
                    return Ok(Value::Struct { name, fields });
                }
                return Ok(Value::Nil);
            }
            "json_as_int" => return Ok(Value::Int(args.first().map(|v| v.to_int()).unwrap_or(0))),
            "json_as_str" => return Ok(Value::Str(args.first().map(|v| v.to_string()).unwrap_or_default())),
            "json_object" => {
                // Build an object from an array of (key, value) tuples, e.g.
                // json::object([("lang", "H#"), ("version", "0.6")]).
                let mut fields = HashMap::new();
                if let Some(Value::Array(pairs)) = args.first() {
                    for pair in pairs {
                        if let Value::Tuple(items) = pair {
                            if items.len() == 2 {
                                let key = items[0].to_string();
                                fields.insert(key, items[1].clone());
                            }
                        }
                    }
                }
                return Ok(Value::Struct { name: "__json".to_string(), fields });
            }
            "json_int_at" => {
                let idx = args.get(1).map(|v| v.to_int()).unwrap_or(0) as usize;
                if let Some(Value::Array(arr)) = args.first() {
                    return Ok(Value::Int(arr.get(idx).map(|v| v.to_int()).unwrap_or(0)));
                }
                return Ok(Value::Int(0));
            }
            "json_obj_at" => {
                let idx = args.get(1).map(|v| v.to_int()).unwrap_or(0) as usize;
                if let Some(Value::Array(arr)) = args.first() {
                    return Ok(arr.get(idx).cloned().unwrap_or(Value::Nil));
                }
                return Ok(Value::Nil);
            }
            "json_query" => {
                let path = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let mut current = args.first().cloned().unwrap_or(Value::Nil);
                for segment in path.split('.') {
                    current = match current {
                        Value::Struct { fields, .. } => fields.get(segment).cloned().unwrap_or(Value::Nil),
                        _ => Value::Nil,
                    };
                }
                return Ok(current);
            }
            // ── HashMap (v0.8) — backed by Value::Struct{name:"__hashmap"} ────
            // Keys are encoded via Value::to_string() since the underlying
            // storage is a plain string-keyed map; this is sufficient for
            // the common case of string/int keys used throughout the stdlib.
            "hashmap_new" => return Ok(Value::Struct { name: "__hashmap".into(), fields: HashMap::new() }),
            "hashmap_insert" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let val = args.get(2).cloned().unwrap_or(Value::Nil);
                if let Some(Value::Struct { name, mut fields }) = args.first().cloned() {
                    fields.insert(key, val);
                    return Ok(Value::Struct { name, fields });
                }
                return Ok(Value::Nil);
            }
            "hashmap_get" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(fields.get(&key).cloned().unwrap_or(Value::Nil));
                }
                return Ok(Value::Nil);
            }
            "hashmap_contains" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Bool(fields.contains_key(&key)));
                }
                return Ok(Value::Bool(false));
            }
            "hashmap_remove" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { name, mut fields }) = args.first().cloned() {
                    fields.remove(&key);
                    return Ok(Value::Struct { name, fields });
                }
                return Ok(Value::Nil);
            }
            "hashmap_len" => {
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Int(fields.len() as i64));
                }
                return Ok(Value::Int(0));
            }
            "hashmap_keys" => {
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Array(fields.keys().map(|k| Value::Str(k.clone())).collect()));
                }
                return Ok(Value::Array(Vec::new()));
            }
            "hashmap_values" => {
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Array(fields.values().cloned().collect()));
                }
                return Ok(Value::Array(Vec::new()));
            }
            // ── HashSet (v0.8) — wraps a Value::Array of unique values ────────
            "hashset_new" => {
                let mut fields = HashMap::new();
                fields.insert("items".to_string(), Value::Array(Vec::new()));
                return Ok(Value::Struct { name: "__hashset".into(), fields });
            }
            "hashset_insert" => {
                let val = args.get(1).cloned().unwrap_or(Value::Nil);
                if let Some(Value::Struct { name, fields }) = args.first().cloned() {
                    let items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                    let mut new_items = items;
                    if !new_items.iter().any(|v| values_equal(v, &val)) {
                        new_items.push(val);
                    }
                    let mut new_fields = fields;
                    new_fields.insert("items".to_string(), Value::Array(new_items));
                    return Ok(Value::Struct { name, fields: new_fields });
                }
                return Ok(Value::Nil);
            }
            "hashset_contains" => {
                let val = args.get(1).cloned().unwrap_or(Value::Nil);
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    if let Some(Value::Array(items)) = fields.get("items") {
                        return Ok(Value::Bool(items.iter().any(|v| values_equal(v, &val))));
                    }
                }
                return Ok(Value::Bool(false));
            }
            "hashset_remove" => {
                let val = args.get(1).cloned().unwrap_or(Value::Nil);
                if let Some(Value::Struct { name, fields }) = args.first().cloned() {
                    let items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                    let new_items: Vec<Value> = items.into_iter().filter(|v| !values_equal(v, &val)).collect();
                    let mut new_fields = fields;
                    new_fields.insert("items".to_string(), Value::Array(new_items));
                    return Ok(Value::Struct { name, fields: new_fields });
                }
                return Ok(Value::Nil);
            }
            "hashset_len" => {
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    if let Some(Value::Array(items)) = fields.get("items") {
                        return Ok(Value::Int(items.len() as i64));
                    }
                }
                return Ok(Value::Int(0));
            }
            "hashset_to_array" => {
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(fields.get("items").cloned().unwrap_or(Value::Array(Vec::new())));
                }
                return Ok(Value::Array(Vec::new()));
            }
            // ── Queue / Stack (v0.8) — each wraps a Value::Array under a
            // distinct struct name so call_method/compute_mutated_container
            // can give them FIFO vs LIFO pop semantics that differ from a
            // plain array's (and from each other).
            "queue_new" => {
                let mut fields = HashMap::new();
                fields.insert("items".to_string(), Value::Array(Vec::new()));
                return Ok(Value::Struct { name: "__queue".into(), fields });
            }
            "stack_new" => {
                let mut fields = HashMap::new();
                fields.insert("items".to_string(), Value::Array(Vec::new()));
                return Ok(Value::Struct { name: "__stack".into(), fields });
            }
            "fs_read" | "read_file" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(std::fs::read_to_string(p.as_str()).map(Value::Str).unwrap_or(Value::Nil));
            }
            "fs_write" | "write_file" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let c = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::write(p.as_str(), c.as_str());
                return Ok(Value::Nil);
            }
            "fs_exists" | "file_exists" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(std::path::Path::new(p.as_str()).exists()));
            }
            "fs_mkdir_all" | "mkdir_all" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::create_dir_all(p.as_str());
                return Ok(Value::Nil);
            }
            "fs_remove" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::remove_file(p.as_str());
                return Ok(Value::Nil);
            }
            "fs_append" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let c = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                use std::io::Write;
                if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(p.as_str()) {
                    let _ = f.write_all(c.as_bytes());
                }
                return Ok(Value::Nil);
            }
            "fs_is_dir" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(std::path::Path::new(p.as_str()).is_dir()));
            }
            "fs_is_file" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(std::path::Path::new(p.as_str()).is_file()));
            }
            "fs_rmdir" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::remove_dir(p.as_str());
                return Ok(Value::Nil);
            }
            "fs_rmdir_all" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::remove_dir_all(p.as_str());
                return Ok(Value::Nil);
            }
            "fs_read_lines" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let content = std::fs::read_to_string(p.as_str()).unwrap_or_default();
                let lines: Vec<Value> = content.lines().map(|l| Value::Str(l.to_string())).collect();
                return Ok(Value::Array(lines));
            }
            "fs_size" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let sz = std::fs::metadata(p.as_str()).map(|m| m.len()).unwrap_or(0);
                return Ok(Value::Int(sz as i64));
            }
            "fs_copy" => {
                let src = args.first().map(|v| v.to_string()).unwrap_or_default();
                let dst = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::copy(src.as_str(), dst.as_str());
                return Ok(Value::Nil);
            }
            "fs_rename" => {
                let src = args.first().map(|v| v.to_string()).unwrap_or_default();
                let dst = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::rename(src.as_str(), dst.as_str());
                return Ok(Value::Nil);
            }
            "fs_cwd" => {
                let cwd = std::env::current_dir().map(|p| p.display().to_string()).unwrap_or_default();
                return Ok(Value::Str(cwd));
            }
            "fs_chdir" => {
                // Real implementation — previously `fs::chdir` was aliased
                // straight to `fs_cwd` (see helpers.rs's alias table),
                // meaning it silently read-and-returned the cwd instead of
                // ever changing it. `std::env::set_current_dir` mirrors
                // the LLVM backend's `hsh_chdir` (runtime/core.c): returns
                // whether it succeeded rather than raising, matching this
                // interpreter's existing fs_* convention of int/bool
                // success flags (see fs_rename/fs_copy above) rather than
                // a distinct error-reporting channel.
                let path = args.first().map(|v| v.to_string()).unwrap_or_default();
                let ok = std::env::set_current_dir(&path).is_ok();
                return Ok(Value::Int(if ok { 1 } else { 0 }));
            }
            "fs_list_dir" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let entries: Vec<Value> = std::fs::read_dir(p.as_str())
                    .map(|rd| rd.filter_map(|e| e.ok())
                        .map(|e| Value::Str(e.file_name().to_string_lossy().to_string()))
                        .collect())
                    .unwrap_or_default();
                return Ok(Value::Array(entries));
            }
            "fs_read_bytes" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(std::fs::read(p.as_str()).map(Value::Bytes).unwrap_or(Value::Nil));
            }
            "fs_write_bytes" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let data: Vec<u8> = match args.get(1) {
                    Some(Value::Bytes(b)) => b.clone(),
                    Some(Value::Str(s)) => s.clone().into_bytes(),
                    _ => Vec::new(),
                };
                let _ = std::fs::write(p.as_str(), &data);
                return Ok(Value::Nil);
            }
            // Build raw `bytes` from an `[int]` array of 0-255 byte
            // values. Needed because H# `string`s are UTF-8-validated
            // text — there's no way to represent e.g. a lone 0x80 byte
            // (an invalid standalone UTF-8 lead byte) as a `string` at
            // all, which binary formats like MessagePack need to emit
            // freely. Backs `std/msgpack.h#`.
            "bytes_from_ints" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let data: Vec<u8> = arr.iter().map(|v| (v.to_int() & 0xff) as u8).collect();
                return Ok(Value::Bytes(data));
            }
            // Inverse of the above — read raw bytes back out as an
            // `[int]` array of 0-255 values, for decoding a binary
            // format byte-by-byte in H#.
            "bytes_to_ints" => {
                let data: Vec<u8> = match args.first() { Some(Value::Bytes(b)) => b.clone(), _ => Vec::new() };
                let arr: Vec<Value> = data.iter().map(|&b| Value::Int(b as i64)).collect();
                return Ok(Value::Array(arr));
            }
            "bytes_concat" => {
                let mut out: Vec<u8> = match args.first() { Some(Value::Bytes(b)) => b.clone(), _ => Vec::new() };
                if let Some(Value::Bytes(b)) = args.get(1) { out.extend_from_slice(b); }
                return Ok(Value::Bytes(out));
            }
            "bytes_len" => {
                let n = match args.first() { Some(Value::Bytes(b)) => b.len(), _ => 0 };
                return Ok(Value::Int(n as i64));
            }
            // `std/fs.h#`'s `walk(root)` — real recursive directory walk,
            // returning every *file* path found beneath `root` (matching
            // the doc comment on the H# side: "Returns all file paths").
            // Written by hand instead of pulling in the `walkdir` crate,
            // since this is the only caller and the recursion is a few
            // lines; symlinks are followed via `read_dir`'s own default
            // behavior (no explicit cycle guard — same tradeoff libc's
            // `nftw` without `FTW_PHYS` makes).
            "fs_walk" => {
                let root = args.first().map(|v| v.to_string()).unwrap_or_default();
                let mut out: Vec<Value> = Vec::new();
                let mut stack = vec![std::path::PathBuf::from(&root)];
                while let Some(dir) = stack.pop() {
                    let Ok(rd) = std::fs::read_dir(&dir) else { continue };
                    for entry in rd.filter_map(|e| e.ok()) {
                        let path = entry.path();
                        if path.is_dir() {
                            stack.push(path);
                        } else {
                            out.push(Value::Str(path.to_string_lossy().to_string()));
                        }
                    }
                }
                return Ok(Value::Array(out));
            }
            // `std/fs.h#`'s `modified_time(path)` — last-modified time as
            // a unix timestamp (seconds), matching `time.h#`/`date.h#`'s
            // convention of representing instants as `int` seconds since
            // the epoch rather than a dedicated timestamp type.
            "fs_modified_time" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let secs = std::fs::metadata(p.as_str())
                    .and_then(|m| m.modified())
                    .ok()
                    .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                    .map(|d| d.as_secs() as i64)
                    .unwrap_or(0);
                return Ok(Value::Int(secs));
            }
            // `std/fs.h#`'s `temp_file(prefix)` — creates an empty file
            // under the OS temp dir and returns its path, so the caller
            // gets back something that's guaranteed to already exist
            // (rather than just a "probably free" name), same guarantee
            // `mkstemp(3)` gives on a real OS.
            "fs_temp_file" => {
                let prefix = args.first().map(|v| v.to_string()).unwrap_or_default();
                let unique = format!(
                    "{}{}_{}",
                    prefix,
                    std::process::id(),
                    std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .map(|d| d.as_nanos())
                        .unwrap_or(0),
                );
                let path = std::env::temp_dir().join(unique);
                let _ = std::fs::write(&path, b"");
                return Ok(Value::Str(path.to_string_lossy().to_string()));
            }
            // ── path (v0.8) ──────────────────────────────────────────────────
            "path_join" => {
                let a = args.first().map(|v| v.to_string()).unwrap_or_default();
                let b = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let joined = std::path::Path::new(&a).join(&b);
                return Ok(Value::Str(joined.to_string_lossy().to_string()));
            }
            "path_stem" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let stem = std::path::Path::new(&p).file_stem()
                    .map(|s| s.to_string_lossy().to_string())
                    .unwrap_or_default();
                return Ok(Value::Str(stem));
            }
            "path_extension" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let ext = std::path::Path::new(&p).extension()
                    .map(|s| s.to_string_lossy().to_string())
                    .unwrap_or_default();
                return Ok(Value::Str(ext));
            }
            "path_parent" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let parent = std::path::Path::new(&p).parent()
                    .map(|s| s.to_string_lossy().to_string())
                    .unwrap_or_default();
                return Ok(Value::Str(parent));
            }
            "path_filename" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let f = std::path::Path::new(&p).file_name()
                    .map(|s| s.to_string_lossy().to_string())
                    .unwrap_or_default();
                return Ok(Value::Str(f));
            }
            "path_is_absolute" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(std::path::Path::new(&p).is_absolute()));
            }
            // Lexical normalization only (`.`/`..` component folding) —
            // does not touch the filesystem or resolve symlinks, unlike
            // `fs::canonicalize`. That distinction matters: `normalize`
            // should work on paths that don't exist yet (e.g. a path
            // you're about to create), which `canonicalize` can't do.
            "path_normalize" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let mut out: Vec<std::path::Component> = Vec::new();
                for comp in std::path::Path::new(&p).components() {
                    match comp {
                        std::path::Component::ParentDir => { out.pop(); }
                        std::path::Component::CurDir => {}
                        other => out.push(other),
                    }
                }
                let joined: std::path::PathBuf = out.iter().collect();
                return Ok(Value::Str(joined.to_string_lossy().to_string()));
            }
            "path_with_extension" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let ext = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let out = std::path::Path::new(&p).with_extension(&ext);
                return Ok(Value::Str(out.to_string_lossy().to_string()));
            }
            // ── env (v0.8) ───────────────────────────────────────────────────
            "env_temp_dir" => {
                return Ok(Value::Str(std::env::temp_dir().to_string_lossy().to_string()));
            }
            "env_get" => {
                let k = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(std::env::var(&k).map(Value::Str).unwrap_or(Value::Nil));
            }
            "env_args" => {
                let a: Vec<Value> = std::env::args().map(Value::Str).collect();
                return Ok(Value::Array(a));
            }
            "env_home" => {
                return Ok(std::env::var("HOME").map(Value::Str).unwrap_or(Value::Str(String::new())));
            }
            // `env::set`/`env::remove` — `std::env::set_var`/`remove_var`
            // only affect this process (and anything it spawns), same
            // scope `setenv(3)`/`unsetenv(3)` have; there's no way for an
            // H# program to reach back and mutate its parent shell's
            // environment, same as any other language.
            "env_set" => {
                let k = args.first().map(|v| v.to_string()).unwrap_or_default();
                let v = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                unsafe { std::env::set_var(&k, &v); }
                return Ok(Value::Nil);
            }
            "env_remove" => {
                let k = args.first().map(|v| v.to_string()).unwrap_or_default();
                unsafe { std::env::remove_var(&k); }
                return Ok(Value::Nil);
            }
            // Returns `["KEY=value", ...]` — kept as a flat array of
            // `"KEY=value"` strings rather than a map, since H#'s
            // `hashmap_*` builtins live behind `std -> collections` and
            // this is a `core`-level primitive that shouldn't have to
            // know about that struct representation.
            "env_vars" => {
                let vars: Vec<Value> = std::env::vars().map(|(k, v)| Value::Str(format!("{k}={v}"))).collect();
                return Ok(Value::Array(vars));
            }
            // ── os (v0.9) ────────────────────────────────────────────────────
            "os_platform" => { return Ok(Value::Str(std::env::consts::OS.to_string())); }
            "os_arch"     => { return Ok(Value::Str(std::env::consts::ARCH.to_string())); }
            "os_username" => {
                let u = std::env::var("USER").or_else(|_| std::env::var("LOGNAME")).unwrap_or_default();
                return Ok(Value::Str(u));
            }
            "os_home_dir" => {
                return Ok(std::env::var("HOME").map(Value::Str).unwrap_or(Value::Str(String::new())));
            }
            "os_is_root" => {
                // No libc dependency: shell out to `id -u`, the same
                // interface `sh` scripts use for this exact check.
                let out = std::process::Command::new("id").arg("-u").output();
                let uid = out.ok()
                    .and_then(|o| String::from_utf8_lossy(&o.stdout).trim().parse::<i64>().ok())
                    .unwrap_or(-1);
                return Ok(Value::Bool(uid == 0));
            }
            "os_kernel_version" => {
                let out = std::process::Command::new("uname").arg("-r").output();
                let v = out.ok().map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string()).unwrap_or_default();
                return Ok(Value::Str(v));
            }
            // ── process (v0.9) ───────────────────────────────────────────────
            // `run`/`run_args` capture stdout (matching `std/process.h#`'s
            // doc comments: "returns output"); real exit-code / stderr
            // access would need a richer return type than `string`, which
            // is intentionally left to a future revision of
            // `std/process.h#` rather than smuggled into this one as a
            // stringly-typed hack.
            "proc_run" => {
                let cmd = args.first().map(|v| v.to_string()).unwrap_or_default();
                let out = std::process::Command::new("sh").arg("-c").arg(&cmd).output();
                return Ok(match out {
                    Ok(o) => Value::Str(String::from_utf8_lossy(&o.stdout).to_string()),
                    Err(e) => Value::Str(format!("process error: {e}")),
                });
            }
            "proc_run_args" => {
                let cmd = args.first().map(|v| v.to_string()).unwrap_or_default();
                let argv: Vec<String> = match args.get(1) {
                    Some(Value::Array(a)) => a.iter().map(|v| v.to_string()).collect(),
                    _ => Vec::new(),
                };
                let out = std::process::Command::new(&cmd).args(&argv).output();
                return Ok(match out {
                    Ok(o) => Value::Str(String::from_utf8_lossy(&o.stdout).to_string()),
                    Err(e) => Value::Str(format!("process error: {e}")),
                });
            }
            // Fire-and-forget spawn — returns the child PID so the H#
            // caller can later `proc_kill`/`proc_exit_code` it, mirroring
            // `fork`+`exec`'s PID-as-handle convention rather than
            // returning some opaque handle type H# doesn't have yet.
            "proc_spawn" => {
                let cmd = args.first().map(|v| v.to_string()).unwrap_or_default();
                let child = std::process::Command::new("sh").arg("-c").arg(&cmd).spawn();
                return Ok(match child {
                    Ok(c) => Value::Int(c.id() as i64),
                    Err(_) => Value::Int(-1),
                });
            }
            "proc_kill" => {
                let pid = args.first().map(|v| v.to_int()).unwrap_or(0);
                let _ = std::process::Command::new("kill").arg(pid.to_string()).status();
                return Ok(Value::Nil);
            }
            "proc_which" => {
                let cmd = args.first().map(|v| v.to_string()).unwrap_or_default();
                let out = std::process::Command::new("which").arg(&cmd).output();
                let path = out.ok()
                    .filter(|o| o.status.success())
                    .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
                    .unwrap_or_default();
                return Ok(Value::Str(path));
            }
            // ── term (v0.9) ──────────────────────────────────────────────────
            // No ioctl/termios crate available — shells out to `stty
            // size`, reading the controlling terminal directly
            // (`-F /dev/tty`) so it still works when stdout itself is
            // redirected/piped. Falls back to the conventional 80x24
            // default (same fallback most CLI tools use) if that fails,
            // e.g. because there's no controlling terminal at all.
            "term_width" | "term_height" => {
                let out = std::process::Command::new("stty").args(["size", "-F", "/dev/tty"]).output();
                let (rows, cols) = out.ok()
                    .filter(|o| o.status.success())
                    .and_then(|o| {
                        let s = String::from_utf8_lossy(&o.stdout).trim().to_string();
                        let mut parts = s.split_whitespace();
                        let r = parts.next()?.parse::<i64>().ok()?;
                        let c = parts.next()?.parse::<i64>().ok()?;
                        Some((r, c))
                    })
                    .unwrap_or((24, 80));
                return Ok(Value::Int(if name == "term_width" { cols } else { rows }));
            }
            "term_is_tty" => {
                // `test -t 1` is the portable, dependency-free way to ask
                // "is stdout a terminal" from a spawned subprocess; doing
                // it for *this* process without a libc/atty crate would
                // need an `isatty(3)` FFI call this crate doesn't have.
                let out = std::process::Command::new("sh").arg("-c").arg("test -t 1").status();
                return Ok(Value::Bool(out.map(|s| s.success()).unwrap_or(false)));
            }
            // ── tcp (real client sockets, std::net — no crate needed) ───────
            // Connections are kept alive in `self.tcp_streams`, keyed by
            // a handle returned to H# as a plain int (see the doc comment
            // on that field in value.rs for why a socket can't just be
            // "reopened by address" the way sqlite/file paths are
            // elsewhere in this file).
            "tcp_connect" => {
                let host = args.first().map(|v| v.to_string()).unwrap_or_default();
                let port = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                let addr = format!("{host}:{port}");
                match std::net::TcpStream::connect(&addr) {
                    Ok(stream) => {
                        let handle = self.next_tcp_handle;
                        self.next_tcp_handle += 1;
                        self.tcp_streams.insert(handle, stream);
                        return Ok(Value::Int(handle));
                    }
                    Err(_) => return Ok(Value::Int(-1)),
                }
            }
            "tcp_send" => {
                use std::io::Write;
                let handle = args.first().map(|v| v.to_int()).unwrap_or(-1);
                let data = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let ok = self.tcp_streams.get_mut(&handle)
                    .map(|s| s.write_all(data.as_bytes()).is_ok())
                    .unwrap_or(false);
                return Ok(Value::Bool(ok));
            }
            "tcp_recv" => {
                use std::io::Read;
                let handle = args.first().map(|v| v.to_int()).unwrap_or(-1);
                let size = args.get(1).map(|v| v.to_int()).unwrap_or(4096).max(0) as usize;
                let mut buf = vec![0u8; size];
                let n = self.tcp_streams.get_mut(&handle)
                    .and_then(|s| s.read(&mut buf).ok())
                    .unwrap_or(0);
                buf.truncate(n);
                return Ok(Value::Str(String::from_utf8_lossy(&buf).to_string()));
            }
            "tcp_close" => {
                let handle = args.first().map(|v| v.to_int()).unwrap_or(-1);
                self.tcp_streams.remove(&handle);
                return Ok(Value::Nil);
            }
            // ── sync (named atomics — see std/sync.h#'s module doc
            // comment for why these are real state, just never
            // contended in this single-native-thread interpreter) ──────
            "atomic_add" => {
                let key = args.first().map(|v| v.to_string()).unwrap_or_default();
                let delta = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                let entry = self.atomics.entry(key).or_insert(0);
                *entry += delta;
                return Ok(Value::Int(*entry));
            }
            "atomic_load" => {
                let key = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Int(*self.atomics.get(&key).unwrap_or(&0)));
            }
            "atomic_store" => {
                let key = args.first().map(|v| v.to_string()).unwrap_or_default();
                let val = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                self.atomics.insert(key, val);
                return Ok(Value::Nil);
            }
            // Real reachability check with a genuine timeout (the naive
            // `TcpStream::connect` above blocks with no timeout at all,
            // which is wrong for a "is this port open" probe specifically)
            "tcp_scan_port" => {
                let host = args.first().map(|v| v.to_string()).unwrap_or_default();
                let port = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                let timeout_ms = args.get(2).map(|v| v.to_int()).unwrap_or(1000).max(0) as u64;
                let addr = format!("{host}:{port}");
                let ok = addr.to_socket_addrs().ok()
                    .and_then(|mut it| it.next())
                    .map(|sa| std::net::TcpStream::connect_timeout(&sa, std::time::Duration::from_millis(timeout_ms)).is_ok())
                    .unwrap_or(false);
                return Ok(Value::Bool(ok));
            }
            // ── http (plain HTTP/1.1 only — NO TLS backend in this
            // runtime, so `https://` URLs will simply fail to connect;
            // that's a real, stated limitation, not a silent downgrade) ──
            // Hand-rolled over the same `std::net::TcpStream` `tcp_*`
            // uses above, since there's no way to verify a `reqwest`/
            // `hyper`/`native-tls` dependency resolves in this
            // environment. Real enough for `http://` APIs and local
            // services; not a browser-grade HTTP client (no redirects,
            // no chunked-transfer decoding, no keep-alive).
            "http_request" => {
                let method = args.first().map(|v| v.to_string()).unwrap_or_else(|| "GET".to_string());
                let url = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let body = args.get(2).map(|v| v.to_string()).unwrap_or_default();
                return Ok(http_request(&method, &url, &body));
            }
            "uuid_v4" => {
                let mut b = [0u8; 16];
                if let Ok(mut f) = std::fs::File::open("/dev/urandom") {
                    use std::io::Read; let _ = f.read_exact(&mut b);
                }
                b[6] = (b[6] & 0x0f) | 0x40; // version 4
                b[8] = (b[8] & 0x3f) | 0x80; // variant 10
                let hex: String = b.iter().map(|x| format!("{:02x}", x)).collect();
                let s = format!(
                    "{}-{}-{}-{}-{}",
                    &hex[0..8], &hex[8..12], &hex[12..16], &hex[16..20], &hex[20..32]
                );
                return Ok(Value::Str(s));
            }
            "uuid_is_valid" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let bytes = s.as_bytes();
                let ok = bytes.len() == 36
                    && bytes[8] == b'-' && bytes[13] == b'-' && bytes[18] == b'-' && bytes[23] == b'-'
                    && s.chars().enumerate().all(|(i, c)| {
                        matches!(i, 8 | 13 | 18 | 23) || c.is_ascii_hexdigit()
                    });
                return Ok(Value::Bool(ok));
            }
            // ── base64 (RFC 4648, standard alphabet, `=` padding) ───────────
            // Hand-written rather than pulling in the `base64` crate:
            // there's no way to `cargo add` + verify a new dependency
            // resolves in this environment, and the algorithm itself is
            // short and has no edge cases worth a crate for.
            "base64_encode" => {
                let data: Vec<u8> = match args.first() {
                    Some(Value::Bytes(b)) => b.clone(),
                    Some(Value::Str(s)) => s.clone().into_bytes(),
                    _ => Vec::new(),
                };
                return Ok(Value::Str(base64_encode_bytes(&data)));
            }
            "base64url_encode" => {
                let data: Vec<u8> = match args.first() {
                    Some(Value::Bytes(b)) => b.clone(),
                    Some(Value::Str(s)) => s.clone().into_bytes(),
                    _ => Vec::new(),
                };
                let b64 = base64_encode_bytes(&data);
                let url = b64.replace('+', "-").replace('/', "_").trim_end_matches('=').to_string();
                return Ok(Value::Str(url));
            }
            "base64url_decode" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let mut std_form = s.replace('-', "+").replace('_', "/");
                while std_form.len() % 4 != 0 { std_form.push('='); }
                return Ok(match base64_decode_str(&std_form) {
                    Some(bytes) => Value::Str(String::from_utf8_lossy(&bytes).to_string()),
                    None => Value::Nil,
                });
            }
            "base64_decode" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(match base64_decode_str(&s) {
                    Some(bytes) => Value::Str(String::from_utf8_lossy(&bytes).to_string()),
                    None => Value::Nil,
                });
            }
            // ── percent-encoding (RFC 3986 unreserved set) ──────────────────
            "url_encode" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let mut out = String::with_capacity(s.len());
                for b in s.bytes() {
                    if b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.' | b'~') {
                        out.push(b as char);
                    } else {
                        out.push_str(&format!("%{:02X}", b));
                    }
                }
                return Ok(Value::Str(out));
            }
            "url_decode" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let bytes = s.as_bytes();
                let mut out = Vec::with_capacity(bytes.len());
                let mut i = 0;
                while i < bytes.len() {
                    if bytes[i] == b'%' && i + 2 < bytes.len() {
                        if let Ok(b) = u8::from_str_radix(&s[i + 1..i + 3], 16) {
                            out.push(b);
                            i += 3;
                            continue;
                        }
                    }
                    out.push(if bytes[i] == b'+' { b' ' } else { bytes[i] });
                    i += 1;
                }
                return Ok(Value::Str(String::from_utf8_lossy(&out).to_string()));
            }
            // ── date/time (proleptic Gregorian, UTC only) ───────────────────
            // Uses Howard Hinnant's `civil_from_days`/`days_from_civil`
            // (public-domain algorithm, http://howardhinnant.github.io/date_algorithms.html)
            // instead of a `chrono`/`time` crate dependency this
            // environment has no way to verify resolves. UTC-only is a
            // real, stated limitation — no timezone database is bundled.
            "date_year" | "date_month" | "date_day" | "date_weekday" => {
                let ts = args.first().map(|v| v.to_int()).unwrap_or(0);
                let (y, m, d, wd) = civil_from_unix(ts);
                return Ok(match name {
                    "date_year"    => Value::Int(y),
                    "date_month"   => Value::Int(m),
                    "date_day"     => Value::Int(d),
                    _ => Value::Str(["Thu","Fri","Sat","Sun","Mon","Tue","Wed"][(wd.rem_euclid(7)) as usize].to_string()),
                });
            }
            "date_add_days" => {
                let ts = args.first().map(|v| v.to_int()).unwrap_or(0);
                let days = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                return Ok(Value::Int(ts + days * 86400));
            }
            "date_add_hours" => {
                let ts = args.first().map(|v| v.to_int()).unwrap_or(0);
                let hrs = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                return Ok(Value::Int(ts + hrs * 3600));
            }
            "date_diff_days" => {
                let a = args.first().map(|v| v.to_int()).unwrap_or(0);
                let b = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                return Ok(Value::Int((a - b) / 86400));
            }
            // Supports the common subset: %Y %m %d %H %M %S. Anything
            // wider (locale names, %z, ...) is a documented gap in
            // `std/date.h#`/`std/time.h#`, not something silently
            // faked here.
            "date_format" => {
                let ts = args.first().map(|v| v.to_int()).unwrap_or(0);
                let fmt = args.get(1).map(|v| v.to_string()).unwrap_or_else(|| "%Y-%m-%d %H:%M:%S".to_string());
                let (y, mo, d, _) = civil_from_unix(ts);
                let secs_of_day = ts.rem_euclid(86400);
                let (h, mi, se) = (secs_of_day / 3600, (secs_of_day / 60) % 60, secs_of_day % 60);
                let out = fmt
                    .replace("%Y", &format!("{:04}", y))
                    .replace("%m", &format!("{:02}", mo))
                    .replace("%d", &format!("{:02}", d))
                    .replace("%H", &format!("{:02}", h))
                    .replace("%M", &format!("{:02}", mi))
                    .replace("%S", &format!("{:02}", se));
                return Ok(Value::Str(out));
            }
            // Parses exactly "YYYY-MM-DD" or "YYYY-MM-DD HH:MM:SS" — the
            // `fmt` argument is accepted for API-compatibility with
            // `format` but not otherwise interpreted (a real strptime-
            // style parser is future work, tracked in std/date.h#'s doc
            // comment rather than faked here).
            "date_parse" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let (date_part, time_part) = s.split_once(' ').unwrap_or((s.as_str(), "00:00:00"));
                let dparts: Vec<i64> = date_part.split('-').filter_map(|p| p.parse().ok()).collect();
                let tparts: Vec<i64> = time_part.split(':').filter_map(|p| p.parse().ok()).collect();
                if dparts.len() != 3 {
                    return Ok(Value::Int(0));
                }
                let days = days_from_civil(dparts[0], dparts[1], dparts[2]);
                let secs = tparts.first().copied().unwrap_or(0) * 3600
                    + tparts.get(1).copied().unwrap_or(0) * 60
                    + tparts.get(2).copied().unwrap_or(0);
                return Ok(Value::Int(days * 86400 + secs));
            }
            // ── iter (v0.8) — higher-order array operations that invoke
            // H# closures passed as Value::Fn arguments via invoke_fn_value.
            // `sort_by` — comparator-based sort, invoking an H# closure
            // for each comparison (see `invoke_fn_value`'s doc comment,
            // which already named this as a planned caller). Uses a
            // simple insertion sort rather than relying on Rust's
            // `sort_by` + a closure that can return `Err`, since a
            // comparator invocation can fail (e.g. the user's closure
            // panics) and `Vec::sort_by`'s comparator can't propagate a
            // `Result` — insertion sort's comparisons are trivial to
            // thread a `?` through one at a time instead.
            "sort_by" => {
                let mut arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let f = args.get(1).cloned();
                let (params, body, fenv) = match &f {
                    Some(Value::Fn { params, body, env, .. }) => (params.clone(), body.clone(), env.clone()),
                    _ => return Ok(Value::Array(arr)),
                };
                for i in 1..arr.len() {
                    let mut j = i;
                    while j > 0 {
                        let cmp = self.invoke_fn_value(&params, &body, fenv.clone(), vec![arr[j - 1].clone(), arr[j].clone()])?;
                        if cmp.to_int() > 0 {
                            arr.swap(j - 1, j);
                            j -= 1;
                        } else {
                            break;
                        }
                    }
                }
                return Ok(Value::Array(arr));
            }
            "iter_map" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let f = args.get(1).cloned();
                let mut result = Vec::with_capacity(arr.len());
                for x in arr {

                    let v = match &f {
                        Some(Value::Fn { params, body, env, .. }) =>
                            self.invoke_fn_value(params, body, env.clone(), vec![x])?,
                        _ => Value::Nil,
                    };
                    result.push(v);
                }
                return Ok(Value::Array(result));
            }
            "iter_filter" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let f = args.get(1).cloned();
                let mut result = Vec::new();
                for x in arr {
                    let keep = match &f {
                        Some(Value::Fn { params, body, env, .. }) =>
                            matches!(self.invoke_fn_value(params, body, env.clone(), vec![x.clone()])?, Value::Bool(true)),
                        _ => false,
                    };
                    if keep { result.push(x); }
                }
                return Ok(Value::Array(result));
            }
            "iter_reduce" => {
                let arr  = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let init = args.get(1).cloned().unwrap_or(Value::Nil);
                let f    = args.get(2).cloned();
                let mut acc = init;
                for x in arr {
                    acc = match &f {
                        Some(Value::Fn { params, body, env, .. }) =>
                            self.invoke_fn_value(params, body, env.clone(), vec![acc, x])?,
                        _ => acc,
                    };
                }
                return Ok(acc);
            }
            "iter_zip" => {
                let a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let b = match args.get(1) { Some(Value::Array(b)) => b.clone(), _ => Vec::new() };
                let len = a.len().min(b.len());
                let zipped: Vec<Value> = (0..len).map(|i| Value::Tuple(vec![a[i].clone(), b[i].clone()])).collect();
                return Ok(Value::Array(zipped));
            }
            "iter_chain" => {
                let mut a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let b = match args.get(1) { Some(Value::Array(b)) => b.clone(), _ => Vec::new() };
                a.extend(b);
                return Ok(Value::Array(a));
            }
            "iter_take" => {
                let a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let n = args.get(1).map(|v| v.to_int()).unwrap_or(0).max(0) as usize;
                return Ok(Value::Array(a.into_iter().take(n).collect()));
            }
            "iter_skip" => {
                let a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let n = args.get(1).map(|v| v.to_int()).unwrap_or(0).max(0) as usize;
                return Ok(Value::Array(a.into_iter().skip(n).collect()));
            }
            "iter_any" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let f = args.get(1).cloned();
                for x in arr {
                    if let Some(Value::Fn { params, body, env, .. }) = &f {
                        if matches!(self.invoke_fn_value(params, body, env.clone(), vec![x])?, Value::Bool(true)) {
                            return Ok(Value::Bool(true));
                        }
                    }
                }
                return Ok(Value::Bool(false));
            }
            "iter_all" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let f = args.get(1).cloned();
                for x in arr {
                    if let Some(Value::Fn { params, body, env, .. }) = &f {
                        if !matches!(self.invoke_fn_value(params, body, env.clone(), vec![x])?, Value::Bool(true)) {
                            return Ok(Value::Bool(false));
                        }
                    }
                }
                return Ok(Value::Bool(true));
            }
            "iter_sum" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let sum: i64 = arr.iter().map(|v| v.to_int()).sum();
                return Ok(Value::Int(sum));
            }
            "iter_product" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let prod: i64 = arr.iter().map(|v| v.to_int()).product();
                return Ok(Value::Int(prod));
            }
            "iter_reverse" => {
                let mut a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                a.reverse();
                return Ok(Value::Array(a));
            }
            "iter_join" => {
                let a   = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let sep = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
                return Ok(Value::Str(parts.join(&sep)));
            }
            "iter_repeat" => {
                let val = args.first().cloned().unwrap_or(Value::Nil);
                let n   = args.get(1).map(|v| v.to_int()).unwrap_or(0).max(0) as usize;
                return Ok(Value::Array(vec![val; n]));
            }
            "iter_unique" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let mut result: Vec<Value> = Vec::new();
                for x in arr {
                    if !result.iter().any(|v| values_equal(v, &x)) {
                        result.push(x);
                    }
                }
                return Ok(Value::Array(result));
            }
            // ── sort (v0.8) ──────────────────────────────────────────────────
            "sort_ints" => {
                let mut arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                arr.sort_by_key(|v| v.to_int());
                return Ok(Value::Array(arr));
            }
            "sort_strings" => {
                let mut arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                arr.sort_by(|a, b| a.to_string().cmp(&b.to_string()));
                return Ok(Value::Array(arr));
            }
            "binary_search" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let target = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                let mut lo: i64 = 0;
                let mut hi: i64 = arr.len() as i64 - 1;
                while lo <= hi {
                    let mid = lo + (hi - lo) / 2;
                    let mid_val = arr[mid as usize].to_int();
                    if mid_val == target { return Ok(Value::Int(mid)); }
                    if mid_val < target { lo = mid + 1; } else { hi = mid - 1; }
                }
                return Ok(Value::Int(-1));
            }
            "binary_search_left" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let target = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                let mut lo: i64 = 0;
                let mut hi: i64 = arr.len() as i64;
                while lo < hi {
                    let mid = lo + (hi - lo) / 2;
                    if arr[mid as usize].to_int() < target { lo = mid + 1; } else { hi = mid; }
                }
                return Ok(Value::Int(lo));
            }
            "min_int" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                return Ok(arr.iter().map(|v| v.to_int()).min().map(Value::Int).unwrap_or(Value::Nil));
            }
            "max_int" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                return Ok(arr.iter().map(|v| v.to_int()).max().map(Value::Int).unwrap_or(Value::Nil));
            }
            "merge_sorted" => {
                let a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let b = match args.get(1) { Some(Value::Array(b)) => b.clone(), _ => Vec::new() };
                let mut result: Vec<Value> = Vec::with_capacity(a.len() + b.len());
                let (mut i, mut j) = (0usize, 0usize);
                while i < a.len() && j < b.len() {
                    if a[i].to_int() <= b[j].to_int() { result.push(a[i].clone()); i += 1; }
                    else { result.push(b[j].clone()); j += 1; }
                }
                result.extend_from_slice(&a[i..]);
                result.extend_from_slice(&b[j..]);
                return Ok(Value::Array(result));
            }
            // ── async (v0.8) — this interpreter's async model runs eagerly
            // (no real cooperative scheduling), so `async::spawn(closure)`
            // simply invokes the closure immediately and wraps its result
            // as a Ready task; `await` on it is then a transparent unwrap.
            // This matches the existing Expr::Await behavior, which already
            // passes non-AsyncTask values through unchanged.
            "async_spawn" => {
                if let Some(Value::Fn { params, body, env, .. }) = args.first().cloned() {
                    let result = self.invoke_fn_value(&params, &body, env, Vec::new())?;
                    return Ok(Value::AsyncTask(Box::new(AsyncTaskState::Ready(result))));
                }
                return Ok(Value::AsyncTask(Box::new(AsyncTaskState::Ready(Value::Nil))));
            }
            "async_timeout" => {
                // args: (timeout_ms, closure) — the timeout itself isn't
                // enforced (no real scheduler/clock-based cancellation in
                // this interpreter); the closure just runs to completion.
                if let Some(Value::Fn { params, body, env, .. }) = args.get(1).cloned() {
                    return self.invoke_fn_value(&params, &body, env, Vec::new());
                }
                return Ok(Value::Nil);
            }
            // ── test / assert (v0.8) — CRITICAL: these were entirely
            // missing before. `assert_eq` etc. fell through to call_fn's
            // catch-all `Ok(Value::Nil)`, meaning every test in the entire
            // suite "passed" unconditionally regardless of whether its
            // assertions were true — the test runner only checks the
            // process exit code, and a silently-ignored assertion never
            // produces a nonzero exit. These builtins raise a real
            // RuntimeError::Panic on failure so a failing assertion
            // actually fails the test (and fails `bytes test`'s
            // `hsharp preview` subprocess check).
            "assert_eq" => {
                let a = args.first().cloned().unwrap_or(Value::Nil);
                let b = args.get(1).cloned().unwrap_or(Value::Nil);
                if !values_equal(&a, &b) {
                    return Err(RuntimeError::Panic(format!(
                        "assert_eq failed:\n  expected: {}\n  actual:   {}", b, a
                    )));
                }
                return Ok(Value::Nil);
            }
            "assert_ne" => {
                let a = args.first().cloned().unwrap_or(Value::Nil);
                let b = args.get(1).cloned().unwrap_or(Value::Nil);
                if values_equal(&a, &b) {
                    return Err(RuntimeError::Panic(format!("assert_ne failed: both equal {}", a)));
                }
                return Ok(Value::Nil);
            }
            "assert_true" => {
                let cond = args.first().cloned().unwrap_or(Value::Bool(false));
                if !matches!(cond, Value::Bool(true)) {
                    return Err(RuntimeError::Panic("assert_true failed: condition was false".into()));
                }
                return Ok(Value::Nil);
            }
            "assert_false" => {
                let cond = args.first().cloned().unwrap_or(Value::Bool(true));
                if matches!(cond, Value::Bool(true)) {
                    return Err(RuntimeError::Panic("assert_false failed: condition was true".into()));
                }
                return Ok(Value::Nil);
            }
            "assert_nil" => {
                let v = args.first().cloned().unwrap_or(Value::Nil);
                if !matches!(v, Value::Nil) {
                    return Err(RuntimeError::Panic(format!("assert_nil failed: got {}", v)));
                }
                return Ok(Value::Nil);
            }
            "assert_not_nil" => {
                let v = args.first().cloned().unwrap_or(Value::Nil);
                if matches!(v, Value::Nil) {
                    return Err(RuntimeError::Panic("assert_not_nil failed: value was nil".into()));
                }
                return Ok(Value::Nil);
            }
            "assert_err" => {
                let v = args.first().cloned().unwrap_or(Value::Nil);
                if !matches!(v, Value::Nil) {
                    return Err(RuntimeError::Panic(format!("assert_err failed: expected error but got {}", v)));
                }
                return Ok(Value::Nil);
            }
            "assert_approx" => {
                let a     = args.first().map(|v| v.to_float()).unwrap_or(0.0);
                let b     = args.get(1).map(|v| v.to_float()).unwrap_or(0.0);
                let delta = args.get(2).map(|v| v.to_float()).unwrap_or(0.0);
                if (a - b).abs() > delta {
                    return Err(RuntimeError::Panic(format!(
                        "assert_approx failed: |{} - {}| = {} > {}", a, b, (a - b).abs(), delta
                    )));
                }
                return Ok(Value::Nil);
            }
            "assert_contains" => {
                let s   = args.first().map(|v| v.to_string()).unwrap_or_default();
                let sub = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if !s.contains(&sub) {
                    return Err(RuntimeError::Panic(format!(
                        "assert_contains failed:\n  string:    {}\n  substring: {}", s, sub
                    )));
                }
                return Ok(Value::Nil);
            }
            "assert_starts_with" => {
                let s      = args.first().map(|v| v.to_string()).unwrap_or_default();
                let prefix = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if !s.starts_with(&prefix) {
                    return Err(RuntimeError::Panic(format!(
                        "assert_starts_with failed:\n  string: {}\n  prefix: {}", s, prefix
                    )));
                }
                return Ok(Value::Nil);
            }
            "assert_len" => {
                let actual = match args.first() {
                    Some(Value::Array(a)) => a.len() as i64,
                    Some(Value::Str(s))   => s.chars().count() as i64,
                    _ => 0,
                };
                let expected = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                if actual != expected {
                    return Err(RuntimeError::Panic(format!(
                        "assert_len failed: expected {}, got {}", expected, actual
                    )));
                }
                return Ok(Value::Nil);
            }
            "fail" => {
                let msg = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Err(RuntimeError::Panic(format!("test failed: {}", msg)));
            }
            "skip" => {
                // Skipping isn't distinguished from passing at this layer
                // (no separate "skipped" exit-code channel) — treat as a
                // no-op success. A real skip-tracking mechanism belongs in
                // the bytes test_runner, which already has its own
                // per-function subprocess invocation it could extend.
                return Ok(Value::Nil);
            }
            "file_size_bytes" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Int(std::fs::metadata(p.as_str()).map(|m| m.len() as i64).unwrap_or(0)));
            }
            "is_dir" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(std::path::Path::new(p.as_str()).is_dir()));
            }
            "file_stem" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Str(std::path::Path::new(p.as_str()).file_stem().and_then(|s| s.to_str()).unwrap_or("").to_string()));
            }
            "file_ext" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Str(std::path::Path::new(p.as_str()).extension().and_then(|s| s.to_str()).unwrap_or("").to_string()));
            }
            "file_parent" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Str(std::path::Path::new(p.as_str()).parent().and_then(|p| p.to_str()).unwrap_or("").to_string()));
            }
            "new_uuid" => {
                let mut b = [0u8; 16];
                if let Ok(mut f) = std::fs::File::open("/dev/urandom") { use std::io::Read; let _ = f.read_exact(&mut b); }
                b[6] = (b[6] & 0x0f) | 0x40;
                b[8] = (b[8] & 0x3f) | 0x80;
                return Ok(Value::Str(format!(
                    "{:02x}{:02x}{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
                    b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],b[8],b[9],b[10],b[11],b[12],b[13],b[14],b[15]
                )));
            }
            "bold"        => { return Ok(Value::Str(format!("\x1b[1m{}\x1b[0m", args.first().map(|v| v.to_string()).unwrap_or_default()))); }
            "green_text"  => { return Ok(Value::Str(format!("\x1b[32m{}\x1b[0m", args.first().map(|v| v.to_string()).unwrap_or_default()))); }
            "red_text"    => { return Ok(Value::Str(format!("\x1b[31m{}\x1b[0m", args.first().map(|v| v.to_string()).unwrap_or_default()))); }
            "yellow_text" => { return Ok(Value::Str(format!("\x1b[33m{}\x1b[0m", args.first().map(|v| v.to_string()).unwrap_or_default()))); }
            "dim_text"    => { return Ok(Value::Str(format!("\x1b[2m{}\x1b[0m",  args.first().map(|v| v.to_string()).unwrap_or_default()))); }
            "dns_resolve" => {
                let host = args.first().map(|v| v.to_string()).unwrap_or_default();
                use std::net::ToSocketAddrs;
                let ip = format!("{}:0", host).to_socket_addrs().ok().and_then(|mut a| a.next()).map(|a| a.ip().to_string()).unwrap_or_default();
                return Ok(Value::Str(ip));
            }
            "scan_port_net" | "scan_port" => {
                let host    = args.first().map(|v| v.to_string()).unwrap_or_default();
                let port    = args.get(1).map(|v| v.to_int()).unwrap_or(80) as u16;
                let timeout = args.get(2).map(|v| v.to_int()).unwrap_or(500) as u64;
                use std::net::TcpStream;
                let addr = format!("{}:{}", host, port);
                let open = addr.parse::<std::net::SocketAddr>()
                    .map(|a| TcpStream::connect_timeout(&a, std::time::Duration::from_millis(timeout)).is_ok())
                    .unwrap_or(false);
                return Ok(Value::Bool(open));
            }
            "sha256" => {
                let data = args.first().map(|v| v.to_string()).unwrap_or_default();
                let mut hasher = Sha256::new();
                Sha2Digest::update(&mut hasher, data.as_bytes());
                let result = hasher.finalize();
                return Ok(Value::Str(result.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            // Real byte-hashing variant — `sha256` above stringifies its
            // argument first (`Value::to_string()`), which for
            // `Value::Bytes` produces the placeholder `"<bytes len=N>"`
            // (see its `Display` impl), not the actual bytes. This exists
            // specifically so `std/crypto.h#`'s `sha256_bytes(data: bytes)`
            // hashes the real byte content instead of that placeholder.
            "sha256_bytes" => {
                let data: Vec<u8> = match args.first() {
                    Some(Value::Bytes(b)) => b.clone(),
                    Some(Value::Str(s)) => s.clone().into_bytes(),
                    _ => Vec::new(),
                };
                let mut hasher = Sha256::new();
                Sha2Digest::update(&mut hasher, &data);
                let result = hasher.finalize();
                return Ok(Value::Str(result.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "sha512" => {
                let data = args.first().map(|v| v.to_string()).unwrap_or_default();
                let mut hasher = Sha512::new();
                Sha2Digest::update(&mut hasher, data.as_bytes());
                let result = hasher.finalize();
                return Ok(Value::Str(result.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "md5" => {
                let data = args.first().map(|v| v.to_string()).unwrap_or_default();
                let mut hasher = Md5::new();
                Sha2Digest::update(&mut hasher, data.as_bytes());
                let result = hasher.finalize();
                return Ok(Value::Str(result.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "sha1" => {
                let data = args.first().map(|v| v.to_string()).unwrap_or_default();
                let mut hasher = Sha1::new();
                Sha2Digest::update(&mut hasher, data.as_bytes());
                let result = hasher.finalize();
                return Ok(Value::Str(result.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "hmac_sha256" => {
                let key = args.first().map(|v| v.to_string()).unwrap_or_default();
                let msg = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let mut mac = <Hmac<Sha256> as Mac>::new_from_slice(key.as_bytes())
                    .expect("HMAC accepts any key length");
                Mac::update(&mut mac, msg.as_bytes());
                let result = mac.finalize().into_bytes();
                return Ok(Value::Str(result.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            // Base64url (no padding) of the *raw* HMAC-SHA256 bytes —
            // added specifically for `std/jwt.h#`'s HS256 signing, which
            // needs the actual binary MAC, not `hmac_sha256`'s hex
            // string (round-tripping hex -> `hex_decode`'s lossy-UTF8
            // string -> base64 would corrupt binary signatures whose
            // bytes aren't valid UTF-8, which is most of them).
            "hmac_sha256_b64url" => {
                let key = args.first().map(|v| v.to_string()).unwrap_or_default();
                let msg = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let mut mac = <Hmac<Sha256> as Mac>::new_from_slice(key.as_bytes())
                    .expect("HMAC accepts any key length");
                Mac::update(&mut mac, msg.as_bytes());
                let raw = mac.finalize().into_bytes();
                let b64 = base64_encode_bytes(&raw);
                let url = b64.replace('+', "-").replace('/', "_").trim_end_matches('=').to_string();
                return Ok(Value::Str(url));
            }
            "hmac_sha512" => {
                let key = args.first().map(|v| v.to_string()).unwrap_or_default();
                let msg = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let mut mac = <Hmac<Sha512> as Mac>::new_from_slice(key.as_bytes())
                    .expect("HMAC accepts any key length");
                Mac::update(&mut mac, msg.as_bytes());
                let result = mac.finalize().into_bytes();
                return Ok(Value::Str(result.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "rot13" => {
                let data = args.first().map(|v| v.to_string()).unwrap_or_default();
                let rotated: String = data.chars().map(|c| {
                    if c.is_ascii_lowercase() {
                        (((c as u8 - b'a' + 13) % 26) + b'a') as char
                    } else if c.is_ascii_uppercase() {
                        (((c as u8 - b'A' + 13) % 26) + b'A') as char
                    } else {
                        c
                    }
                }).collect();
                return Ok(Value::Str(rotated));
            }
            "xor_hex" => {
                let a = args.first().map(|v| v.to_string()).unwrap_or_default();
                let b_s = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let ab: Vec<u8> = (0..a.len()).step_by(2).filter_map(|i| u8::from_str_radix(a.get(i..i+2).unwrap_or(""), 16).ok()).collect();
                let bb: Vec<u8> = (0..b_s.len()).step_by(2).filter_map(|i| u8::from_str_radix(b_s.get(i..i+2).unwrap_or(""), 16).ok()).collect();
                let r: String = ab.iter().zip(bb.iter().cycle()).map(|(x,y)| format!("{:02x}", x^y)).collect();
                return Ok(Value::Str(r));
            }
            // ── array_*/string_* free-function forms ──────────────────────
            // These are the *only* form real-world H# code actually uses
            // (`array_len(x)`, `string_starts_with(s, p)`, ...) — every
            // project of any size uses this style, not `x.len()`/
            // `s.starts_with(p)`. Every single one of these names was
            // completely unimplemented here: `call_method` above has
            // roughly matching logic under different Rust-y names
            // ("to_upper" vs "string_upper", etc), but nothing ever
            // dispatched a free-function call name into it, so *every*
            // call to any of these silently fell through to "Unknown
            // function — return Nil" further down. A real program built
            // around this style — which is to say, virtually any
            // real H# program — doesn't error under `hsharp run`, it just
            // silently computes complete garbage from that point on
            // (`array_len(args)` returning `nil`, then every length check
            // and loop condition derived from it misbehaving) while
            // `hsharp build` (LLVM, with these implemented for real in
            // core.c) works correctly. Semantics below match core.c's
            // hsh_array_*/hsh_string_* exactly (byte-indexed slicing,
            // -1-for-not-found on find/rfind, etc), not just "some
            // reasonable Rust behavior", so a working program shouldn't be
            // able to tell which backend it's running under from these.
            "array_len" | "array_count" => {
                let n = match args.first() { Some(Value::Array(a)) => a.len() as i64, _ => 0 };
                return Ok(Value::Int(n));
            }
            "array_push" => {
                let mut a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                a.push(args.get(1).cloned().unwrap_or(Value::Nil));
                return Ok(Value::Array(a));
            }
            "array_pop" => {
                let mut a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                a.pop();
                return Ok(Value::Array(a));
            }
            "array_get" => {
                let idx = args.get(1).and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None }).unwrap_or(0);
                let v = match args.first() {
                    Some(Value::Array(a)) if idx >= 0 && (idx as usize) < a.len() => a[idx as usize].clone(),
                    _ => Value::Int(0),
                };
                return Ok(v);
            }
            "array_set" => {
                let mut a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let idx = args.get(1).and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None }).unwrap_or(0);
                if idx >= 0 && (idx as usize) < a.len() {
                    a[idx as usize] = args.get(2).cloned().unwrap_or(Value::Nil);
                }
                return Ok(Value::Array(a));
            }
            "array_remove" => {
                let mut a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let idx = args.get(1).and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None }).unwrap_or(0);
                if idx >= 0 && (idx as usize) < a.len() { a.remove(idx as usize); }
                return Ok(Value::Array(a));
            }
            "array_contains" => {
                let target = args.get(1).cloned().unwrap_or(Value::Nil);
                let found = match args.first() {
                    Some(Value::Array(a)) => a.iter().any(|v| v.to_str_val() == target.to_str_val()),
                    _ => false,
                };
                return Ok(Value::Bool(found));
            }
            "array_concat" => {
                let mut a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                if let Some(Value::Array(b)) = args.get(1) { a.extend(b.iter().cloned()); }
                return Ok(Value::Array(a));
            }
            "string_len" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                return Ok(Value::Int(s.len() as i64));
            }
            "string_at" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                let idx = args.get(1).and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None }).unwrap_or(0);
                let ch = if idx >= 0 { s.as_bytes().get(idx as usize) } else { None };
                return Ok(Value::Str(ch.map(|b| (*b as char).to_string()).unwrap_or_default()));
            }
            "string_chars" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                return Ok(Value::Array(s.chars().map(|c| Value::Str(c.to_string())).collect()));
            }
            "string_contains" | "string_contains_str" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                let p = args.get(1).map(|v| v.to_str_val()).unwrap_or_default();
                return Ok(Value::Bool(s.contains(&p)));
            }
            "string_starts_with" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                let p = args.get(1).map(|v| v.to_str_val()).unwrap_or_default();
                return Ok(Value::Bool(s.starts_with(&p)));
            }
            "string_ends_with" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                let p = args.get(1).map(|v| v.to_str_val()).unwrap_or_default();
                return Ok(Value::Bool(s.ends_with(&p)));
            }
            "string_find" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                let p = args.get(1).map(|v| v.to_str_val()).unwrap_or_default();
                return Ok(Value::Int(s.find(&p).map(|i| i as i64).unwrap_or(-1)));
            }
            "string_rfind" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                let p = args.get(1).map(|v| v.to_str_val()).unwrap_or_default();
                return Ok(Value::Int(s.rfind(&p).map(|i| i as i64).unwrap_or(-1)));
            }
            "string_lower" | "string_to_lower" => {
                return Ok(Value::Str(args.first().map(|v| v.to_str_val()).unwrap_or_default().to_lowercase()));
            }
            "string_upper" | "string_to_upper" => {
                return Ok(Value::Str(args.first().map(|v| v.to_str_val()).unwrap_or_default().to_uppercase()));
            }
            "string_trim" => {
                return Ok(Value::Str(args.first().map(|v| v.to_str_val()).unwrap_or_default().trim().to_string()));
            }
            "string_trim_right" => {
                return Ok(Value::Str(args.first().map(|v| v.to_str_val()).unwrap_or_default().trim_end().to_string()));
            }
            "string_pad_right" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                let width = args.get(1).and_then(|v| if let Value::Int(n) = v { Some(*n as usize) } else { None }).unwrap_or(0);
                let mut s = s;
                if s.len() < width { s.push_str(&" ".repeat(width - s.len())); }
                return Ok(Value::Str(s));
            }
            "string_repeat" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                let n = args.get(1).and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None }).unwrap_or(0);
                return Ok(Value::Str(if n > 0 { s.repeat(n as usize) } else { String::new() }));
            }
            "string_replace" | "string_replace_all" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                let from = args.get(1).map(|v| v.to_str_val()).unwrap_or_default();
                let to = args.get(2).map(|v| v.to_str_val()).unwrap_or_default();
                return Ok(Value::Str(s.replace(&from, &to)));
            }
            "string_split" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                let sep = args.get(1).map(|v| v.to_str_val()).unwrap_or_default();
                let parts: Vec<Value> = if sep.is_empty() {
                    s.chars().map(|c| Value::Str(c.to_string())).collect()
                } else {
                    s.split(sep.as_str()).map(|p| Value::Str(p.to_string())).collect()
                };
                return Ok(Value::Array(parts));
            }
            "string_slice" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                let bytes = s.as_bytes();
                let slen = bytes.len() as i64;
                let mut start = args.get(1).and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None }).unwrap_or(0);
                let mut end = args.get(2).and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None }).unwrap_or(slen);
                if start < 0 { start = 0; }
                if end > slen { end = slen; }
                if start >= end { return Ok(Value::Str(String::new())); }
                let out = String::from_utf8_lossy(&bytes[start as usize..end as usize]).to_string();
                return Ok(Value::Str(out));
            }
            "string_to_bytes" => {
                let s = args.first().map(|v| v.to_str_val()).unwrap_or_default();
                return Ok(Value::Bytes(s.into_bytes()));
            }
            // Lossy inverse of `string_to_bytes` — needed by
            // `std/msgpack.h#`'s decoder, which reconstructs a `bytes`
            // value from raw `[int]`s via `bytes_from_ints` and then
            // needs it back as a `string` for the caller.
            "bytes_to_string" => {
                let b = match args.first() { Some(Value::Bytes(b)) => b.clone(), _ => Vec::new() };
                return Ok(Value::Str(String::from_utf8_lossy(&b).to_string()));
            }
            // ── end array_*/string_* free-function forms ──────────────────
            // These have no interpreter implementation: `hsharp run` is a
            // tree-walking interpreter with no addressable-memory or
            // manual-refcounting model at all, while `hsharp build` (LLVM)
            // implements them for real (see codegen.rs/core.c). Previously
            // calling one of these here silently fell through to "Unknown
            // function — return Nil" below, so e.g. `arc_alloc(8)` quietly
            // became `Nil` instead of erroring — the same `@arc`/`@pointers`
            // source file could run "successfully" under `hsharp run` while
            // doing nothing at all, and only work correctly under
            // `hsharp build`. A clear error here at least makes that
            // divergence visible instead of silently wrong.
            "arc_alloc" | "arc_retain" | "arc_release" | "arc_count" |
            "arc_downgrade" | "arc_upgrade" | "arc_weak_release" | "arc_weak_count" |
            "ptr_read_i64" | "ptr_write_i64" | "ptr_read_i32" | "ptr_write_i32" |
            "ptr_read_i16" | "ptr_write_i16" | "ptr_read_i8"  | "ptr_write_i8"  |
            "ptr_read_f64" | "ptr_write_f64" | "ptr_read_f32" | "ptr_write_f32" |
            "ptr_read_ptr" | "ptr_write_ptr" | "ptr_add" | "ptr_is_null" |
            "ptr_alloc_size" | "ptr_copy" | "ptr_compare" | "ptr_field_offset" |
            "ptr_read_checked" | "ptr_write_checked" | "ptr_fill" | "ptr_zero" => {
                return Err(RuntimeError::TypeError(format!(
                    "`{}` is an `@arc`/`@pointers` raw-memory builtin implemented only for the LLVM backend — the interpreter (`hsharp run`) has no addressable-memory model to back it with; compile with `hsharp build` instead",
                    name
                )));
            }
            // `@arena` checkpoint/rewind/stats (see core.c's
            // hsh_arena_checkpoint doc comment): unlike the ptr_*/arc_*
            // builtins above, these have a well-defined, genuinely
            // consistent meaning even with no arena backing them —
            // core.c's own versions are already no-ops ("checkpoint" is
            // 0, "rewind" does nothing, "used"/"capacity" are 0) whenever
            // no arena is active, and the interpreter never has one
            // active at all. True no-op stubs here match the real
            // backend's own no-arena behavior exactly, rather than
            // needing a "LLVM only" error — there's no silent-wrongness
            // risk the way there is for arc_alloc returning a fake `Nil`
            // pointer that then gets dereferenced.
            "arena_checkpoint" | "arena_used" | "arena_capacity" => {
                return Ok(Value::Int(0));
            }
            "arena_rewind" => {
                return Ok(Value::Nil);
            }
            // ── end real stdlib ─────────────────────────────────────────
            _ => {}
        }

        // User-defined functions
        if let Some(f) = self.fns.get(name).cloned() {
            // `@arena`/`@safety` are LLVM-codegen-only behaviors (bump
            // allocation, and the straight-line move-after-use checker,
            // respectively) — the interpreter runs the body exactly like
            // `@default` either way. That's fine for `@arena` (same
            // observable result, just heap-allocated instead of arena-
            // allocated) but means a `@safety` violation that codegen
            // would at least warn about is completely silent here. A
            // one-time-per-function note makes that gap visible instead
            // of `hsharp run` and `hsharp build` silently diverging.
            if matches!(f.mem_mode, MemoryMode::Safety | MemoryMode::Arena)
                && self.mem_mode_notes_given.insert(f.name.clone())
            {
                match f.mem_mode {
                    MemoryMode::Safety => eprintln!(
                        "note: `{}` is `@safety`, but the interpreter (`hsharp run`) doesn't run the move-after-use checker — that only happens in `hsharp build`'s LLVM codegen",
                        f.name
                    ),
                    MemoryMode::Arena => eprintln!(
                        "note: `{}` is `@arena`, but the interpreter (`hsharp run`) allocates its values normally — arena bump-allocation only happens in `hsharp build`'s LLVM codegen; observable behavior is the same, just not the performance characteristic",
                        f.name
                    ),
                    _ => unreachable!(),
                }
            }
            // Monomorphize generic functions at call site
            let f = if !f.type_params.is_empty() {
                // Build type substitution from actual argument types
                let mut subst = std::collections::HashMap::new();
                for (tp, val) in f.type_params.iter().zip(args.iter()) {
                    let concrete_ty = match val {
                        Value::Int(_)   => hsharp_parser::ast::TypeExpr::Named("int".into()),
                        Value::Float(_) => hsharp_parser::ast::TypeExpr::Named("float".into()),
                        Value::Str(_)   => hsharp_parser::ast::TypeExpr::Named("string".into()),
                        Value::Bool(_)  => hsharp_parser::ast::TypeExpr::Named("bool".into()),
                        Value::Array(_) => hsharp_parser::ast::TypeExpr::Array(Box::new(hsharp_parser::ast::TypeExpr::Named("any".into()))),
                        _               => hsharp_parser::ast::TypeExpr::Named("any".into()),
                    };
                    subst.insert(tp.name.clone(), concrete_ty);
                }
                crate::value::mono_fn_inline(&f, &subst)
            } else {
                f
            };
            self.env.push();
            for (param, val) in f.params.iter().zip(args) {
                self.env.define(&param.name, val, param.mutable);
            }
            let result = self.exec_block(&f.body)?;
            self.env.pop();
            let resolved = match result {
                Some(Value::Return(v)) => *v,
                Some(v) => v,
                None => Value::Nil,
            };
            // If function is async, wrap in AsyncTask::Ready
            if f.is_async {
                return Ok(Value::AsyncTask(Box::new(AsyncTaskState::Ready(resolved))));
            }
            return Ok(resolved);
        }
        // Unknown function — return Nil (or could return error)
        Ok(Value::Nil)


    }

    pub fn call_method(&mut self, obj: Value, method: &str, args: Vec<Value>) -> Result<Value, RuntimeError> {
        // User-defined `impl Type is fn method(self, ...) ... end` methods
        // take priority over the builtin method table below — this is what
        // makes `point.distance_to(other)`, custom `HashMap`-style structs,
        // etc. actually execute real H# code instead of always falling
        // through to the generic struct-field lookup. Mutation of `self`
        // inside the method is discarded here (no receiver binding to write
        // back to) — see `Expr::MethodCall` in `eval_expr` for the path
        // that *does* propagate self-mutation back to a named variable.
        if matches!(obj, Value::Struct { .. }) {
            if let Some(result) = self.try_user_method(&obj, method, &args) {
                return result.map(|(ret, _mutated_self)| ret);
            }
        }

        let arg0_str = || args.first().and_then(|v| if let Value::Str(s) = v { Some(s.clone()) } else { None }).unwrap_or_default();
        let arg0_int = || args.first().and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None }).unwrap_or(0);

        match (&obj, method) {
            // ── String methods ────────────────────────────────────────────────
            (Value::Str(s), "len")          => Ok(Value::Int(s.len() as i64)),
            (Value::Str(s), "to_upper")     => Ok(Value::Str(s.to_uppercase())),
            (Value::Str(s), "to_uppercase") => Ok(Value::Str(s.to_uppercase())),
            (Value::Str(s), "to_lower")     => Ok(Value::Str(s.to_lowercase())),
            (Value::Str(s), "to_lowercase") => Ok(Value::Str(s.to_lowercase())),
            (Value::Str(s), "trim")         => Ok(Value::Str(s.trim().to_string())),
            (Value::Str(s), "trim_start")   => Ok(Value::Str(s.trim_start().to_string())),
            (Value::Str(s), "trim_end")     => Ok(Value::Str(s.trim_end().to_string())),
            (Value::Str(s), "to_string")    => Ok(Value::Str(s.clone())),
            (Value::Str(s), "is_empty")     => Ok(Value::Bool(s.is_empty())),
            (Value::Str(s), "reverse") => {
                Ok(Value::Str(s.chars().rev().collect()))
            }
            (Value::Str(s), "contains") => {
                let pat = arg0_str();
                Ok(Value::Bool(s.contains(pat.as_str())))
            }
            (Value::Str(s), "starts_with") => {
                let pat = arg0_str();
                Ok(Value::Bool(s.starts_with(pat.as_str())))
            }
            (Value::Str(s), "ends_with") => {
                let pat = arg0_str();
                Ok(Value::Bool(s.ends_with(pat.as_str())))
            }
            (Value::Str(s), "split") => {
                let sep = arg0_str();
                Ok(Value::Array(s.split(sep.as_str()).map(|p| Value::Str(p.to_string())).collect()))
            }
            (Value::Str(s), "replace") => {
                let from = arg0_str();
                let to = args.get(1).and_then(|v| if let Value::Str(s) = v { Some(s.clone()) } else { None }).unwrap_or_default();
                Ok(Value::Str(s.replace(from.as_str(), to.as_str())))
            }
            (Value::Str(s), "replace_all") => {
                let from = arg0_str();
                let to = args.get(1).and_then(|v| if let Value::Str(s) = v { Some(s.clone()) } else { None }).unwrap_or_default();
                Ok(Value::Str(s.replace(from.as_str(), to.as_str())))
            }
            (Value::Str(s), "index_of") => {
                let sub = arg0_str();
                match s.find(sub.as_str()) {
                    Some(i) => Ok(Value::Int(i as i64)),
                    None => Ok(Value::Int(-1)),
                }
            }
            (Value::Str(s), "count") => {
                let sub = arg0_str();
                Ok(Value::Int(s.matches(sub.as_str()).count() as i64))
            }
            (Value::Str(s), "chars") => {
                Ok(Value::Array(s.chars().map(|c| Value::Str(c.to_string())).collect()))
            }
            (Value::Str(s), "bytes") => {
                Ok(Value::Bytes(s.as_bytes().to_vec()))
            }
            (Value::Str(s), "parse_int") => {
                s.trim().parse::<i64>()
                    .map(Value::Int)
                    .map_err(|_| RuntimeError::TypeError(format!("cannot parse int from '{}'", s)))
            }
            (Value::Str(s), "parse_float") => {
                s.trim().parse::<f64>()
                    .map(Value::Float)
                    .map_err(|_| RuntimeError::TypeError(format!("cannot parse float from '{}'", s)))
            }
            (Value::Str(s), "repeat") => {
                let n = arg0_int() as usize;
                Ok(Value::Str(s.repeat(n)))
            }
            // ── Array methods ─────────────────────────────────────────────────
            (Value::Array(arr), "len")     => Ok(Value::Int(arr.len() as i64)),
            (Value::Array(arr), "first")   => Ok(arr.first().cloned().unwrap_or(Value::Nil)),
            (Value::Array(arr), "last")    => Ok(arr.last().cloned().unwrap_or(Value::Nil)),
            (Value::Array(arr), "is_empty") => Ok(Value::Bool(arr.is_empty())),
            (Value::Array(arr), "contains") => {
                let target = args.first().cloned().unwrap_or(Value::Nil);
                Ok(Value::Bool(arr.iter().any(|v| values_equal(v, &target))))
            }
            (Value::Array(arr), "reverse") => {
                let mut rev = arr.clone();
                rev.reverse();
                Ok(Value::Array(rev))
            }
            (Value::Array(arr), "join") => {
                let sep = arg0_str();
                let parts: Vec<String> = arr.iter().map(|v| v.to_str_val()).collect();
                Ok(Value::Str(parts.join(sep.as_str())))
            }
            (Value::Array(_), "push") => {
                // push mutates — handled by caller via assign; here we just
                // return the value pushed (the interpreter special-cases mutations)
                Ok(args.first().cloned().unwrap_or(Value::Nil))
            }
            // ── Bytes methods ─────────────────────────────────────────────────
            (Value::Bytes(b), "len") => Ok(Value::Int(b.len() as i64)),
            (Value::Bytes(b), "to_hex") => {
                Ok(Value::Str(b.iter().map(|byte| format!("{:02x}", byte)).collect()))
            }
            (Value::Bytes(b), "to_string") => {
                Ok(Value::Str(String::from_utf8_lossy(b).to_string()))
            }
            (Value::Bytes(b), "is_empty") => Ok(Value::Bool(b.is_empty())),
            // ── Primitive to_string ───────────────────────────────────────────
            (Value::Int(n), "to_string")   => Ok(Value::Str(n.to_string())),
            (Value::Float(f), "to_string") => Ok(Value::Str(f.to_string())),
            (Value::Bool(b), "to_string")  => Ok(Value::Str(b.to_string())),
            (Value::Nil, "to_string")      => Ok(Value::Str("nil".to_string())),
            // ── HashMap (v0.8) — read-only methods (mutation handled via
            // compute_mutated_container in the MethodCall write-back path) ──
            (Value::Struct { name, fields }, "get") if name == "__hashmap" => {
                let key = arg0_str();
                Ok(fields.get(&key).cloned().unwrap_or(Value::Nil))
            }
            (Value::Struct { name, fields }, "contains_key") if name == "__hashmap" => {
                let key = arg0_str();
                Ok(Value::Bool(fields.contains_key(&key)))
            }
            (Value::Struct { name, fields }, "len") if name == "__hashmap" => {
                Ok(Value::Int(fields.len() as i64))
            }
            (Value::Struct { name, fields }, "is_empty") if name == "__hashmap" => {
                Ok(Value::Bool(fields.is_empty()))
            }
            (Value::Struct { name, fields }, "keys") if name == "__hashmap" => {
                Ok(Value::Array(fields.keys().map(|k| Value::Str(k.clone())).collect()))
            }
            (Value::Struct { name, fields }, "values") if name == "__hashmap" => {
                Ok(Value::Array(fields.values().cloned().collect()))
            }
            (Value::Struct { name, .. }, "insert") if name == "__hashmap" => {
                // Mutation is applied via compute_mutated_container's
                // write-back; `insert` itself doesn't return a useful value.
                Ok(Value::Nil)
            }
            (Value::Struct { name, .. }, "remove") if name == "__hashmap" => {
                Ok(Value::Nil)
            }
            // ── HashSet (v0.8) ─────────────────────────────────────────────────
            (Value::Struct { name, .. }, "insert") if name == "__hashset" => {
                Ok(Value::Nil)
            }
            (Value::Struct { name, .. }, "remove") if name == "__hashset" => {
                Ok(Value::Nil)
            }
            (Value::Struct { name, fields }, "contains") if name == "__hashset" => {
                let target = args.first().cloned().unwrap_or(Value::Nil);
                let items = match fields.get("items") { Some(Value::Array(a)) => a, _ => return Ok(Value::Bool(false)) };
                Ok(Value::Bool(items.iter().any(|v| values_equal(v, &target))))
            }
            (Value::Struct { name, fields }, "len") if name == "__hashset" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(Value::Int(a.len() as i64)),
                    _ => Ok(Value::Int(0)),
                }
            }
            (Value::Struct { name, fields }, "is_empty") if name == "__hashset" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(Value::Bool(a.is_empty())),
                    _ => Ok(Value::Bool(true)),
                }
            }
            (Value::Struct { name, fields }, "to_array") if name == "__hashset" => {
                Ok(fields.get("items").cloned().unwrap_or(Value::Array(Vec::new())))
            }
            // ── Queue / Stack (v0.8) — shared read-only methods ─────────────────
            (Value::Struct { name, fields }, "len") if name == "__queue" || name == "__stack" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(Value::Int(a.len() as i64)),
                    _ => Ok(Value::Int(0)),
                }
            }
            (Value::Struct { name, fields }, "is_empty") if name == "__queue" || name == "__stack" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(Value::Bool(a.is_empty())),
                    _ => Ok(Value::Bool(true)),
                }
            }
            (Value::Struct { name, fields }, "peek") if name == "__queue" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(a.first().cloned().unwrap_or(Value::Nil)),
                    _ => Ok(Value::Nil),
                }
            }
            (Value::Struct { name, fields }, "peek") if name == "__stack" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(a.last().cloned().unwrap_or(Value::Nil)),
                    _ => Ok(Value::Nil),
                }
            }
            // `pop`'s *return value* for queue/stack: the write-back of the
            // shrunk container happens separately in compute_mutated_container;
            // here we just report what *would be / was* removed.
            (Value::Struct { name, fields }, "pop") if name == "__queue" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(a.first().cloned().unwrap_or(Value::Nil)),
                    _ => Ok(Value::Nil),
                }
            }
            (Value::Struct { name, fields }, "pop") if name == "__stack" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(a.last().cloned().unwrap_or(Value::Nil)),
                    _ => Ok(Value::Nil),
                }
            }
            (Value::Struct { name, .. }, "push") if name == "__queue" || name == "__stack" => {
                // The pushed value is the expression's result, matching
                // Array's push semantics; the actual mutation/write-back
                // happens in compute_mutated_container.
                Ok(args.first().cloned().unwrap_or(Value::Nil))
            }
            // ── Struct field dispatch ─────────────────────────────────────────
            (Value::Struct { fields, .. }, _) => {
                if let Some(v) = fields.get(method) {
                    Ok(v.clone())
                } else {
                    Err(RuntimeError::TypeError(format!("no method or field `{}` on struct", method)))
                }
            }
            _ => Err(RuntimeError::TypeError(format!("no method `{}` on {}", method, obj))),
        }
    }

    pub fn eval_binop(&self, l: Value, op: &BinOp, r: Value) -> Result<Value, RuntimeError> {
        match op {
            BinOp::Add => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_add(b))),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
                (Value::Int(a), Value::Float(b)) => Ok(Value::Float(a as f64 + b)),
                (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a + b as f64)),
                (Value::Str(a), Value::Str(b)) => Ok(Value::Str(a + &b)),
                (l, r) => Err(RuntimeError::TypeError(format!("cannot add {} and {}", l, r))),
            },
            BinOp::Sub => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_sub(b))),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
                (l, r) => Err(RuntimeError::TypeError(format!("cannot subtract {} and {}", l, r))),
            },
            BinOp::Mul => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_mul(b))),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
                (l, r) => Err(RuntimeError::TypeError(format!("cannot multiply {} and {}", l, r))),
            },
            BinOp::Div => match (l, r) {
                (Value::Int(a), Value::Int(b)) => {
                    if b == 0 { Err(RuntimeError::DivisionByZero) }
                    else { Ok(Value::Int(a / b)) }
                },
                (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
                (l, r) => Err(RuntimeError::TypeError(format!("cannot divide {} and {}", l, r))),
            },
            BinOp::Mod => match (l, r) {
                (Value::Int(a), Value::Int(b)) => {
                    if b == 0 { Err(RuntimeError::DivisionByZero) }
                    else { Ok(Value::Int(a % b)) }
                },
                (l, r) => Err(RuntimeError::TypeError(format!("cannot mod {} and {}", l, r))),
            },
            BinOp::Eq => Ok(Value::Bool(values_equal(&l, &r))),
            BinOp::NotEq => Ok(Value::Bool(!values_equal(&l, &r))),
            BinOp::Lt => compare_values(l, r, |ord| ord == std::cmp::Ordering::Less),
            BinOp::Gt => compare_values(l, r, |ord| ord == std::cmp::Ordering::Greater),
            BinOp::LtEq => compare_values(l, r, |ord| ord != std::cmp::Ordering::Greater),
            BinOp::GtEq => compare_values(l, r, |ord| ord != std::cmp::Ordering::Less),
            BinOp::And => Ok(Value::Bool(l.is_truthy() && r.is_truthy())),
            BinOp::Or => Ok(if l.is_truthy() { l } else { r }),
            BinOp::BitAnd => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a & b)),
                _ => Err(RuntimeError::TypeError("bitwise & requires integers".into())),
            },
            BinOp::BitOr => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a | b)),
                _ => Err(RuntimeError::TypeError("bitwise | requires integers".into())),
            },
            BinOp::BitXor => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a ^ b)),
                _ => Err(RuntimeError::TypeError("bitwise ^ requires integers".into())),
            },
            BinOp::Shl => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a << b)),
                _ => Err(RuntimeError::TypeError("<< requires integers".into())),
            },
            BinOp::Shr => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a >> b)),
                _ => Err(RuntimeError::TypeError(">> requires integers".into())),
            },
        }
    }

    pub fn pattern_matches(&self, pat: &Pattern, val: &Value) -> bool {
        match pat {
            Pattern::Wildcard(_) => true,
            // A bare identifier pattern always matches (and binds) UNLESS
            // it happens to name a known unit variant of an enum the
            // value belongs to — this supports the common style of
            // writing unit variants without `Type::` qualification or
            // parens, e.g. `match status is Ok => ... Error(msg) => ... end`.
            // Most of the time `name` is just a binding, so the variant
            // check only applies when the value is actually a
            // `Type::Variant`-shaped struct and `name` matches its bare
            // variant name.
            Pattern::Ident(name, _) => {
                if let Value::Struct { name: type_variant, .. } = val {
                    if let Some((_, variant)) = type_variant.split_once("::") {
                        if variant == name { return true; }
                        // A different variant of (presumably) the same
                        // enum — an Ident pattern shouldn't blanket-match
                        // every enum value, only ones whose variant name
                        // it doesn't otherwise look like it's trying to
                        // exclude. Since Ident patterns are also plain
                        // bindings, fall through to true here too — H#
                        // doesn't track enum exhaustiveness strictly
                        // enough at the interpreter level to disambiguate
                        // "binding to any value" vs "matching a wrong
                        // variant name that happens to look like one";
                        // the typechecker's exhaustiveness pass is the
                        // proper place for that warning.
                    }
                }
                true
            }
            Pattern::Literal(lit, _) => match (lit, val) {
                (Literal::Int(a), Value::Int(b)) => a == b,
                (Literal::Float(a), Value::Float(b)) => (a - b).abs() < f64::EPSILON,
                (Literal::Bool(a), Value::Bool(b)) => a == b,
                (Literal::String(a), Value::Str(b)) => a == b,
                (Literal::Nil, Value::Nil) => true,
                _ => false,
            },
            Pattern::Or(pats, _) => pats.iter().any(|p| self.pattern_matches(p, val)),
            Pattern::Enum { qualified_type, variant, inner, .. } => {
                let Value::Struct { name: type_variant, fields } = val else { return false; };
                let actual_variant = type_variant.split_once("::").map(|(_, v)| v).unwrap_or(type_variant.as_str());
                let actual_type    = type_variant.split_once("::").map(|(t, _)| t);
                if actual_variant != variant { return false; }
                if let Some(qt) = qualified_type {
                    if actual_type != Some(qt.as_str()) { return false; }
                }
                if inner.is_empty() { return true; }
                inner.iter().enumerate().all(|(i, p)| {
                    match fields.get(&i.to_string()) {
                        Some(v) => self.pattern_matches(p, v),
                        None => false,
                    }
                })
            }
            Pattern::Tuple(pats, _) => {
                let Value::Tuple(items) = val else { return false; };
                if pats.len() != items.len() { return false; }
                pats.iter().zip(items.iter()).all(|(p, v)| self.pattern_matches(p, v))
            }
            Pattern::Struct { fields: pat_fields, .. } => {
                let Value::Struct { fields, .. } = val else { return false; };
                pat_fields.iter().all(|(fname, fpat)| {
                    match fields.get(fname) {
                        Some(v) => self.pattern_matches(fpat, v),
                        None => false,
                    }
                })
            }
            Pattern::Range(lo, hi, inclusive, _) => {
                let (Pattern::Literal(Literal::Int(lo), _), Pattern::Literal(Literal::Int(hi), _)) = (lo.as_ref(), hi.as_ref()) else {
                    return false;
                };
                match val {
                    Value::Int(n) => if *inclusive { *n >= *lo && *n <= *hi } else { *n >= *lo && *n < *hi },
                    _ => false,
                }
            }
        }
    }

    pub fn bind_pattern(&mut self, pat: &Pattern, val: Value) {
        match pat {
            Pattern::Ident(name, _) => {
                if name != "_" {
                    self.env.define(name, val, false);
                }
            }
            Pattern::Enum { inner, .. } => {
                if let Value::Struct { fields, .. } = &val {
                    for (i, p) in inner.iter().enumerate() {
                        if let Some(v) = fields.get(&i.to_string()) {
                            self.bind_pattern(p, v.clone());
                        }
                    }
                }
            }
            Pattern::Tuple(pats, _) => {
                if let Value::Tuple(items) = &val {
                    for (p, v) in pats.iter().zip(items.iter()) {
                        self.bind_pattern(p, v.clone());
                    }
                }
            }
            Pattern::Struct { fields: pat_fields, .. } => {
                if let Value::Struct { fields, .. } = &val {
                    for (fname, fpat) in pat_fields {
                        if let Some(v) = fields.get(fname) {
                            self.bind_pattern(fpat, v.clone());
                        }
                    }
                }
            }
            Pattern::Or(pats, _) => {
                // Bind using whichever alternative actually matched.
                if let Some(p) = pats.iter().find(|p| self.pattern_matches(p, &val)) {
                    self.bind_pattern(p, val);
                }
            }
            Pattern::Wildcard(_) | Pattern::Literal(_, _) | Pattern::Range(_, _, _, _) => {}
        }
    }

    pub fn get_stdout(&self) -> &str {
        &self.stdout
    }

    /// Assign `val` into the place described by `lhs`.
    ///
    /// Generalized (was previously `Expr::Ident`-only for the *base* of
    /// each case — `arr[i]` worked but `matrix[i][j]` or `obj.a.b` did
    /// not, since e.g. `IndexAccess`'s array sub-expression had to
    /// literally be an `Ident`) to recurse: evaluate the immediate
    /// container, mutate the one element/field being assigned, then
    /// call `assign_lhs` again on the *sub*-expression to write that
    /// mutated container back wherever it actually lives — which is
    /// exactly the same "value types, no shared references" situation
    /// every other write-back in this file (`MethodCall`,
    /// `sort::sort_ints`, ...) already has to work around, just applied
    /// one level at a time until it bottoms out at a plain `Ident`.
    pub fn assign_lhs(&mut self, lhs: &Expr, val: Value) -> Result<(), RuntimeError> {
        match lhs {
            Expr::Ident(name, _) => {
                if !self.env.set(name, val) {
                    return Err(RuntimeError::ImmutableAssign(name.clone()));
                }
                Ok(())
            }
            Expr::IndexAccess(arr_expr, idx_expr, _) => {
                let idx = match self.eval_expr(idx_expr)? {
                    Value::Int(i) => i as usize,
                    _ => return Err(RuntimeError::TypeError("index must be int".into())),
                };
                let container = self.eval_expr(arr_expr)?;
                match container {
                    Value::Array(mut arr) => {
                        if idx >= arr.len() {
                            return Err(RuntimeError::IndexOutOfBounds(idx as i64, arr.len()));
                        }
                        arr[idx] = val;
                        self.assign_lhs(arr_expr, Value::Array(arr))
                    }
                    _ => Err(RuntimeError::TypeError("cannot index-assign".into())),
                }
            }
            Expr::FieldAccess(obj_expr, field, _) => {
                let container = self.eval_expr(obj_expr)?;
                match container {
                    Value::Struct { name: sname, mut fields } => {
                        fields.insert(field.clone(), val);
                        self.assign_lhs(obj_expr, Value::Struct { name: sname, fields })
                    }
                    _ => Err(RuntimeError::TypeError("cannot field-assign".into())),
                }
            }
            _ => Err(RuntimeError::TypeError("invalid assignment target".into())),
        }
    }
}

// ─── free-function helpers backing the builtins above ──────────────────────
// Kept outside `impl Interpreter` since they're pure functions of their
// arguments with no interpreter state involved.

/// RFC 4648 standard base64 alphabet, `=` padded.
fn base64_encode_bytes(data: &[u8]) -> String {
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity((data.len() + 2) / 3 * 4);
    for chunk in data.chunks(3) {
        let b0 = chunk[0];
        let b1 = *chunk.get(1).unwrap_or(&0);
        let b2 = *chunk.get(2).unwrap_or(&0);
        let n = ((b0 as u32) << 16) | ((b1 as u32) << 8) | (b2 as u32);
        out.push(ALPHABET[((n >> 18) & 0x3f) as usize] as char);
        out.push(ALPHABET[((n >> 12) & 0x3f) as usize] as char);
        out.push(if chunk.len() > 1 { ALPHABET[((n >> 6) & 0x3f) as usize] as char } else { '=' });
        out.push(if chunk.len() > 2 { ALPHABET[(n & 0x3f) as usize] as char } else { '=' });
    }
    out
}

fn base64_decode_str(s: &str) -> Option<Vec<u8>> {
    fn val(c: u8) -> Option<u32> {
        match c {
            b'A'..=b'Z' => Some((c - b'A') as u32),
            b'a'..=b'z' => Some((c - b'a' + 26) as u32),
            b'0'..=b'9' => Some((c - b'0' + 52) as u32),
            b'+' => Some(62),
            b'/' => Some(63),
            _ => None,
        }
    }
    let clean: Vec<u8> = s.bytes().filter(|&b| b != b'=' && !b.is_ascii_whitespace()).collect();
    let mut out = Vec::with_capacity(clean.len() / 4 * 3 + 3);
    for chunk in clean.chunks(4) {
        let vals: Vec<u32> = chunk.iter().map(|&c| val(c)).collect::<Option<Vec<_>>>()?;
        let n = vals.iter().enumerate().fold(0u32, |acc, (i, v)| acc | (v << (18 - 6 * i)));
        out.push(((n >> 16) & 0xff) as u8);
        if vals.len() > 2 { out.push(((n >> 8) & 0xff) as u8); }
        if vals.len() > 3 { out.push((n & 0xff) as u8); }
    }
    Some(out)
}

/// Howard Hinnant's `civil_from_days` (public domain —
/// http://howardhinnant.github.io/date_algorithms.html), adapted to take
/// a unix timestamp directly. Returns `(year, month, day, days_since_epoch_mod_7)`;
/// the last field is used by `date_weekday` (1970-01-01 was a Thursday,
/// which is why that lookup table there starts at "Thu").
fn civil_from_unix(ts: i64) -> (i64, i64, i64, i64) {
    let z = ts.div_euclid(86400) + 719468;
    let era = if z >= 0 { z } else { z - 146096 } / 146097;
    let doe = (z - era * 146097) as i64; // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365; // [0, 399]
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let d = doy - (153 * mp + 2) / 5 + 1; // [1, 31]
    let m = if mp < 10 { mp + 3 } else { mp - 9 }; // [1, 12]
    let year = if m <= 2 { y + 1 } else { y };
    (year, m, d, ts.div_euclid(86400))
}

/// Real (plain-HTTP-only — no TLS) HTTP/1.1 request over a raw
/// `TcpStream`. Returns a `Value::Struct { name: "__http_response",
/// fields: {status: Int, body: Str} }` — deliberately not `Value::Nil`
/// on failure, since "connection refused" and "200 OK with an empty
/// body" need to stay distinguishable to the H# caller (status 0 means
/// the request itself failed, not that the server returned nothing).
fn http_request(method: &str, url: &str, body: &str) -> Value {
    fn make(status: i64, body: &str) -> Value {
        let mut fields = HashMap::new();
        fields.insert("status".to_string(), Value::Int(status));
        fields.insert("body".to_string(), Value::Str(body.to_string()));
        Value::Struct { name: "__http_response".to_string(), fields }
    }

    let rest = match url.strip_prefix("http://") {
        Some(r) => r,
        None if url.starts_with("https://") => {
            return make(0, "https:// is not supported — this runtime has no TLS backend, use http:// or a reverse proxy");
        }
        None => url,
    };
    let (host_port, path) = match rest.find('/') {
        Some(i) => (&rest[..i], &rest[i..]),
        None => (rest, "/"),
    };
    let (host, port) = match host_port.split_once(':') {
        Some((h, p)) => (h, p.parse::<u16>().unwrap_or(80)),
        None => (host_port, 80),
    };

    let addr = format!("{host}:{port}");
    let sock_addr = match addr.to_socket_addrs().ok().and_then(|mut it| it.next()) {
        Some(a) => a,
        None => return make(0, "DNS resolution failed"),
    };
    let mut stream = match std::net::TcpStream::connect_timeout(&sock_addr, std::time::Duration::from_secs(10)) {
        Ok(s) => s,
        Err(e) => return make(0, &format!("connection failed: {e}")),
    };
    let _ = stream.set_read_timeout(Some(std::time::Duration::from_secs(10)));

    use std::io::{Read, Write};
    let request = if body.is_empty() {
        format!("{method} {path} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\nUser-Agent: hsharp\r\n\r\n")
    } else {
        format!(
            "{method} {path} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\nUser-Agent: hsharp\r\nContent-Length: {}\r\n\r\n{body}",
            body.len()
        )
    };
    if let Err(e) = stream.write_all(request.as_bytes()) {
        return make(0, &format!("write failed: {e}"));
    }

    let mut raw = Vec::new();
    if let Err(e) = stream.read_to_end(&mut raw) {
        return make(0, &format!("read failed: {e}"));
    }
    let text = String::from_utf8_lossy(&raw).to_string();

    let status = text
        .lines()
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .and_then(|code| code.parse::<i64>().ok())
        .unwrap_or(0);

    // Split headers from body at the first blank line. Deliberately does
    // NOT decode chunked transfer-encoding — a real gap, documented on
    // the std/http.h#/std/net_http.h# side rather than silently
    // returning a mangled body.
    let resp_body = match text.find("\r\n\r\n") {
        Some(i) => &text[i + 4..],
        None => "",
    };
    make(status, resp_body)
}

/// Howard Hinnant's `days_from_civil` — inverse of `civil_from_unix`,
/// used by `date_parse`. Returns days since 1970-01-01 (not yet
/// multiplied by 86400).
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400; // [0, 399]
    let mp = if m > 2 { m - 3 } else { m + 9 }; // [0, 11]
    let doy = (153 * mp + 2) / 5 + d - 1; // [0, 365]
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy; // [0, 146096]
    era * 146097 + doe - 719468
}
