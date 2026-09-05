use hsharp_parser::ast::*;
use std::collections::HashMap;
use crate::value::{Value, Env, RuntimeError, Interpreter};
use crate::runtime_async;


impl Interpreter {
    pub fn new() -> Self {
        Self {
            env: Env::new(),
            fns: HashMap::new(),
            methods: HashMap::new(),
            structs: HashMap::new(),
            enums: HashMap::new(),
            stdout: String::new(),
            captured_output: false,
            reactor: runtime_async::Reactor::new(),
            mem_mode_notes_given: std::collections::HashSet::new(),
            step_count: 0,
            step_limit: None,
            tcp_streams: HashMap::new(),
            next_tcp_handle: 1,
            atomics: HashMap::new(),
        }
    }

    pub fn run_module(&mut self, module: &Module) -> Result<(), RuntimeError> {
        self.run_module_register_only(module)?;

        // Call main
        if let Some(main_fn) = self.fns.get("main").cloned() {
            let stmts = main_fn.body.clone();
            self.env.push();
            self.exec_block(&stmts)?;
            self.env.pop();
        }

        Ok(())
    }

    /// Register every top-level item (functions, structs, enums, inline
    /// modules, impl blocks) without invoking `main`. Used by `run_module`
    /// internally, and exposed publicly so callers that want to invoke a
    /// *specific* function directly — e.g. a test runner calling individual
    /// `#[test]` functions one at a time — can register the module once and
    /// then drive execution themselves via whatever entry point they want.
    pub fn run_module_register_only(&mut self, module: &Module) -> Result<(), RuntimeError> {
        // ── `use "std -> x"` resolution ──────────────────────────────────
        // Real file-based std library loading. This used to be a complete
        // no-op (`Stmt::Import`/`module.imports` were parsed and then
        // discarded — see git history / COMPILER-PATCH-NOTES.md); every
        // `std ->` capability instead came from a hidden Rust-side alias
        // table (`helpers::resolve_stdlib_alias`, now disabled by design).
        // From here on, each `use "std -> lib"` a program declares is
        // resolved against the real HackerOS std library layout and its
        // functions are registered exactly like a `mod lib` declaration
        // would be — done *before* any other item registration, so a
        // user-defined function of the same name naturally shadows the
        // std one (later inserts into `self.fns` win) rather than the
        // reverse. `use "core -> x"` is intentionally left untouched here:
        // `core` stays statically embedded in this runtime, unaffected by
        // this whole mechanism (see `helpers.rs` module doc comment).
        for (kind, alias, _span) in &module.imports {
            if let hsharp_parser::ast::ImportKind::Std { path, .. } = kind {
                let lib = path.last().cloned().unwrap_or_default();
                if lib.is_empty() { continue; }
                let ns = alias.clone().unwrap_or_else(|| lib.clone());
                self.load_std_module(&lib, &ns)?;
            }
        }

        // Register top-level items
        for item in &module.items {
            match item {
                Item::FnDef(f) => { self.fns.insert(f.name.clone(), f.clone()); }
                Item::StructDef(s) => { self.structs.insert(s.name.clone(), s.clone()); }
                Item::EnumDef(e) => { self.enums.insert(e.name.clone(), e.clone()); }
                Item::ModDecl { name, inline: Some(items), .. } => {
                    self.register_mod_items(name, items);
                }
                Item::ImplBlock(imp) => {
                    self.register_impl_methods(&imp.type_name, &imp.methods);
                }
                _ => {}
            }
        }
        // `const`/top-level `let` bindings: evaluated once, here, after
        // every fn/struct/enum is already registered above (so a const
        // initializer can call a top-level fn) but before `main` runs.
        // Stored in the outermost env scope via `define`, same place
        // function-body `let`s live, so `Expr::Ident` lookup finds them
        // through the exact same path with no special-casing needed.
        for item in &module.items {
            if let Item::ConstDef { name, value, .. } = item {
                let v = self.eval_expr(value)?;
                self.env.define(name, v, false);
            }
        }
        Ok(())
    }

    /// Resolve and load one `use "std -> lib"` import: find
    /// `/usr/lib/HackerOS/H#/std/{lib}.h#` on disk, parse it, and register
    /// its public functions under the `{ns}::{fn}` namespace (`ns` is the
    /// import's `from "alias"` if given, otherwise `lib` itself) — the
    /// same registration `register_mod_items` already does for an inline
    /// `mod` block, reused here so `fs::read(...)`-style call sites
    /// resolve identically either way.
    ///
    /// A std file is free to `use "std -> other"` itself (e.g. `fs.h#`
    /// leaning on `path.h#`); those nested imports are resolved
    /// recursively, each under its own declared namespace, before this
    /// file's own functions are registered — so a std file's internal
    /// calls into another std module see it already loaded.
    ///
    /// Returns a hard error (not a warning, not a silent fallback) if the
    /// file doesn't exist or fails to parse — see
    /// `helpers::std_lib_missing_message` for the exact wording, which
    /// deliberately points at `hacker unpack h#-utils` rather than just
    /// saying "file not found".
    ///
    /// NOTE on redundancy with the compiler crate: `hsharp-compiler`'s
    /// `modules::ModuleResolver::expand_program` now *also* resolves
    /// `use "std -> x"` — by inlining the std file's items straight into
    /// `module.items` (mangled as `{alias}_{fn}`, the same convention
    /// `mod` uses) *before* `run_module`/`run_module_register_only` here
    /// ever runs, so that both the interpreter and the LLVM/AOT backend
    /// compile the exact same expanded source (see that function's doc
    /// comment for the full interpreter/AOT-divergence story this fixed).
    /// Every CLI entry point that goes through `expand_program` first
    /// (`hsharp preview`/`build`/`check`) therefore hits this function
    /// with imports that are already satisfied — this becomes a no-op-
    /// shaped redundant registration, not a bug, since re-registering an
    /// already-inlined function under its `{ns}::{fn}` key alongside the
    /// mangled `{ns}_{fn}` one just adds a second, harmless way to call
    /// it. This function is kept (rather than deleted) for the one
    /// caller that *doesn't* go through `expand_program`: the WASM
    /// playground (`playground/src/run.rs`), which calls `run_module`
    /// directly on a freshly-parsed single-file snippet with no
    /// filesystem access at all — where this will simply, correctly,
    /// fail with the "please install h# utils" message, since
    /// `/usr/lib/HackerOS` doesn't exist in a browser sandbox either way.
    pub fn load_std_module(&mut self, lib: &str, ns: &str) -> Result<(), RuntimeError> {
        let path = crate::helpers::std_lib_path(lib);
        let src = std::fs::read_to_string(&path)
            .map_err(|_| RuntimeError::Custom(crate::helpers::std_lib_missing_message(lib)))?;

        let result = hsharp_parser::parse(&src, path.to_str().unwrap_or(lib));
        if result.has_errors() {
            return Err(RuntimeError::Custom(format!(
                "parse errors while loading std module '{}' ({}):\n{}",
                lib, path.display(), result.render_errors()
            )));
        }

        // A std file's own `use "std -> other"` imports, resolved before
        // its functions are registered (see doc comment above).
        for (kind, sub_alias, _span) in &result.module.imports {
            if let ImportKind::Std { path: sub_path, .. } = kind {
                let sub_lib = sub_path.last().cloned().unwrap_or_default();
                if sub_lib.is_empty() { continue; }
                let sub_ns = sub_alias.clone().unwrap_or_else(|| sub_lib.clone());
                self.load_std_module(&sub_lib, &sub_ns)?;
            }
        }

        self.register_mod_items(ns, &result.module.items);
        Ok(())
    }

    /// Directly invoke a top-level function by name with no arguments —
    /// the shape every `#[test] fn name() is ... end` function has. Returns
    /// the RuntimeError (e.g. a failed `assert_eq`) on failure so callers
    /// can report it, rather than propagating a process exit.
    pub fn call_test_fn(&mut self, name: &str) -> Result<Value, RuntimeError> {
        self.call_fn(name, Vec::new())
    }

    pub fn exec_block(&mut self, stmts: &[Stmt]) -> Result<Option<Value>, RuntimeError> {
        let len = stmts.len();
        for (i, stmt) in stmts.iter().enumerate() {
            // Implicit return: last expression in block yields its value
            if i == len - 1 {
                if let Stmt::Expr(expr, _) = stmt {
                    match expr {
                        // Control-flow exprs are executed normally
                        Expr::If { .. } | Expr::While { .. } | Expr::For { .. } |
                        Expr::Assign(..) | Expr::CompoundAssign(..) | Expr::Unsafe(..) => {
                            if let Some(v) = self.exec_stmt(stmt)? {
                                return Ok(Some(v));
                            }
                        }
                        // All other exprs: evaluate and return their value
                        _ => {
                            let v = self.eval_expr(expr)?;
                            return Ok(Some(v));
                        }
                    }
                    continue;
                }
            }
            if let Some(v) = self.exec_stmt(stmt)? {
                return Ok(Some(v));
            }
        }
        Ok(None)
    }

    pub fn exec_stmt(&mut self, stmt: &Stmt) -> Result<Option<Value>, RuntimeError> {
        if let Some(limit) = self.step_limit {
            self.step_count += 1;
            if self.step_count > limit {
                return Err(RuntimeError::Panic(format!(
                    "step limit exceeded ({} statements) — program did not finish in time; this is usually an infinite or runaway loop",
                    limit
                )));
            }
        }
        match stmt {
            Stmt::Let { name, mutable, value, .. } => {
                let val = if let Some(expr) = value {
                    self.eval_expr(expr)?
                } else {
                    Value::Nil
                };
                // The `?` operator (Expr::Try) signals an early return by
                // producing a Value::Return(Nil) sentinel instead of an
                // ordinary value. If we're binding the result of an
                // expression containing a top-level `?` that short-
                // circuited, propagate the early return immediately rather
                // than binding the sentinel itself to `name` and continuing
                // — that would silently corrupt `name`'s value and let
                // execution carry on past where it should have stopped.
                if matches!(val, Value::Return(_)) {
                    return Ok(Some(val));
                }
                self.env.define(name, val, *mutable);
                Ok(None)
            }
            Stmt::Return(expr, _) => {
                let val = if let Some(e) = expr {
                    self.eval_expr(e)?
                } else {
                    Value::Nil
                };
                Ok(Some(Value::Return(Box::new(val))))
            }
            Stmt::Break(_, _) => Ok(Some(Value::Break)),
            Stmt::Continue(_) => Ok(Some(Value::Continue)),
            Stmt::Expr(expr, _) => {
                match expr {
                    Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
                        let cond_val = self.eval_expr(condition)?;
                        if cond_val.is_truthy() {
                            self.env.push();
                            let r = self.exec_block(then_body)?;
                            self.env.pop();
                            return Ok(r);
                        }
                        for (ec, eb) in elsif_branches {
                            let cv = self.eval_expr(ec)?;
                            if cv.is_truthy() {
                                self.env.push();
                                let r = self.exec_block(eb)?;
                                self.env.pop();
                                return Ok(r);
                            }
                        }
                        if let Some(else_b) = else_body {
                            self.env.push();
                            let r = self.exec_block(else_b)?;
                            self.env.pop();
                            return Ok(r);
                        }
                        Ok(None)
                    }
                    Expr::While { condition, body, .. } => {
                        loop {
                            let cond = self.eval_expr(condition)?;
                            if !cond.is_truthy() { break; }
                            self.env.push();
                            let r = self.exec_block(body)?;
                            self.env.pop();
                            match r {
                                Some(Value::Break) => break,
                                Some(Value::Continue) => continue,
                                Some(v @ Value::Return(_)) => return Ok(Some(v)),
                                _ => {}
                            }
                        }
                        Ok(None)
                    }
                    Expr::For { pattern, iterable, body, .. } => {
                        let iter_val = self.eval_expr(iterable)?;
                        let items = match &iter_val {
                            Value::Array(arr) => arr.clone(),
                            Value::Str(s) => s.chars().map(|c| Value::Str(c.to_string())).collect(),
                            _ => return Err(RuntimeError::TypeError(format!("cannot iterate over {}", iter_val))),
                        };
                        for item in items {
                            self.env.push();
                            if let Pattern::Ident(name, _) = pattern {
                                self.env.define(name, item, false);
                            }
                            let r = self.exec_block(body)?;
                            self.env.pop();
                            match r {
                                Some(Value::Break) => break,
                                Some(Value::Continue) => continue,
                                Some(v @ Value::Return(_)) => return Ok(Some(v)),
                                _ => {}
                            }
                        }
                        Ok(None)
                    }
                    Expr::Assign(lhs, rhs, _) => {
                        let val = self.eval_expr(rhs)?;
                        self.assign_lhs(lhs, val)?;
                        Ok(None)
                    }
                    Expr::CompoundAssign(lhs, op, rhs, _) => {
                        let rval = self.eval_expr(rhs)?;
                        let lval = self.eval_expr(lhs)?;
                        let result = self.eval_binop(lval, op, rval)?;
                        self.assign_lhs(lhs, result)?;
                        Ok(None)
                    }
                    Expr::Unsafe(body, arena_cfg, _) => {
                        use hsharp_parser::ast::{UnsafeMode, ArenaKind, ManualKind};
                        // Describe arena type in scope (for debug/tooling)
                        let arena_name = match arena_cfg.as_ref().map(|c| &c.mode) {
                            Some(UnsafeMode::Arena { kind, size: _ }) => {
                                let k = match kind {
                                    ArenaKind::General => "general",
                                    ArenaKind::Fixed   => "fixed",
                                    ArenaKind::Pool    => "pool",
                                    ArenaKind::Page    => "page",
                                    ArenaKind::Ring    => "ring",
                                };
                                format!("arena({})", k)
                            }
                            Some(UnsafeMode::Manual(ManualKind::Modern))  => "manual".to_string(),
                            Some(UnsafeMode::Manual(ManualKind::Classic)) => "manual(classic)".to_string(),
                            Some(UnsafeMode::Raw) | None                  => "raw".to_string(),
                        };
                        self.env.push();
                        // Expose __arena_kind in scope for introspection
                        self.env.define(&format!("__unsafe_{}", arena_name), Value::Str(arena_name.clone()), false);
                        let r = self.exec_block(body)?;
                        self.env.pop();
                        // Only propagate explicit returns, not block values
                        // (otherwise outer block exits early after arena block)
                        match r {
                            Some(Value::Return(_)) => Ok(r),
                            _ => Ok(None),
                        }
                    }
                    _ => {
                        self.eval_expr(expr)?;
                        Ok(None)
                    }
                }
            }
            Stmt::Item(Item::FnDef(f)) => {
                self.fns.insert(f.name.clone(), f.clone());
                Ok(None)
            }
            Stmt::Item(Item::ModDecl { name, inline: Some(items), .. }) => {
                self.register_mod_items(name, items);
                Ok(None)
            }
            // A function body — or a REPL line (see cli/src/repl.rs) —
            // can contain a local `const`/struct/enum def just like it can
            // contain a local `fn`. These previously fell through to the
            // wildcard arm below and silently did nothing; now they
            // register the same way the top-level versions do in
            // `run_module_register_only`.
            Stmt::Item(Item::ConstDef { name, value, .. }) => {
                let v = self.eval_expr(value)?;
                self.env.define(name, v, false);
                Ok(None)
            }
            Stmt::Item(Item::StructDef(s)) => {
                self.structs.insert(s.name.clone(), s.clone());
                Ok(None)
            }
            Stmt::Item(Item::EnumDef(e)) => {
                self.enums.insert(e.name.clone(), e.clone());
                Ok(None)
            }
            _ => Ok(None),
        }
    }
}
