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
            _ => Ok(None),
        }
    }
}
