use hsharp_parser::ast::*;
use std::collections::HashMap;
use crate::value::{Value, RuntimeError};
use crate::value::Interpreter;
use crate::value::AsyncTaskState;
use crate::helpers::compute_mutated_container;


impl Interpreter {

pub fn eval_expr(&mut self, expr: &Expr) -> Result<Value, RuntimeError> {
        match expr {
            // String interpolation: evaluate ALL parts (text + expressions)
            Expr::Literal(Literal::Interpolated(parts), _) => {
                let mut result = String::new();
                for part in parts {
                    match part {
                        hsharp_parser::ast::InterpPart::Text(t) => result.push_str(t),
                        hsharp_parser::ast::InterpPart::Expr(e) => {
                            let v = self.eval_expr(e)?;
                            result.push_str(&v.to_string());
                        }
                    }
                }
                return Ok(Value::Str(result));
            }
            Expr::Literal(lit, _) => Ok(match lit {
                Literal::Int(n) => Value::Int(*n),
                Literal::Float(f) => Value::Float(*f),
                Literal::String(s) => Value::Str(s.clone()),
                Literal::Bool(b) => Value::Bool(*b),
                Literal::Nil => Value::Nil,
                Literal::Interpolated(parts) => {
                    let mut r = String::new();
                    for p in parts {
                        match p {
                            hsharp_parser::ast::InterpPart::Text(t) => r.push_str(t),
                            hsharp_parser::ast::InterpPart::Expr(_) => {},
                        }
                    }
                    Value::Str(r)
                }
                Literal::Bytes(b) => Value::Bytes(b.clone()),
            }),
            Expr::Ident(name, _) => {
                if let Some(v) = self.env.get(name).cloned() {
                    Ok(v)
                } else if self.fns.contains_key(name) {
                    let f = self.fns[name].clone();
                    Ok(Value::Fn {
                        name: name.clone(),
                        params: f.params.clone(),
                        body: f.body.clone(),
                        env: self.env.clone(),
                        is_async: f.is_async,
                    })
                } else {
                    Err(RuntimeError::UndefinedVar(name.clone()))
                }
            }
            Expr::BinOp(lhs, op, rhs, _) => {
                let l = self.eval_expr(lhs)?;
                let r = self.eval_expr(rhs)?;
                self.eval_binop(l, op, r)
            }
            Expr::UnOp(op, inner, _) => {
                let v = self.eval_expr(inner)?;
                match op {
                    UnOp::Neg => match v {
                        Value::Int(n) => Ok(Value::Int(-n)),
                        Value::Float(f) => Ok(Value::Float(-f)),
                        _ => Err(RuntimeError::TypeError("cannot negate".into())),
                    },
                    UnOp::Not => Ok(Value::Bool(!v.is_truthy())),
                    _ => Ok(v),
                }
            }
            Expr::Call(callee, args, _) => {
                let arg_vals: Vec<Value> = args.iter()
                    .map(|a| self.eval_expr(a))
                    .collect::<Result<_, _>>()?;

                if let Expr::Ident(name, _) = callee.as_ref() {
                    return self.call_fn(name, arg_vals);
                }

                // module::function(...) call — e.g. json::parse(x), math::sqrt(x)
                if let Expr::Path(segments, _) = callee.as_ref() {
                    let result = self.call_path(segments, arg_vals)?;
                    // sort::sort_ints / sort::sort_strings document an
                    // in-place mutation API (`sort::sort_ints(arr)` sorts
                    // `arr` itself, not a copy) — the builtin returns the
                    // sorted array, and we write it back to the first
                    // argument's binding if it's a plain named variable,
                    // mirroring the MethodCall write-back mechanism used
                    // for collection mutation elsewhere.
                    let full = segments.join("::");
                    if matches!(full.as_str(), "sort::sort_ints" | "sort::sort_strings") {
                        if let Some(Expr::Ident(name, _)) = args.first() {
                            self.env.set(name, result.clone());
                        }
                    }
                    return Ok(result);
                }

                let callee_val = self.eval_expr(callee)?;
                match callee_val {
                    Value::Fn { params, body, env, .. } => {
                        self.invoke_fn_value(&params, &body, env, arg_vals)
                    }
                    _ => Err(RuntimeError::TypeError("not callable".into())),
                }
            }
            // Bare module path used as a value — e.g. passing `math::PI` around,
            // or a path that wasn't immediately called. We best-effort resolve
            // it as a zero-arg call; otherwise return Nil.
            Expr::Path(segments, _) => {
                self.call_path(segments, Vec::new())
            }
            Expr::MethodCall(obj, method, args, _) => {
                let obj_val = self.eval_expr(obj)?;
                let arg_vals: Vec<Value> = args.iter()
                    .map(|a| self.eval_expr(a))
                    .collect::<Result<_, _>>()?;

                let var_name = if let Expr::Ident(n, _) = obj.as_ref() { Some(n.clone()) } else { None };

                // Case 1: receiver is a struct with a user-defined `impl`
                // method. Run it with `self` bound, then — if the receiver
                // is a plain named variable — write the (possibly mutated)
                // `self` back so field assignments like `self.x = 5` made
                // inside the method are visible to the caller.
                if matches!(obj_val, Value::Struct { .. }) {
                    if let Some(result) = self.try_user_method(&obj_val, method, &arg_vals) {
                        let (ret, mutated_self) = result?;
                        if let Some(name) = &var_name {
                            self.env.set(name, mutated_self);
                        }
                        return Ok(ret);
                    }
                }

                // Case 2: builtin mutating methods (push/pop/insert/remove)
                // on a plain named variable — compute the new container
                // value and write it back into the environment, since this
                // interpreter passes Value by clone rather than by shared
                // reference.
                if let Some(name) = &var_name {
                    if let Some(new_val) = compute_mutated_container(&obj_val, method, &arg_vals) {
                        self.env.set(name, new_val);
                    }
                }
                self.call_method(obj_val, method, arg_vals)
            }
            Expr::FieldAccess(obj, field, _) => {
                let v = self.eval_expr(obj)?;
                match v {
                    Value::Struct { fields, .. } => {
                        fields.get(field).cloned()
                            .ok_or_else(|| RuntimeError::UndefinedField(field.clone()))
                    }
                    Value::Tuple(items) => {
                        // Tuple field access: t.0, t.1, ... — `field` is the
                        // numeric index as a string (see the parser's
                        // numeric-field special case for the Dot operator).
                        field.parse::<usize>().ok()
                            .and_then(|idx| items.get(idx).cloned())
                            .ok_or_else(|| RuntimeError::UndefinedField(field.clone()))
                    }
                    _ => Err(RuntimeError::TypeError(format!("no field `{}` on {}", field, v))),
                }
            }
            Expr::IndexAccess(arr, idx, _) => {
                let a = self.eval_expr(arr)?;
                // Detect a literal Range subexpression directly, so we can
                // slice without materializing the full index array (which
                // is what a bare `Expr::Range` evaluates to — see below).
                if let Expr::Range(start_e, end_e, inclusive, _) = idx.as_ref() {
                    let start_v = self.eval_expr(start_e)?;
                    let end_v   = self.eval_expr(end_e)?;
                    if let (Value::Int(s), Value::Int(e)) = (start_v, end_v) {
                        let s = s.max(0) as usize;
                        let e_excl = if *inclusive { (e + 1).max(0) as usize } else { e.max(0) as usize };
                        return match a {
                            Value::Array(items) => {
                                let e_clamped = e_excl.min(items.len());
                                let s_clamped = s.min(e_clamped);
                                Ok(Value::Array(items[s_clamped..e_clamped].to_vec()))
                            }
                            Value::Str(s_val) => {
                                let chars: Vec<char> = s_val.chars().collect();
                                let e_clamped = e_excl.min(chars.len());
                                let s_clamped = s.min(e_clamped);
                                Ok(Value::Str(chars[s_clamped..e_clamped].iter().collect()))
                            }
                            Value::Bytes(b) => {
                                let e_clamped = e_excl.min(b.len());
                                let s_clamped = s.min(e_clamped);
                                Ok(Value::Bytes(b[s_clamped..e_clamped].to_vec()))
                            }
                            _ => Err(RuntimeError::TypeError("cannot slice this type".into())),
                        };
                    }
                }
                let i = self.eval_expr(idx)?;
                match (a, i) {
                    (Value::Array(arr), Value::Int(i)) => {
                        let idx = i as usize;
                        arr.get(idx).cloned()
                            .ok_or(RuntimeError::IndexOutOfBounds(i, arr.len()))
                    }
                    (Value::Str(s), Value::Int(i)) => {
                        s.chars().nth(i as usize)
                            .map(|c| Value::Str(c.to_string()))
                            .ok_or(RuntimeError::IndexOutOfBounds(i, s.len()))
                    }
                    (Value::Bytes(b), Value::Int(i)) => {
                        b.get(i as usize).copied()
                            .map(|byte| Value::Int(byte as i64))
                            .ok_or(RuntimeError::IndexOutOfBounds(i, b.len()))
                    }
                    // Index with an already-materialized Range array (e.g.
                    // produced by a `let r = 0..3; arr[r]` indirection) —
                    // treat a contiguous ascending int array as a slice.
                    (Value::Array(items), Value::Array(range_idx)) if !range_idx.is_empty() => {
                        if let (Some(Value::Int(first)), Some(Value::Int(last))) =
                            (range_idx.first(), range_idx.last())
                        {
                            let s = (*first).max(0) as usize;
                            let e_excl = ((*last) + 1).max(0) as usize;
                            let e_clamped = e_excl.min(items.len());
                            let s_clamped = s.min(e_clamped);
                            Ok(Value::Array(items[s_clamped..e_clamped].to_vec()))
                        } else {
                            Err(RuntimeError::TypeError("invalid slice index".into()))
                        }
                    }
                    (Value::Str(s_val), Value::Array(range_idx)) if !range_idx.is_empty() => {
                        if let (Some(Value::Int(first)), Some(Value::Int(last))) =
                            (range_idx.first(), range_idx.last())
                        {
                            let chars: Vec<char> = s_val.chars().collect();
                            let s = (*first).max(0) as usize;
                            let e_excl = ((*last) + 1).max(0) as usize;
                            let e_clamped = e_excl.min(chars.len());
                            let s_clamped = s.min(e_clamped);
                            Ok(Value::Str(chars[s_clamped..e_clamped].iter().collect()))
                        } else {
                            Err(RuntimeError::TypeError("invalid slice index".into()))
                        }
                    }
                    _ => Err(RuntimeError::TypeError("cannot index".into())),
                }
            }
            Expr::ArrayLit(elems, _) => {
                let vals: Vec<Value> = elems.iter()
                    .map(|e| self.eval_expr(e))
                    .collect::<Result<_, _>>()?;
                Ok(Value::Array(vals))
            }
            Expr::TupleLit(elems, _) => {
                let vals: Vec<Value> = elems.iter()
                    .map(|e| self.eval_expr(e))
                    .collect::<Result<_, _>>()?;
                Ok(Value::Tuple(vals))
            }
            Expr::StructLit(name, fields, _) => {
                let mut field_map = HashMap::new();
                for (fname, fexpr) in fields {
                    field_map.insert(fname.clone(), self.eval_expr(fexpr)?);
                }
                Ok(Value::Struct { name: name.clone(), fields: field_map })
            }
            Expr::Cast(inner, ty, _) => {
                let v = self.eval_expr(inner)?;
                match (v, ty) {
                    (Value::Int(n), TypeExpr::Named(t)) if t == "f64" || t == "f32" => Ok(Value::Float(n as f64)),
                    (Value::Float(f), TypeExpr::Named(t)) if t == "int" || t.starts_with('i') => Ok(Value::Int(f as i64)),
                    (Value::Int(n), TypeExpr::Named(t)) if t.starts_with('i') || t.starts_with('u') => Ok(Value::Int(n)),
                    (v, _) => Ok(v),
                }
            }
            Expr::Range(start, end, inclusive, _) => {
                let s = self.eval_expr(start)?;
                let e = self.eval_expr(end)?;
                match (s, e) {
                    (Value::Int(s), Value::Int(e)) => {
                        let end = if *inclusive { e + 1 } else { e };
                        Ok(Value::Array((s..end).map(Value::Int).collect()))
                    }
                    _ => Err(RuntimeError::TypeError("range requires integers".into())),
                }
            }
            Expr::Return(val, _) => {
                let v = if let Some(e) = val { self.eval_expr(e)? } else { Value::Nil };
                Ok(Value::Return(Box::new(v)))
            }
            Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
                let cond = self.eval_expr(condition)?;
                if cond.is_truthy() {
                    self.env.push();
                    let r = self.exec_block(then_body)?;
                    self.env.pop();
                    return Ok(r.unwrap_or(Value::Nil));
                }
                for (ec, eb) in elsif_branches {
                    let cv = self.eval_expr(ec)?;
                    if cv.is_truthy() {
                        self.env.push();
                        let r = self.exec_block(eb)?;
                        self.env.pop();
                        return Ok(r.unwrap_or(Value::Nil));
                    }
                }
                if let Some(else_b) = else_body {
                    self.env.push();
                    let r = self.exec_block(else_b)?;
                    self.env.pop();
                    return Ok(r.unwrap_or(Value::Nil));
                }
                Ok(Value::Nil)
            }
            Expr::Match { subject, arms, .. } => {
                let subj = self.eval_expr(subject)?;
                for arm in arms {
                    if self.pattern_matches(&arm.pattern, &subj) {
                        self.env.push();
                        self.bind_pattern(&arm.pattern, subj.clone());
                        // NOTE: previously this special-cased a
                        // single-statement arm by calling self.eval_expr()
                        // directly on its body, as a shortcut to get the
                        // arm's value without the Option<Value> wrapping
                        // exec_block produces. That shortcut was wrong for
                        // any arm whose single statement was an assignment
                        // (`pattern => var = value`) or compound assignment,
                        // since eval_expr has no case for Expr::Assign /
                        // Expr::CompoundAssign at all — those are only
                        // handled inside exec_block's Stmt::Expr dispatch.
                        // Going through exec_block unconditionally fixes
                        // this; for the common "last expression is the
                        // arm's value" case, exec_block's own implicit-
                        // return handling (see its Stmt::Expr branch)
                        // already does the right thing.
                        let result = self.exec_block(&arm.body)?;
                        self.env.pop();
                        return Ok(result.unwrap_or(Value::Nil));
                    }
                }
                Ok(Value::Nil)
            }
            Expr::SelfExpr(_) => {
                self.env.get("self").cloned()
                    .ok_or_else(|| RuntimeError::UndefinedVar("self".into()))
            }
            Expr::Unsafe(body, _arena_cfg, _) => {
                self.env.push();
                let r = self.exec_block(body)?;
                self.env.pop();
                Ok(match r {
                    Some(Value::Return(v)) => *v,
                    Some(v) => v,
                    None => Value::Nil,
                })
            }
            // await expr — resolve AsyncTask
            Expr::Await(inner, _) => {
                let task_val = self.eval_expr(inner)?;
                match task_val {
                    Value::AsyncTask(t) => match *t {
                        AsyncTaskState::Ready(v) => Ok(v),
                        AsyncTaskState::Pending { fn_name, ref args } => {
                            // v0.6: check if it's an I/O task registered in reactor
                            // otherwise execute synchronously
                            self.call_fn(&fn_name, args.clone())
                        }
                    },
                    other => Ok(other),
                }
            }
                        // Closure with environment capture
            Expr::Closure { params, body, .. } => {
                // Capture lexical scope — flatten all scopes so captured vars
                // are always accessible regardless of scope nesting
                Ok(Value::Fn {
                    name:     "<closure>".to_string(),
                    params:   params.clone(),
                    body:     body.clone(),
                    env:      self.env.flatten_for_capture(),
                    is_async: false,
                })
            }
            // ? (Try) operator — propagate Nil as early return
            Expr::Try(inner, _) => {
                let v = self.eval_expr(inner)?;
                match &v {
                    Value::Nil => {
                        // Early return with Nil from the enclosing function
                        return Ok(Value::Return(Box::new(Value::Nil)));
                    }
                    _ => Ok(v),
                }
            }

            _ => Ok(Value::Nil),
        }
    }

    /// Register an inline module's functions both under their namespaced
    /// key (`mod_name::fn_name`, used by `mod_name::fn_name(...)` call
    /// sites) and under their bare name (used by other functions *inside*
    /// the same module calling each other directly, e.g. `gcd` calling
    /// `gcd` recursively without the `math_utils::` prefix). Nested `mod`
    /// blocks are flattened recursively with dotted-path namespacing.
    pub fn register_mod_items(&mut self, mod_name: &str, items: &[Item]) {
        for item in items {
            match item {
                Item::FnDef(f) => {
                    let namespaced = format!("{}::{}", mod_name, f.name);
                    self.fns.insert(namespaced, f.clone());
                    // Also register under the bare name so sibling
                    // functions in the same module can call each other
                    // without the module prefix. If a bare name collision
                    // already exists (e.g. two modules both define
                    // `helper`), the most recently registered module wins —
                    // acceptable for v0.8; cross-module name collisions
                    // should use the qualified form anyway.
                    self.fns.insert(f.name.clone(), f.clone());
                }
                Item::StructDef(s) => {
                    self.structs.insert(s.name.clone(), s.clone());
                }
                Item::ModDecl { name: sub_name, inline: Some(sub_items), .. } => {
                    let nested = format!("{}::{}", mod_name, sub_name);
                    self.register_mod_items(&nested, sub_items);
                }
                _ => {}
            }
        }
    }

}
