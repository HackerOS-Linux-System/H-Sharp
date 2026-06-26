use hsharp_parser::ast::*;
use hsharp_parser::span::Span;
use std::collections::{HashMap, HashSet};

pub struct OptimizeContext {
    /// Functions eligible for inlining: `#[inline]`/`#[always_inline]`,
    /// single-statement body that is `return <expr>` or a bare tail
    /// expression, with no recursion (checked below).
    inline_fns: HashMap<String, (Vec<String>, Expr)>,
    /// Struct names with `#[derive(Debug)]` -> generated fn name.
    derive_debug: HashSet<String>,
    /// Struct names with `#[derive(PartialEq)]` -> generated fn name.
    derive_eq: HashSet<String>,
    /// Map from variable name -> struct type name, for the current
    /// function being processed (best-effort, from `let x: StructName = ...`
    /// and constructor calls). Used to resolve derive-call rewriting
    /// without a full type checker pass.
    var_types: HashMap<String, String>,
    pub stats: OptStats,
}

#[derive(Default, Debug)]
pub struct OptStats {
    pub consts_folded:    usize,
    pub strings_folded:   usize,
    pub branches_removed: usize,
    pub calls_inlined:    usize,
    pub derive_rewrites:  usize,
}

impl OptimizeContext {
    pub fn new() -> Self {
        Self {
            inline_fns:   HashMap::new(),
            derive_debug: HashSet::new(),
            derive_eq:    HashSet::new(),
            var_types:    HashMap::new(),
            stats:        OptStats::default(),
        }
    }

    /// Run the full pass over a module, returning the optimized module.
    pub fn run(mut self, mut module: Module) -> (Module, OptStats) {
        self.collect_inline_fns(&module);
        self.collect_derives(&module);

        for item in &mut module.items {
            self.optimize_item(item);
        }

        (module, self.stats)
    }

    // ── Collection passes ──────────────────────────────────────────────────

    fn collect_inline_fns(&mut self, module: &Module) {
        for item in &module.items {
            if let Item::FnDef(f) = item {
                let is_inline = f.attrs.iter().any(|a| a.name == "inline" || a.name == "always_inline");
                if !is_inline { continue; }
                // Only single-statement bodies: `return <expr>` or a bare
                // tail expression. Anything with control flow, multiple
                // statements, or `let` bindings is not inlined (keeps the
                // substitution trivial and side-effect-safe).
                if f.body.len() != 1 { continue; }
                let tail_expr = match &f.body[0] {
                    Stmt::Return(Some(e), _) => Some(e.clone()),
                    Stmt::Expr(e, _)         => Some(e.clone()),
                    _                        => None,
                };
                let Some(expr) = tail_expr else { continue };

                // Reject self-recursive inline candidates (would infinitely
                // expand). Cheap syntactic check: does the body call `f.name`?
                if expr_calls_fn(&expr, &f.name) { continue; }

                let params: Vec<String> = f.params.iter().map(|p| p.name.clone()).collect();
                self.inline_fns.insert(f.name.clone(), (params, expr));
            }
        }
    }

    fn collect_derives(&mut self, module: &Module) {
        for item in &module.items {
            if let Item::StructDef(s) = item {
                for attr in &s.attrs {
                    if attr.name != "derive" { continue; }
                    for arg in &attr.args {
                        match arg {
                            AttrArg::Ident(name) if name == "Debug" => {
                                self.derive_debug.insert(s.name.clone());
                            }
                            AttrArg::Ident(name) if name == "PartialEq" => {
                                self.derive_eq.insert(s.name.clone());
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
    }

    // ── Item-level dispatch ──────────────────────────────────────────────────

    fn optimize_item(&mut self, item: &mut Item) {
        match item {
            Item::FnDef(f) => self.optimize_fn(f),
            Item::ImplBlock(imp) => {
                for m in &mut imp.methods { self.optimize_fn(m); }
            }
            Item::ModDecl { inline: Some(items), .. } => {
                for it in items { self.optimize_item(it); }
            }
            _ => {}
        }
    }

    fn optimize_fn(&mut self, f: &mut FnDef) {
        // Record declared-type hints for derive-call rewriting within this
        // function's body (reset per-function — best-effort, local only).
        self.var_types.clear();
        for p in &f.params {
            if let TypeExpr::Named(tn) = &p.ty {
                if self.derive_debug.contains(tn) || self.derive_eq.contains(tn) {
                    self.var_types.insert(p.name.clone(), tn.clone());
                }
            }
        }
        self.optimize_block(&mut f.body);
    }

    fn optimize_block(&mut self, stmts: &mut Vec<Stmt>) {
        for stmt in stmts.iter_mut() {
            self.optimize_stmt(stmt);
        }
        // Dead-code elimination pass: if any statement is an `if` whose
        // condition folded to a constant, splice the taken branch's
        // statements in place of the `if` (or remove it entirely if the
        // taken branch is empty and there's no else).
        let mut i = 0;
        while i < stmts.len() {
            let replacement = match &mut stmts[i] {
                Stmt::Expr(Expr::If { condition, then_body, elsif_branches, else_body, .. }, _) => {
                    try_fold_if(condition, then_body, elsif_branches, else_body, &mut self.stats)
                }
                _ => None,
            };
            match replacement {
                Some(mut new_stmts) => {
                    self.stats.branches_removed += 1;
                    stmts.splice(i..i + 1, new_stmts.drain(..));
                    // Re-optimize the spliced-in statements (they may
                    // themselves contain foldable expressions/branches).
                    let end = stmts.len();
                    for j in i..end {
                        if let Some(s) = stmts.get_mut(j) {
                            self.optimize_stmt(s);
                        }
                    }
                    // Don't advance `i` — re-check the spliced region in
                    // case it folds further (rare, but cheap to allow).
                }
                None => { i += 1; }
            }
        }
    }

    fn optimize_stmt(&mut self, stmt: &mut Stmt) {
        match stmt {
            Stmt::Let { value: Some(e), ty, name, .. } => {
                self.optimize_expr(e);
                // Track struct-typed locals for derive-call rewriting.
                if let Some(TypeExpr::Named(tn)) = ty {
                    if self.derive_debug.contains(tn) || self.derive_eq.contains(tn) {
                        self.var_types.insert(name.clone(), tn.clone());
                    }
                } else if let Expr::StructLit(sn, _, _) = e {
                    if self.derive_debug.contains(sn) || self.derive_eq.contains(sn) {
                        self.var_types.insert(name.clone(), sn.clone());
                    }
                }
            }
            Stmt::Let { value: None, .. } => {}
            Stmt::Return(Some(e), _) | Stmt::Expr(e, _) => self.optimize_expr(e),
            Stmt::Return(None, _) | Stmt::Break(None, _) | Stmt::Continue(_) => {}
            Stmt::Break(Some(e), _) => self.optimize_expr(e),
            Stmt::Import(..) | Stmt::Item(_) => {}
        }
    }

    // ── Expression-level optimization ────────────────────────────────────────

    fn optimize_expr(&mut self, expr: &mut Expr) {
        // First, recurse into children so folding happens bottom-up
        // (innermost constants fold first, enabling outer folds).
        match expr {
            Expr::BinOp(l, _, r, _) => { self.optimize_expr(l); self.optimize_expr(r); }
            Expr::UnOp(_, e, _) => self.optimize_expr(e),
            Expr::Cast(e, _, _) => self.optimize_expr(e),
            Expr::Assign(l, r, _) => { self.optimize_expr(l); self.optimize_expr(r); }
            Expr::CompoundAssign(l, _, r, _) => { self.optimize_expr(l); self.optimize_expr(r); }
            Expr::FieldAccess(e, _, _) => self.optimize_expr(e),
            Expr::IndexAccess(e, i, _) => { self.optimize_expr(e); self.optimize_expr(i); }
            Expr::MethodCall(recv, _, args, _) => {
                self.optimize_expr(recv);
                for a in args { self.optimize_expr(a); }
            }
            Expr::Call(callee, args, _) => {
                self.optimize_expr(callee);
                for a in args { self.optimize_expr(a); }
            }
            Expr::ArrayLit(elems, _) | Expr::TupleLit(elems, _) => {
                for e in elems { self.optimize_expr(e); }
            }
            Expr::StructLit(_, fields, _) => {
                for (_, e) in fields { self.optimize_expr(e); }
            }
            Expr::Range(a, b, _, _) => { self.optimize_expr(a); self.optimize_expr(b); }
            Expr::Try(e, _) | Expr::Await(e, _) => self.optimize_expr(e),
            Expr::Return(Some(e), _) => self.optimize_expr(e),
            Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
                self.optimize_expr(condition);
                self.optimize_block(then_body);
                for (c, b) in elsif_branches.iter_mut() {
                    self.optimize_expr(c);
                    self.optimize_block(b);
                }
                if let Some(b) = else_body { self.optimize_block(b); }
            }
            Expr::While { condition, body, .. } => {
                self.optimize_expr(condition);
                self.optimize_block(body);
            }
            Expr::For { iterable, body, .. } => {
                self.optimize_expr(iterable);
                self.optimize_block(body);
            }
            Expr::Do { body, .. } => self.optimize_block(body),
            Expr::Match { subject, arms, .. } => {
                self.optimize_expr(subject);
                for arm in arms.iter_mut() {
                    if let Some(g) = &mut arm.guard { self.optimize_expr(g); }
                    self.optimize_block(&mut arm.body);
                }
            }
            Expr::Closure { body, .. } => self.optimize_block(body),
            Expr::Unsafe(body, _, _) => self.optimize_block(body),
            _ => {}
        }

        // Then apply rewrites to this node itself.
        self.fold_constants(expr);
        self.fold_string_concat(expr);
        self.fold_interpolated(expr);
        self.inline_call(expr);
        self.rewrite_derive_call(expr);
    }

    // ── 1. Constant folding (arithmetic/comparison on literals) ─────────────

    fn fold_constants(&mut self, expr: &mut Expr) {
        let folded = if let Expr::BinOp(l, op, r, span) = expr {
            match (l.as_ref(), r.as_ref()) {
                (Expr::Literal(Literal::Int(a), _), Expr::Literal(Literal::Int(b), _)) => {
                    fold_int_binop(*a, *b, op).map(|v| Expr::Literal(Literal::Int(v), span.clone()))
                }
                (Expr::Literal(Literal::Float(a), _), Expr::Literal(Literal::Float(b), _)) => {
                    fold_float_binop(*a, *b, op).map(|v| Expr::Literal(Literal::Float(v), span.clone()))
                }
                (Expr::Literal(Literal::Bool(a), _), Expr::Literal(Literal::Bool(b), _)) => {
                    fold_bool_binop(*a, *b, op).map(|v| Expr::Literal(Literal::Bool(v), span.clone()))
                }
                _ => None,
            }
        } else if let Expr::UnOp(op, inner, span) = expr {
            match (op, inner.as_ref()) {
                (UnOp::Neg, Expr::Literal(Literal::Int(n), _)) =>
                Some(Expr::Literal(Literal::Int(-n), span.clone())),
                (UnOp::Neg, Expr::Literal(Literal::Float(n), _)) =>
                Some(Expr::Literal(Literal::Float(-n), span.clone())),
                (UnOp::Not, Expr::Literal(Literal::Bool(b), _)) =>
                Some(Expr::Literal(Literal::Bool(!b), span.clone())),
                _ => None,
            }
        } else {
            None
        };

        if let Some(new_expr) = folded {
            self.stats.consts_folded += 1;
            *expr = new_expr;
        }
    }

    // ── 2. String concatenation folding ──────────────────────────────────────

    fn fold_string_concat(&mut self, expr: &mut Expr) {
        if let Expr::BinOp(l, BinOp::Add, r, span) = expr {
            if let (Expr::Literal(Literal::String(a), _), Expr::Literal(Literal::String(b), _)) =
                (l.as_ref(), r.as_ref())
                {
                    let combined = format!("{}{}", a, b);
                    self.stats.strings_folded += 1;
                    *expr = Expr::Literal(Literal::String(combined), span.clone());
                }
        }
    }

    /// Fold `Literal::Interpolated` parts when every `${...}` expression has
    /// itself folded down to a literal (after the bottom-up recursion in
    /// `optimize_expr` already ran on each part). E.g.:
    ///   "x = ${1 + 2}"  ->  (after step 1)  "x = ${3}"  ->  "x = 3"
    fn fold_interpolated(&mut self, expr: &mut Expr) {
        let Expr::Literal(Literal::Interpolated(parts), span) = expr else { return };

        // Interpolated parts aren't visited by the generic recursion above
        // (InterpPart::Expr holds a boxed Expr) — fold each part's
        // expression here first.
        for part in parts.iter_mut() {
            if let InterpPart::Expr(e) = part {
                self.optimize_expr(e);
            }
        }

        // If every part is now a literal-or-text, concatenate into one
        // plain string.
        let mut all_const = true;
        let mut out = String::new();
        for part in parts.iter() {
            match part {
                InterpPart::Text(t) => out.push_str(t),
                InterpPart::Expr(e) => match e.as_ref() {
                    Expr::Literal(Literal::String(s), _) => out.push_str(s),
                    Expr::Literal(Literal::Int(n), _)    => out.push_str(&n.to_string()),
                    Expr::Literal(Literal::Float(f), _)  => out.push_str(&f.to_string()),
                    Expr::Literal(Literal::Bool(b), _)   => out.push_str(if *b { "true" } else { "false" }),
                    _ => { all_const = false; break; }
                },
            }
        }

        if all_const {
            self.stats.strings_folded += 1;
            *expr = Expr::Literal(Literal::String(out), span.clone());
        }
    }

    // ── 4. #[inline] substitution ────────────────────────────────────────────

    fn inline_call(&mut self, expr: &mut Expr) {
        let Expr::Call(callee, args, span) = expr else { return };
        let Expr::Ident(name, _) = callee.as_ref() else { return };
        let Some((params, body)) = self.inline_fns.get(name).cloned() else { return };
        if params.len() != args.len() { return; }

        // Substitute each parameter identifier in `body` with the
        // corresponding argument expression. Only safe because inline
        // candidates are restricted (in collect_inline_fns) to pure,
        // single-expression bodies — no risk of evaluation-order or
        // multiple-evaluation side effects changing semantics... EXCEPT
        // if a parameter appears more than once in `body` AND the
        // corresponding argument has side effects (e.g. a function call).
        // Guard against that:
        for (i, p) in params.iter().enumerate() {
            if count_ident_uses(&body, p) > 1 && expr_has_side_effects(&args[i]) {
                return; // not safe to inline — would duplicate side effects
            }
        }

        let mut subst = HashMap::new();
        for (p, a) in params.iter().zip(args.iter()) {
            subst.insert(p.clone(), a.clone());
        }
        let mut new_body = body;
        substitute_idents(&mut new_body, &subst);
        retag_span(&mut new_body, span);
        self.stats.calls_inlined += 1;
        *expr = new_body;
    }

    // ── 5. Derive-call rewriting ──────────────────────────────────────────────

    /// Rewrite `to_string(x)` -> `{Struct}_debug(x)` when `x` has a known
    /// derived-`Debug` struct type, and `x == y` / `x != y` ->
    /// `{Struct}_eq(x, y)` (negated for `!=`) when both sides share a known
    /// derived-`PartialEq` struct type.
    ///
    /// Type information here is best-effort (from `var_types`, populated by
    /// `let x: StructName = ...` declarations and struct-literal
    /// assignments in the *same function*). This is intentionally
    /// conservative: if the type can't be determined locally, the call is
    /// left as-is and falls through to the existing `HType::Any` codegen
    /// path (which previously just returned 0 for struct equality —
    /// silently wrong; this rewrite fixes the common case without requiring
    /// the full type checker from §3 to land first).
    fn rewrite_derive_call(&mut self, expr: &mut Expr) {
        match expr {
            Expr::Call(callee, args, span) => {
                let Expr::Ident(name, _) = callee.as_ref() else { return };
                if name != "to_string" || args.len() != 1 { return; }
                let Some(struct_name) = self.expr_struct_type(&args[0]) else { return };
                if !self.derive_debug.contains(&struct_name) { return; }
                let debug_fn = format!("{}_debug", struct_name);
                self.stats.derive_rewrites += 1;
                *expr = Expr::Call(
                    Box::new(Expr::Ident(debug_fn, span.clone())),
                                   args.clone(),
                                   span.clone(),
                );
            }
            Expr::BinOp(l, op @ (BinOp::Eq | BinOp::NotEq), r, span) => {
                let Some(lt) = self.expr_struct_type(l) else { return };
                let Some(rt) = self.expr_struct_type(r) else { return };
                if lt != rt || !self.derive_eq.contains(&lt) { return; }
                let eq_fn = format!("{}_eq", lt);
                let call = Expr::Call(
                    Box::new(Expr::Ident(eq_fn, span.clone())),
                                      vec![(**l).clone(), (**r).clone()],
                                      span.clone(),
                );
                self.stats.derive_rewrites += 1;
                *expr = if matches!(op, BinOp::NotEq) {
                    Expr::UnOp(UnOp::Not, Box::new(call), span.clone())
                } else {
                    call
                };
            }
            _ => {}
        }
    }

    /// Best-effort: resolve the struct type name of an expression using
    /// `var_types` (identifiers) and direct struct literals.
    fn expr_struct_type(&self, e: &Expr) -> Option<String> {
        match e {
            Expr::Ident(name, _)        => self.var_types.get(name).cloned(),
            Expr::StructLit(name, _, _) => Some(name.clone()),
            Expr::UnOp(UnOp::Ref | UnOp::RefMut | UnOp::Deref, inner, _) => self.expr_struct_type(inner),
            _ => None,
        }
    }
}

// ── Free helper functions ──────────────────────────────────────────────────

fn fold_int_binop(a: i64, b: i64, op: &BinOp) -> Option<i64> {
    match op {
        BinOp::Add => a.checked_add(b),
        BinOp::Sub => a.checked_sub(b),
        BinOp::Mul => a.checked_mul(b),
        // Avoid folding division/modulo by zero — let it be a runtime error
        // (matches normal language semantics) rather than a compile-time
        // panic in the optimizer.
        BinOp::Div if b != 0 => a.checked_div(b),
        BinOp::Mod if b != 0 => a.checked_rem(b),
        BinOp::BitAnd => Some(a & b),
        BinOp::BitOr  => Some(a | b),
        BinOp::BitXor => Some(a ^ b),
        BinOp::Shl if (0..64).contains(&b) => a.checked_shl(b as u32),
        BinOp::Shr if (0..64).contains(&b) => a.checked_shr(b as u32),
        _ => None,
    }
}

fn fold_float_binop(a: f64, b: f64, op: &BinOp) -> Option<f64> {
    match op {
        BinOp::Add => Some(a + b),
        BinOp::Sub => Some(a - b),
        BinOp::Mul => Some(a * b),
        BinOp::Div if b != 0.0 => Some(a / b),
        _ => None,
    }
}

fn fold_bool_binop(a: bool, b: bool, op: &BinOp) -> Option<bool> {
    match op {
        BinOp::And => Some(a && b),
        BinOp::Or  => Some(a || b),
        BinOp::Eq    => Some(a == b),
        BinOp::NotEq => Some(a != b),
        _ => None,
    }
}

/// If `condition` is a constant `bool` literal (after folding), return the
/// statements of the branch that would execute, flattening the `if` away
/// entirely. Returns `None` if the condition isn't a known constant.
fn try_fold_if(
    condition:      &mut Expr,
    then_body:      &mut Vec<Stmt>,
    elsif_branches: &mut Vec<(Expr, Vec<Stmt>)>,
               else_body:      &mut Option<Vec<Stmt>>,
                   stats:          &mut OptStats,
) -> Option<Vec<Stmt>> {
    let Expr::Literal(Literal::Bool(cond_val), _) = condition else { return None };

    if *cond_val {
        return Some(std::mem::take(then_body));
    }

    // Condition is false: try each elsif in order.
    for (i, (cond, _)) in elsif_branches.iter().enumerate() {
        match cond {
            Expr::Literal(Literal::Bool(true), _) => {
                let (_, body) = elsif_branches.remove(i);
                return Some(body);
            }
            Expr::Literal(Literal::Bool(false), _) => {
                // This elsif is also dead; continue checking later ones.
                // (Removal happens lazily — we only fully resolve when we
                // hit a non-constant or run out, to keep indices simple.)
                let _ = stats; // reserved for future per-branch counting
                continue;
            }
            _ => return None, // a non-constant elsif — can't fully resolve
        }
    }

    // All elsifs (if any) are constant-false; fall through to else.
    if elsif_branches.iter().all(|(c, _)| matches!(c, Expr::Literal(Literal::Bool(false), _))) {
        return Some(else_body.take().unwrap_or_default());
    }

    None
}

/// Does `expr` contain a call to function `name`? (cheap syntactic check
/// used to reject self-recursive #[inline] candidates)
fn expr_calls_fn(expr: &Expr, name: &str) -> bool {
    let mut found = false;
    walk_expr(expr, &mut |e| {
        if let Expr::Call(callee, ..) = e {
            if let Expr::Ident(n, _) = callee.as_ref() {
                if n == name { found = true; }
            }
        }
    });
    found
}

/// Does this expression have observable side effects if evaluated more than
/// once? Conservative: any `Call`/`MethodCall`/`Assign` counts as a side
/// effect. Plain identifiers, literals, and pure arithmetic do not.
fn expr_has_side_effects(expr: &Expr) -> bool {
    let mut has = false;
    walk_expr(expr, &mut |e| {
        match e {
            Expr::Call(..) | Expr::MethodCall(..) |
            Expr::Assign(..) | Expr::CompoundAssign(..) |
            Expr::Await(..) => has = true,
              _ => {}
        }
    });
    has
}

/// Count how many times identifier `name` appears (as a bare `Expr::Ident`)
/// within `expr`.
fn count_ident_uses(expr: &Expr, name: &str) -> usize {
    let mut count = 0;
    walk_expr(expr, &mut |e| {
        if let Expr::Ident(n, _) = e {
            if n == name { count += 1; }
        }
    });
    count
}

/// Replace every `Expr::Ident(name, _)` matching a key in `subst` with a
/// clone of the corresponding replacement expression.
fn substitute_idents(expr: &mut Expr, subst: &HashMap<String, Expr>) {
    if let Expr::Ident(name, _) = expr {
        if let Some(repl) = subst.get(name) {
            *expr = repl.clone();
            return;
        }
    }
    walk_expr_mut(expr, &mut |e| substitute_idents(e, subst));
}

/// Recursively overwrite every span in `expr` with `span` (so an inlined
/// expression reports errors/locations at the call site, not the original
/// function definition — better diagnostics, see §1).
fn retag_span(expr: &mut Expr, span: &Span) {
    *expr_span_mut(expr) = span.clone();
    walk_expr_mut(expr, &mut |e| retag_span(e, span));
}

fn expr_span_mut(expr: &mut Expr) -> &mut Span {
    match expr {
        Expr::Literal(_, s) | Expr::Ident(_, s) | Expr::BinOp(_, _, _, s) |
        Expr::UnOp(_, _, s) | Expr::Assign(_, _, s) | Expr::CompoundAssign(_, _, _, s) |
        Expr::FieldAccess(_, _, s) | Expr::IndexAccess(_, _, s) |
        Expr::MethodCall(_, _, _, s) | Expr::Call(_, _, s) |
        Expr::If { span: s, .. } | Expr::Match { span: s, .. } |
        Expr::While { span: s, .. } | Expr::For { span: s, .. } |
        Expr::Do { span: s, .. } | Expr::StructLit(_, _, s) |
        Expr::ArrayLit(_, s) | Expr::TupleLit(_, s) |
        Expr::Closure { span: s, .. } | Expr::Cast(_, _, s) |
        Expr::Range(_, _, _, s) | Expr::Unsafe(_, _, s) |
        Expr::Return(_, s) | Expr::SelfExpr(s) | Expr::Try(_, s) |
        Expr::Await(_, s) | Expr::Path(_, s) => s,
    }
}

/// Generic single-level child-expression visitor (immutable). Used by the
/// read-only helper functions above. Does NOT recurse into statement bodies
/// of nested blocks (if/while/for/match/closure) — those are walked
/// separately by `optimize_block` during the main pass. This keeps the
/// helper functions (recursion detection, side-effect check, ident
/// counting) focused on the *expression* being considered for inlining,
/// which by construction (single-expression-body) never contains nested
/// blocks anyway.
fn walk_expr(expr: &Expr, f: &mut impl FnMut(&Expr)) {
    f(expr);
    match expr {
        Expr::BinOp(l, _, r, _) | Expr::Range(l, r, _, _) => { walk_expr(l, f); walk_expr(r, f); }
        Expr::UnOp(_, e, _) | Expr::Cast(e, _, _) | Expr::Try(e, _) | Expr::Await(e, _) => walk_expr(e, f),
        Expr::Assign(l, r, _) | Expr::CompoundAssign(l, _, r, _) => { walk_expr(l, f); walk_expr(r, f); }
        Expr::FieldAccess(e, _, _) => walk_expr(e, f),
        Expr::IndexAccess(e, i, _) => { walk_expr(e, f); walk_expr(i, f); }
        Expr::MethodCall(recv, _, args, _) => { walk_expr(recv, f); for a in args { walk_expr(a, f); } }
        Expr::Call(callee, args, _) => { walk_expr(callee, f); for a in args { walk_expr(a, f); } }
        Expr::ArrayLit(elems, _) | Expr::TupleLit(elems, _) => { for e in elems { walk_expr(e, f); } }
        Expr::StructLit(_, fields, _) => { for (_, e) in fields { walk_expr(e, f); } }
        Expr::Return(Some(e), _) => walk_expr(e, f),
        _ => {}
    }
}

fn walk_expr_mut(expr: &mut Expr, f: &mut impl FnMut(&mut Expr)) {
    match expr {
        Expr::BinOp(l, _, r, _) | Expr::Range(l, r, _, _) => { f(l); f(r); }
        Expr::UnOp(_, e, _) | Expr::Cast(e, _, _) | Expr::Try(e, _) | Expr::Await(e, _) => f(e),
        Expr::Assign(l, r, _) | Expr::CompoundAssign(l, _, r, _) => { f(l); f(r); }
        Expr::FieldAccess(e, _, _) => f(e),
        Expr::IndexAccess(e, i, _) => { f(e); f(i); }
        Expr::MethodCall(recv, _, args, _) => { f(recv); for a in args { f(a); } }
        Expr::Call(callee, args, _) => { f(callee); for a in args { f(a); } }
        Expr::ArrayLit(elems, _) | Expr::TupleLit(elems, _) => { for e in elems { f(e); } }
        Expr::StructLit(_, fields, _) => { for (_, e) in fields { f(e); } }
        Expr::Return(Some(e), _) => f(e),
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use hsharp_parser::parse;

    fn optimize_src(src: &str) -> Module {
        let result = parse(src, "<test>");
        assert!(!result.has_errors(), "{:?}", result.errors);
        let (m, _) = OptimizeContext::new().run(result.module);
        m
    }

    #[test]
    fn folds_int_arithmetic() {
        let m = optimize_src("fn f() -> int is\n    return 2 + 3 * 4\nend\n");
        let Item::FnDef(f) = &m.items[0] else { panic!() };
        let Stmt::Return(Some(Expr::Literal(Literal::Int(n), _)), _) = &f.body[0] else {
            panic!("expected folded int literal, got {:?}", f.body[0]);
        };
        assert_eq!(*n, 14);
    }

    #[test]
    fn folds_string_concat_chain() {
        let m = optimize_src(r#"fn f() -> string is
        return "a" + "b" + "c"
        end
        "#);
        let Item::FnDef(f) = &m.items[0] else { panic!() };
        let Stmt::Return(Some(Expr::Literal(Literal::String(s), _)), _) = &f.body[0] else {
            panic!("expected folded string, got {:?}", f.body[0]);
        };
        assert_eq!(s, "abc");
    }

    #[test]
    fn eliminates_dead_branch() {
        let m = optimize_src(r#"fn f() -> int is
        if true is
            return 1
            else is
                return 2
                end
                end
                "#);
            let Item::FnDef(f) = &m.items[0] else { panic!() };
        assert_eq!(f.body.len(), 1);
        assert!(matches!(&f.body[0], Stmt::Return(Some(Expr::Literal(Literal::Int(1), _)), _)));
    }

    #[test]
    fn inlines_simple_fn() {
        let m = optimize_src(r#"#[inline]
        fn double(x: int) -> int is
        return x * 2
        end

        fn f() -> int is
        return double(21)
        end
        "#);
        let Item::FnDef(f) = &m.items[1] else { panic!() };
        // double(21) -> 21 * 2 -> folded to 42
        let Stmt::Return(Some(Expr::Literal(Literal::Int(n), _)), _) = &f.body[0] else {
            panic!("expected inlined+folded int, got {:?}", f.body[0]);
        };
        assert_eq!(*n, 42);
    }
}
