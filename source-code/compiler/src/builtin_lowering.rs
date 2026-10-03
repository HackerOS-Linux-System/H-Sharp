use hsharp_parser::ast::*;

fn lowered_name(name: &str) -> Option<&'static str> {
    match name {
        "__builtin_str_split" => Some("str_split"),
        "__builtin_str_join"  => Some("iter_join"),
        _ => None,
    }
}

pub fn lower_string_builtins(module: &mut Module) {
    for item in &mut module.items {
        lower_item(item);
    }
}

fn lower_item(item: &mut Item, ) {
    match item {
        Item::FnDef(f) => lower_block(&mut f.body),
        Item::ImplBlock(imp) => {
            for m in &mut imp.methods { lower_block(&mut m.body); }
        }
        Item::ModDecl { inline: Some(items), .. } => {
            for it in items { lower_item(it); }
        }
        // StructDef/EnumDef/TraitDef/TypeAlias/Extern/ConstDef (already
        // consumed above)/ModDecl-without-inline: nothing with a
        // `const`-referencing expression body to rewrite.
        _ => {}
    }
}

fn lower_block(stmts: &mut [Stmt], ) {
    for s in stmts { lower_stmt(s); }
}

fn lower_stmt(stmt: &mut Stmt, ) {
    match stmt {
        Stmt::Let { value: Some(e), .. } => lower_expr(e),
        Stmt::Let { value: None, .. } => {}
        Stmt::Expr(e, _) => lower_expr(e),
        Stmt::Return(Some(e), _) => lower_expr(e),
        Stmt::Return(None, _) => {}
        Stmt::Break(Some(e), _) => lower_expr(e),
        Stmt::Break(None, _) => {}
        Stmt::Continue(_) => {}
        Stmt::Import(..) => {}
        Stmt::Item(it) => lower_item(it),
    }
}

fn lower_expr(expr: &mut Expr, ) {
    match expr {
        Expr::Ident(name, _) => {
            if let Some(target) = lowered_name(name) {
                *name = target.to_string();
            }
        }
        Expr::Literal(..) | Expr::SelfExpr(_) | Expr::Path(..) => {}
        Expr::BinOp(l, _, r, _) => { lower_expr(l); lower_expr(r); }
        Expr::UnOp(_, e, _) => lower_expr(e),
        Expr::Assign(l, r, _) => { lower_expr(l); lower_expr(r); }
        Expr::CompoundAssign(l, _, r, _) => { lower_expr(l); lower_expr(r); }
        Expr::FieldAccess(e, _, _) => lower_expr(e),
        Expr::IndexAccess(e, i, _) => { lower_expr(e); lower_expr(i); }
        Expr::MethodCall(recv, _, args, _) => {
            lower_expr(recv);
            for a in args { lower_expr(a); }
        }
        Expr::Call(callee, args, _) => {
            lower_expr(callee);
            for a in args { lower_expr(a); }
        }
        Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
            lower_expr(condition);
            lower_block(then_body);
            for (c, b) in elsif_branches { lower_expr(c); lower_block(b); }
            if let Some(b) = else_body { lower_block(b); }
        }
        Expr::Match { subject, arms, .. } => {
            lower_expr(subject);
            for arm in arms {
                if let Some(guard) = &mut arm.guard { lower_expr(guard); }
                lower_block(&mut arm.body);
            }
        }
        Expr::While { condition, body, .. } => { lower_expr(condition); lower_block(body); }
        Expr::For { iterable, body, .. } => { lower_expr(iterable); lower_block(body); }
        Expr::Do { body, .. } => lower_block(body),
        Expr::StructLit(_, fields, _) => { for (_, e) in fields { lower_expr(e); } }
        Expr::ArrayLit(items, _) => { for e in items { lower_expr(e); } }
        Expr::TupleLit(items, _) => { for e in items { lower_expr(e); } }
        Expr::Closure { body, .. } => lower_block(body),
        Expr::Cast(e, _, _) => lower_expr(e),
        Expr::Range(a, b, _, _) => { lower_expr(a); lower_expr(b); }
        Expr::Unsafe(body, _, _) => lower_block(body),
        Expr::Return(Some(e), _) => lower_expr(e),
        Expr::Return(None, _) => {}
        Expr::Try(e, _) => lower_expr(e),
        Expr::Await(e, _) => lower_expr(e),
    }
}

/// Removes `#[test]` functions (top level and inside inline `mod`s) from an
/// AOT compilation: they are executed by `hsharp test`, and their
/// `assert_eq`/`assert_true` calls have no definition in a normal build.
pub fn strip_test_fns(module: &mut Module) {
    strip_items(&mut module.items);
}

fn strip_items(items: &mut Vec<Item>) {
    items.retain(|it| match it {
        Item::FnDef(f) => !f.attrs.iter().any(|a| a.name == "test"),
        _ => true,
    });
    for it in items.iter_mut() {
        if let Item::ModDecl { inline: Some(sub), .. } = it {
            strip_items(sub);
        }
    }
}
