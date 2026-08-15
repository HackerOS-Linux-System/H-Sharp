use hsharp_parser::ast::*;
use std::collections::HashSet;

pub fn lower_consts(module: &mut Module) {
    let mut const_names: HashSet<String> = HashSet::new();
    let mut new_items = Vec::with_capacity(module.items.len());

    for item in module.items.drain(..) {
        if let Item::ConstDef { name, ty, value, pub_, span } = item {
            const_names.insert(name.clone());
            let thunk = FnDef {
                attrs:       vec![],
                type_params: vec![],
                name:        thunk_name(&name),
                params:      vec![],
                return_type: ty,
                body:        vec![Stmt::Return(Some(value), span.clone())],
                pub_,
                is_unsafe:   false,
                is_async:    false,
                mem_mode:    MemoryMode::default(),
                span,
            };
            new_items.push(Item::FnDef(thunk));
        } else {
            new_items.push(item);
        }
    }
    module.items = new_items;

    if const_names.is_empty() { return; }
    for item in &mut module.items {
        rewrite_item(item, &const_names);
    }
}

fn thunk_name(const_name: &str) -> String {
    format!("__hsh_const_{}", const_name)
}

fn rewrite_item(item: &mut Item, names: &HashSet<String>) {
    match item {
        Item::FnDef(f) => rewrite_block(&mut f.body, names),
        Item::ImplBlock(imp) => {
            for m in &mut imp.methods { rewrite_block(&mut m.body, names); }
        }
        Item::ModDecl { inline: Some(items), .. } => {
            for it in items { rewrite_item(it, names); }
        }
        // StructDef/EnumDef/TraitDef/TypeAlias/Extern/ConstDef (already
        // consumed above)/ModDecl-without-inline: nothing with a
        // `const`-referencing expression body to rewrite.
        _ => {}
    }
}

fn rewrite_block(stmts: &mut [Stmt], names: &HashSet<String>) {
    for s in stmts { rewrite_stmt(s, names); }
}

fn rewrite_stmt(stmt: &mut Stmt, names: &HashSet<String>) {
    match stmt {
        Stmt::Let { value: Some(e), .. } => rewrite_expr(e, names),
        Stmt::Let { value: None, .. } => {}
        Stmt::Expr(e, _) => rewrite_expr(e, names),
        Stmt::Return(Some(e), _) => rewrite_expr(e, names),
        Stmt::Return(None, _) => {}
        Stmt::Break(Some(e), _) => rewrite_expr(e, names),
        Stmt::Break(None, _) => {}
        Stmt::Continue(_) => {}
        Stmt::Import(..) => {}
        Stmt::Item(it) => rewrite_item(it, names),
    }
}

fn rewrite_expr(expr: &mut Expr, names: &HashSet<String>) {
    match expr {
        Expr::Ident(name, span) => {
            if names.contains(name.as_str()) {
                *expr = Expr::Call(
                    Box::new(Expr::Ident(thunk_name(name), span.clone())),
                    vec![],
                    span.clone(),
                );
            }
        }
        Expr::Literal(..) | Expr::SelfExpr(_) | Expr::Path(..) => {}
        Expr::BinOp(l, _, r, _) => { rewrite_expr(l, names); rewrite_expr(r, names); }
        Expr::UnOp(_, e, _) => rewrite_expr(e, names),
        Expr::Assign(l, r, _) => { rewrite_expr(l, names); rewrite_expr(r, names); }
        Expr::CompoundAssign(l, _, r, _) => { rewrite_expr(l, names); rewrite_expr(r, names); }
        Expr::FieldAccess(e, _, _) => rewrite_expr(e, names),
        Expr::IndexAccess(e, i, _) => { rewrite_expr(e, names); rewrite_expr(i, names); }
        Expr::MethodCall(recv, _, args, _) => {
            rewrite_expr(recv, names);
            for a in args { rewrite_expr(a, names); }
        }
        Expr::Call(callee, args, _) => {
            rewrite_expr(callee, names);
            for a in args { rewrite_expr(a, names); }
        }
        Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
            rewrite_expr(condition, names);
            rewrite_block(then_body, names);
            for (c, b) in elsif_branches { rewrite_expr(c, names); rewrite_block(b, names); }
            if let Some(b) = else_body { rewrite_block(b, names); }
        }
        Expr::Match { subject, arms, .. } => {
            rewrite_expr(subject, names);
            for arm in arms {
                if let Some(guard) = &mut arm.guard { rewrite_expr(guard, names); }
                rewrite_block(&mut arm.body, names);
            }
        }
        Expr::While { condition, body, .. } => { rewrite_expr(condition, names); rewrite_block(body, names); }
        Expr::For { iterable, body, .. } => { rewrite_expr(iterable, names); rewrite_block(body, names); }
        Expr::Do { body, .. } => rewrite_block(body, names),
        Expr::StructLit(_, fields, _) => { for (_, e) in fields { rewrite_expr(e, names); } }
        Expr::ArrayLit(items, _) => { for e in items { rewrite_expr(e, names); } }
        Expr::TupleLit(items, _) => { for e in items { rewrite_expr(e, names); } }
        Expr::Closure { body, .. } => rewrite_block(body, names),
        Expr::Cast(e, _, _) => rewrite_expr(e, names),
        Expr::Range(a, b, _, _) => { rewrite_expr(a, names); rewrite_expr(b, names); }
        Expr::Unsafe(body, _, _) => rewrite_block(body, names),
        Expr::Return(Some(e), _) => rewrite_expr(e, names),
        Expr::Return(None, _) => {}
        Expr::Try(e, _) => rewrite_expr(e, names),
        Expr::Await(e, _) => rewrite_expr(e, names),
    }
}
