use hsharp_parser::ast::*;
use std::collections::HashMap;

pub type TypeSubst = HashMap<String, TypeExpr>;

pub fn mono_fn(f: &FnDef, subst: &TypeSubst) -> FnDef {
    FnDef {
        attrs:       f.attrs.clone(),
        type_params: vec![],
        name:        mono_name(&f.name, subst),
        params:      f.params.iter().map(|p| Param {
            name: p.name.clone(), ty: subst_type(&p.ty, subst),
            mutable: p.mutable, span: p.span.clone(),
        }).collect(),
        return_type: f.return_type.as_ref().map(|t| subst_type(t, subst)),
        body:        mono_stmts(&f.body, subst),
        pub_: f.pub_, is_async: f.is_async, is_unsafe: f.is_unsafe, span: f.span.clone(),
    }
}

pub fn mono_name(base: &str, subst: &TypeSubst) -> String {
    if subst.is_empty() { return base.to_string(); }
    let mut parts: Vec<String> = subst.values().map(type_to_str).collect();
    parts.sort();
    format!("{}__{}", base, parts.join("__"))
}

fn type_to_str(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Named(n)       => n.clone(),
        TypeExpr::Generic(n, a)  => format!("{}__{}", n, a.iter().map(type_to_str).collect::<Vec<_>>().join("__")),
        TypeExpr::Array(t)       => format!("arr_{}", type_to_str(t)),
        TypeExpr::Optional(t)    => format!("opt_{}", type_to_str(t)),
        TypeExpr::Tuple(ts)      => format!("tup_{}", ts.iter().map(type_to_str).collect::<Vec<_>>().join("_")),
        _                        => "t".to_string(),
    }
}

pub fn subst_type(ty: &TypeExpr, subst: &TypeSubst) -> TypeExpr {
    match ty {
        TypeExpr::Named(n) => subst.get(n).cloned().unwrap_or(ty.clone()),
        TypeExpr::Generic(n, args) => {
            if let Some(c) = subst.get(n) { c.clone() }
            else { TypeExpr::Generic(n.clone(), args.iter().map(|a| subst_type(a, subst)).collect()) }
        }
        TypeExpr::Array(t)    => TypeExpr::Array(Box::new(subst_type(t, subst))),
        TypeExpr::Optional(t) => TypeExpr::Optional(Box::new(subst_type(t, subst))),
        TypeExpr::Tuple(ts)   => TypeExpr::Tuple(ts.iter().map(|t| subst_type(t, subst)).collect()),
        other                  => other.clone(),
    }
}

pub fn mono_stmts(stmts: &[Stmt], subst: &TypeSubst) -> Vec<Stmt> {
    stmts.iter().map(|s| mono_stmt(s, subst)).collect()
}

fn mono_stmt(stmt: &Stmt, subst: &TypeSubst) -> Stmt {
    match stmt {
        Stmt::Let { name, ty, mutable, value, span } => Stmt::Let {
            name: name.clone(),
            ty:   ty.as_ref().map(|t| subst_type(t, subst)),
            mutable: *mutable,
            value: value.as_ref().map(|e| mono_expr(e, subst)),
            span: span.clone(),
        },
        Stmt::Return(e, s)    => Stmt::Return(e.as_ref().map(|e| mono_expr(e, subst)), s.clone()),
        Stmt::Expr(e, s)      => Stmt::Expr(mono_expr(e, subst), s.clone()),
        Stmt::Break(e, s)     => Stmt::Break(e.as_ref().map(|e| mono_expr(e, subst)), s.clone()),
        other                  => other.clone(),
    }
}

fn mono_expr(expr: &Expr, subst: &TypeSubst) -> Expr {
    match expr {
        Expr::Call(callee, args, s) => Expr::Call(
            Box::new(mono_expr(callee, subst)),
            args.iter().map(|a| mono_expr(a, subst)).collect(),
            s.clone(),
        ),
        Expr::If { condition, then_body, elsif_branches, else_body, span } => Expr::If {
            condition: Box::new(mono_expr(condition, subst)),
            then_body: mono_stmts(then_body, subst),
            elsif_branches: elsif_branches.iter().map(|(c, b)| (mono_expr(c, subst), mono_stmts(b, subst))).collect(),
            else_body: else_body.as_ref().map(|b| mono_stmts(b, subst)),
            span: span.clone(),
        },
        Expr::BinOp(l, op, r, s) => Expr::BinOp(Box::new(mono_expr(l, subst)), op.clone(), Box::new(mono_expr(r, subst)), s.clone()),
        Expr::UnOp(op, e, s)     => Expr::UnOp(op.clone(), Box::new(mono_expr(e, subst)), s.clone()),
        Expr::Return(e, s)       => Expr::Return(e.as_ref().map(|e| Box::new(mono_expr(e, subst))), s.clone()),
        Expr::Await(e, s)        => Expr::Await(Box::new(mono_expr(e, subst)), s.clone()),
        Expr::Try(e, s)          => Expr::Try(Box::new(mono_expr(e, subst)), s.clone()),
        other                     => other.clone(),
    }
}
