use hsharp_parser::ast::*;

/// For each struct with #[derive(...)], generate the corresponding FnDefs
pub fn expand_derives(module: &Module) -> Vec<Item> {
    let mut generated = Vec::new();
    
    for item in &module.items {
        if let Item::StructDef(s) = item {
            for attr in &s.attrs {
                if attr.name == "derive" {
                    for arg in &attr.args {
                        let trait_name = match arg {
                            AttrArg::Ident(n) => n.as_str(),
                            _ => continue,
                        };
                        let fns = generate_derive_impl(&s, trait_name);
                        generated.extend(fns.into_iter().map(Item::FnDef));
                    }
                }
            }
        }
    }
    generated
}

/// Generate method implementations for a single derived trait
fn generate_derive_impl(s: &StructDef, trait_name: &str) -> Vec<FnDef> {
    let span = s.span.clone();
    
    match trait_name {
        "Debug" => vec![make_fn(&s.name, "debug", vec![], Some(TypeExpr::Named("string".into())), {
            // body: return "StructName { field1: <val>, ... }"
            let mut body = Vec::new();
            // let __result = "StructName { "
            let name_str = format!("{} {{ ", s.name);
            body.push(Stmt::Let {
                name: "__dbg_out".into(),
                ty: Some(TypeExpr::Named("string".into())),
                mutable: true,
                value: Some(Expr::Literal(Literal::String(name_str), span.clone())),
                span: span.clone(),
            });
            for (i, field) in s.fields.iter().enumerate() {
                // __dbg_out = __dbg_out + "field_name: " + to_string(self.field_name)
                let sep = if i > 0 { format!(", {}: ", field.name) } else { format!("{}: ", field.name) };
                let concat = Expr::BinOp(
                    Box::new(Expr::BinOp(
                        Box::new(Expr::Ident("__dbg_out".into(), span.clone())),
                        BinOp::Add,
                        Box::new(Expr::Literal(Literal::String(sep), span.clone())),
                        span.clone(),
                    )),
                    BinOp::Add,
                    Box::new(Expr::Call(
                        Box::new(Expr::Ident("to_string".into(), span.clone())),
                        vec![Expr::FieldAccess(
                            Box::new(Expr::SelfExpr(span.clone())),
                            field.name.clone(),
                            span.clone(),
                        )],
                        span.clone(),
                    )),
                    span.clone(),
                );
                body.push(Stmt::Expr(Expr::Assign(
                    Box::new(Expr::Ident("__dbg_out".into(), span.clone())),
                    Box::new(concat),
                    span.clone(),
                ), span.clone()));
            }
            // __dbg_out = __dbg_out + " }"
            body.push(Stmt::Expr(Expr::Assign(
                Box::new(Expr::Ident("__dbg_out".into(), span.clone())),
                Box::new(Expr::BinOp(
                    Box::new(Expr::Ident("__dbg_out".into(), span.clone())),
                    BinOp::Add,
                    Box::new(Expr::Literal(Literal::String(" }".into()), span.clone())),
                    span.clone(),
                )),
                span.clone(),
            ), span.clone()));
            body.push(Stmt::Return(Some(Expr::Ident("__dbg_out".into(), span.clone())), span.clone()));
            body
        }, span.clone())],

        "Clone" => vec![make_fn(&s.name, "clone", vec![], Some(TypeExpr::Named(s.name.clone())), {
            // body: return Self { field1: self.field1, field2: self.field2, ... }
            let fields: Vec<(String, Expr)> = s.fields.iter().map(|f| (
                f.name.clone(),
                Expr::FieldAccess(Box::new(Expr::SelfExpr(span.clone())), f.name.clone(), span.clone()),
            )).collect();
            vec![Stmt::Return(Some(Expr::StructLit(s.name.clone(), fields, span.clone())), span.clone())]
        }, span.clone())],

        "PartialEq" | "Eq" => vec![make_fn(&s.name, "eq",
            vec![Param { name: "other".into(), ty: TypeExpr::Named(s.name.clone()), mutable: false, span: span.clone() }],
            Some(TypeExpr::Named("bool".into())),
            {
                // body: return self.f1 == other.f1 && self.f2 == other.f2 && ...
                let mut expr = Expr::Literal(Literal::Bool(true), span.clone());
                for field in &s.fields {
                    let self_f = Expr::FieldAccess(Box::new(Expr::SelfExpr(span.clone())), field.name.clone(), span.clone());
                    let other_f = Expr::FieldAccess(Box::new(Expr::Ident("other".into(), span.clone())), field.name.clone(), span.clone());
                    let cmp = Expr::BinOp(Box::new(self_f), BinOp::Eq, Box::new(other_f), span.clone());
                    expr = Expr::BinOp(Box::new(expr), BinOp::And, Box::new(cmp), span.clone());
                }
                vec![Stmt::Return(Some(expr), span.clone())]
            }, span.clone())],

        "Display" => vec![make_fn(&s.name, "to_string", vec![], Some(TypeExpr::Named("string".into())), {
            // Same as Debug but simpler: "StructName(f1=v1, f2=v2)"
            let mut body = Vec::new();
            body.push(Stmt::Let {
                name: "__disp_out".into(),
                ty: Some(TypeExpr::Named("string".into())),
                mutable: true,
                value: Some(Expr::Literal(Literal::String(format!("{}(", s.name)), span.clone())),
                span: span.clone(),
            });
            for (i, field) in s.fields.iter().enumerate() {
                let sep = if i > 0 { format!(", {}=", field.name) } else { format!("{}=", field.name) };
                let concat = Expr::BinOp(
                    Box::new(Expr::BinOp(
                        Box::new(Expr::Ident("__disp_out".into(), span.clone())),
                        BinOp::Add,
                        Box::new(Expr::Literal(Literal::String(sep), span.clone())),
                        span.clone(),
                    )),
                    BinOp::Add,
                    Box::new(Expr::Call(
                        Box::new(Expr::Ident("to_string".into(), span.clone())),
                        vec![Expr::FieldAccess(Box::new(Expr::SelfExpr(span.clone())), field.name.clone(), span.clone())],
                        span.clone(),
                    )),
                    span.clone(),
                );
                body.push(Stmt::Expr(Expr::Assign(
                    Box::new(Expr::Ident("__disp_out".into(), span.clone())),
                    Box::new(concat),
                    span.clone(),
                ), span.clone()));
            }
            body.push(Stmt::Expr(Expr::Assign(
                Box::new(Expr::Ident("__disp_out".into(), span.clone())),
                Box::new(Expr::BinOp(
                    Box::new(Expr::Ident("__disp_out".into(), span.clone())),
                    BinOp::Add,
                    Box::new(Expr::Literal(Literal::String(")".into()), span.clone())),
                    span.clone(),
                )),
                span.clone(),
            ), span.clone()));
            body.push(Stmt::Return(Some(Expr::Ident("__disp_out".into(), span.clone())), span.clone()));
            body
        }, span.clone())],

        "Default" => vec![make_fn(&s.name, "default", vec![], Some(TypeExpr::Named(s.name.clone())), {
            let fields: Vec<(String, Expr)> = s.fields.iter().map(|f| (
                f.name.clone(),
                match &f.ty {
                    TypeExpr::Named(t) if t == "int" || t == "i64" || t == "i32" => Expr::Literal(Literal::Int(0), span.clone()),
                    TypeExpr::Named(t) if t == "float" || t == "f64" => Expr::Literal(Literal::Float(0.0), span.clone()),
                    TypeExpr::Named(t) if t == "bool" => Expr::Literal(Literal::Bool(false), span.clone()),
                    TypeExpr::Named(t) if t == "string" => Expr::Literal(Literal::String(String::new()), span.clone()),
                    _ => Expr::Literal(Literal::Nil, span.clone()),
                }
            )).collect();
            vec![Stmt::Return(Some(Expr::StructLit(s.name.clone(), fields, span.clone())), span.clone())]
        }, span.clone())],

        _ => vec![], // Unknown derive — silently ignore
    }
}

fn make_fn(type_name: &str, method: &str, params: Vec<Param>, ret: Option<TypeExpr>, body: Vec<Stmt>, span: hsharp_parser::span::Span) -> FnDef {
    FnDef {
        attrs: vec![],
        type_params: vec![],
        name: format!("{}_{}", type_name, method),
        params,
        return_type: ret,
        body,
        pub_: true,
        is_async: false,
        is_unsafe: false,
        span,
    }
}
