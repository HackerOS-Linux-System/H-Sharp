use crate::ast::*;
use crate::lexer::Token;
use chumsky::prelude::*;
use chumsky::recursive::Recursive;

#[derive(Clone)]
enum IdentSuffix {
    Union(String, Box<HSharpExpr>),
    Struct(Vec<HSharpExpr>),
    Call(Vec<HSharpExpr>),
    Var,
}

#[derive(Clone)]
enum PostfixOp {
    Field(String),
    Method(String, Vec<HSharpExpr>),
    Index(Box<HSharpExpr>),
}

pub fn parser() -> impl Parser<Token, HSharpProgram, Error = Simple<Token>> {
    recursive(|stmt| {
        let ty = recursive(|ty| {
            choice((
                select! { Token::I8Type => HType::I8 },
                select! { Token::I32Type => HType::I32 },
                select! { Token::I64Type => HType::I64 },
                select! { Token::BoolType => HType::Bool },
                select! { Token::F32Type => HType::F32 },
                select! { Token::F64Type => HType::F64 },
                select! { Token::UnitType => HType::Unit },
                just(Token::Star).ignore_then(ty.clone()).map(|t| HType::Pointer(Box::new(t))),

                    // Generics: List<Int>
                    select! { Token::Ident(s) => s }
                    .then(
                        just(Token::Lt)
                        .ignore_then(ty.clone().separated_by(just(Token::Comma)))
                        .then_ignore(just(Token::Gt))
                        .or_not()
                    )
                    .map(|(name, generics)| {
                        HType::Struct(name, generics.unwrap_or_default())
                    }),

                    // Array: [T; 10]
                    just(Token::LBracket)
                    .ignore_then(ty.clone())
                    .then(just(Token::Semi).ignore_then(select! { Token::Num(n) => n as usize }).or_not())
                    .then_ignore(just(Token::RBracket))
                    .map(|(inner, size)| {
                        if let Some(s) = size {
                            HType::Array(Box::new(inner), s)
                        } else {
                            HType::Slice(Box::new(inner))
                        }
                    }),
                    just(Token::LParen).ignore_then(ty).then_ignore(just(Token::RParen)),
            ))
        });

        let expr = recursive(|expr: Recursive<'_, Token, HSharpExpr, Simple<Token>>| {
            let literal = choice((
                select! { Token::Num(n) => HSharpLiteral::Int(n) },
                                  select! { Token::Float(f) => HSharpLiteral::Float(f) },
                                  select! { Token::True => HSharpLiteral::Bool(true) },
                                  select! { Token::False => HSharpLiteral::Bool(false) },
                                  select! { Token::String(s) => HSharpLiteral::String(s) },
            ))
            .map(HSharpExpr::Literal);

            let ident_parser = select! { Token::Ident(s) => s };

            let block = just(Token::LBrace)
            .ignore_then(stmt.clone().repeated())
            .then_ignore(just(Token::RBrace))
            .map(HSharpExpr::Block);

            let ident_suffix = choice((
                just(Token::Dot)
                .ignore_then(ident_parser.clone())
                .then(just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)))
                .map(|(field, e)| IdentSuffix::Union(field, Box::new(e))),

                                       just(Token::LBrace)
                                       .ignore_then(expr.clone().separated_by(just(Token::Comma)))
                                       .then_ignore(just(Token::RBrace))
                                       .map(IdentSuffix::Struct),

                                       just(Token::LParen)
                                       .ignore_then(expr.clone().separated_by(just(Token::Comma)))
                                       .then_ignore(just(Token::RParen))
                                       .map(IdentSuffix::Call),

                                       empty().to(IdentSuffix::Var),
            ));

            let match_case = expr.clone()
            .then_ignore(just(Token::DoubleArrow))
            .then(expr.clone().or(block.clone()));

            let atom = choice((
                literal,
                ident_parser.clone().then(ident_suffix)
                .map(|(name, suffix)| match suffix {
                    IdentSuffix::Union(f, e) => HSharpExpr::UnionLit(name, f, e),
                     IdentSuffix::Struct(fields) => HSharpExpr::StructLit(name, fields),
                     IdentSuffix::Call(args) => HSharpExpr::Call(name, args),
                     IdentSuffix::Var => HSharpExpr::Var(name),
                }),
                just(Token::Break).to(HSharpExpr::Break),
                               just(Token::Continue).to(HSharpExpr::Continue),
                               just(Token::Match)
                               .ignore_then(expr.clone())
                               .then(just(Token::LBrace)
                               .ignore_then(match_case.separated_by(just(Token::Comma)).allow_trailing())
                               .then(just(Token::Else).ignore_then(just(Token::DoubleArrow)).ignore_then(expr.clone().or(block.clone())).or_not())
                               .then_ignore(just(Token::RBrace)))
                               .map(|(target, (cases, default_))| HSharpExpr::Match(Box::new(target), cases, default_.map(Box::new))),
                               just(Token::Alloc)
                               .ignore_then(just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)))
                               .map(|e| HSharpExpr::Alloc(Box::new(e))),
                               just(Token::Dealloc)
                               .ignore_then(just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)))
                               .map(|e| HSharpExpr::Dealloc(Box::new(e))),
                               just(Token::Write)
                               .ignore_then(just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)))
                               .map(|e| HSharpExpr::Write(Box::new(e))),
                               just(Token::Cast)
                               .ignore_then(just(Token::LParen))
                               .ignore_then(ty.clone())
                               .then_ignore(just(Token::Comma))
                               .then(expr.clone())
                               .then_ignore(just(Token::RParen))
                               .map(|(t, e)| HSharpExpr::Cast(t, Box::new(e))),
                               just(Token::SizeOf)
                               .ignore_then(just(Token::LParen).ignore_then(ty.clone()).then_ignore(just(Token::RParen)))
                               .map(|t| HSharpExpr::SizeOf(t)),
                               just(Token::Direct)
                               .ignore_then(block.clone())
                               .map(|b| HSharpExpr::Direct(Box::new(b))),
                               just(Token::If)
                               .ignore_then(expr.clone())
                               .then(block.clone())
                               .then(just(Token::Else).ignore_then(block.clone()).or_not())
                               .map(|((cond, then), else_): ((HSharpExpr, HSharpExpr), Option<HSharpExpr>)| HSharpExpr::If(Box::new(cond), Box::new(then), else_.map(Box::new))),
                               just(Token::While)
                               .ignore_then(expr.clone())
                               .then(block.clone())
                               .map(|(cond, body)| HSharpExpr::While(Box::new(cond), Box::new(body))),
                               just(Token::For)
                               .ignore_then(ident_parser.clone())
                               .then_ignore(just(Token::Eq))
                               .then(expr.clone())
                               .then_ignore(just(Token::Lt))
                               .then(expr.clone())
                               .then(block.clone())
                               .map(|(((var, start), end), body)| HSharpExpr::For(var, Box::new(start), Box::new(end), Box::new(body))),
                               just(Token::Return)
                               .ignore_then(expr.clone())
                               .map(|e| HSharpExpr::Return(Box::new(e))),
                               just(Token::LBracket)
                               .ignore_then(expr.clone().separated_by(just(Token::Comma)))
                               .then_ignore(just(Token::RBracket))
                               .map(HSharpExpr::ArrayLit),
                               just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)),
                               block,
            ));

            let unary = recursive(|unary| {
                choice((
                    just(Token::Star).ignore_then(unary.clone()).map(|e| HSharpExpr::Deref(Box::new(e))),
                        just(Token::Amp).ignore_then(unary.clone()).map(|e| HSharpExpr::AddrOf(Box::new(e))),
                        atom,
                ))
            });

            let postfix_op = choice((
                just(Token::Dot).ignore_then(ident_parser.clone())
                .then(just(Token::LParen).ignore_then(expr.clone().separated_by(just(Token::Comma))).then_ignore(just(Token::RParen)).or_not())
                .map(|(field, args_opt)| if let Some(args) = args_opt { PostfixOp::Method(field, args) } else { PostfixOp::Field(field) }),
                                     just(Token::LBracket).ignore_then(expr.clone()).then_ignore(just(Token::RBracket)).map(|i| PostfixOp::Index(Box::new(i))),
            ));

            let postfix = unary.clone()
            .then(postfix_op.repeated())
            .foldl(|left, op| match op {
                PostfixOp::Field(f) => HSharpExpr::Field(Box::new(left), f),
                   PostfixOp::Method(m, args) => HSharpExpr::MethodCall(Box::new(left), m, args),
                   PostfixOp::Index(i) => HSharpExpr::Index(Box::new(left), i),
            });

            let cast = postfix
            .then(just(Token::As).ignore_then(ty.clone()).or_not())
            .map(|(e, opt_ty)| {
                if let Some(ty) = opt_ty {
                    HSharpExpr::Cast(ty, Box::new(e))
                } else {
                    e
                }
            });

            let product_op = choice((
                just(Token::Star).to(HSharpOp::Mul),
                                     just(Token::Slash).to(HSharpOp::Div),
                                     just(Token::Percent).to(HSharpOp::Mod),
            ));
            let product = cast.clone()
            .then(product_op.then(cast.clone()).repeated())
            .foldl(|lhs, (op, rhs)| HSharpExpr::BinOp(op, Box::new(lhs), Box::new(rhs)));

            let sum_op = choice((
                just(Token::Plus).to(HSharpOp::Add),
                                 just(Token::Minus).to(HSharpOp::Sub),
            ));
            let sum = product.clone()
            .then(sum_op.then(product.clone()).repeated())
            .foldl(|lhs, (op, rhs)| HSharpExpr::BinOp(op, Box::new(lhs), Box::new(rhs)));

            let cmp_op = choice((
                just(Token::EqEq).to(HSharpOp::Eq),
                                 just(Token::Ne).to(HSharpOp::Ne),
                                 just(Token::Le).to(HSharpOp::Le),
                                 just(Token::Ge).to(HSharpOp::Ge),
                                 just(Token::Lt).to(HSharpOp::Lt),
                                 just(Token::Gt).to(HSharpOp::Gt),
            ));
            let compare = sum.clone()
            .then(cmp_op.then(sum.clone()).repeated())
            .foldl(|lhs, (op, rhs)| HSharpExpr::BinOp(op, Box::new(lhs), Box::new(rhs)));

            let logic_op = choice((
                just(Token::AndAnd).to(HSharpOp::And),
                                   just(Token::OrOr).to(HSharpOp::Or),
            ));

            let logic = compare.clone()
            .then(logic_op.then(compare.clone()).repeated())
            .foldl(|lhs, (op, rhs)| HSharpExpr::BinOp(op, Box::new(lhs), Box::new(rhs)));

            logic.clone()
            .then(just(Token::Eq).ignore_then(expr.clone()).or_not())
            .map(|(lhs, rhs)| {
                if let Some(r) = rhs {
                    HSharpExpr::Assign(Box::new(lhs), Box::new(r))
                } else {
                    lhs
                }
            })
        });

        let ident_parser = select! { Token::Ident(s) => s };

        let param = choice((
            ident_parser.clone().then(just(Token::Colon).ignore_then(ty.clone())).map(|(name, ty)| (name, ty)),
                            just(Token::Ellipsis).to(("...".to_string(), HType::Unit))
        ));

        let field_def = ident_parser.clone().then_ignore(just(Token::Colon)).then(ty.clone());

        let let_stmt = just(Token::Let)
        .ignore_then(ident_parser.clone())
        .then(just(Token::Colon).ignore_then(ty.clone()).or_not())
        .then_ignore(just(Token::Eq))
        .then(expr.clone())
        .then_ignore(just(Token::Semi))
        .map(|((name, ty), e)| HSharpStmt::Let(name, ty, e));

        let expr_stmt = expr.clone()
        .then(just(Token::Semi).or_not())
        .map(|(e, _)| HSharpStmt::Expr(e));

        // Fix: Use .or_not() then direct wrapping, do not wrap Option in Option
        let fn_stmt = just(Token::Fn)
        .ignore_then(ident_parser.clone())
        .then(just(Token::LParen).ignore_then(param.separated_by(just(Token::Comma))).then_ignore(just(Token::RParen)))
        .then(just(Token::Arrow).ignore_then(ty.clone()).or_not())
        .then(expr.clone().map(Box::new).or_not())
        .map(|(((name, params), ret), body)| HSharpStmt::FunctionDef(name, params, ret.unwrap_or(HType::Unit), body));

        let struct_def = just(Token::Struct)
        .ignore_then(ident_parser.clone())
        .then(
            just(Token::Lt)
            .ignore_then(ident_parser.clone().separated_by(just(Token::Comma)))
            .then_ignore(just(Token::Gt))
            .or_not()
        )
        .then(just(Token::LBrace).ignore_then(field_def.clone().separated_by(just(Token::Comma)).allow_trailing()).then_ignore(just(Token::RBrace)))
        .map(|((name, generics), fields)| HSharpStmt::StructDef(name, generics.unwrap_or_default(), fields));

        let union_def = just(Token::Union)
        .ignore_then(ident_parser.clone())
        .then(just(Token::LBrace).ignore_then(field_def.separated_by(just(Token::Comma)).allow_trailing()).then_ignore(just(Token::RBrace)))
        .map(|(name, fields)| HSharpStmt::UnionDef(name, fields));

        let impl_block = just(Token::Impl)
        .ignore_then(ident_parser.clone())
        .then(just(Token::LBrace).ignore_then(fn_stmt.clone().repeated()).then_ignore(just(Token::RBrace)))
        .map(|(name, stmts)| HSharpStmt::Impl(name, stmts));

        let require_item = ident_parser.clone().then(just(Token::Colon).ignore_then(ident_parser.clone()).or_not()).map(|(m, opt_s)| if let Some(s) = opt_s { RequireItem::Specific(m, s) } else { RequireItem::WholeModule(m) });
        let import_stmt = just(Token::From)
        .ignore_then(just(Token::LBracket).ignore_then(ident_parser.clone()).then_ignore(just(Token::RBracket)))
        .then(just(Token::Require).ignore_then(just(Token::LBracket).ignore_then(require_item.separated_by(just(Token::Comma))).then_ignore(just(Token::RBracket))))
        .then_ignore(just(Token::Semi))
        .map(|(from, requires)| HSharpStmt::Import(from, requires));

        choice((let_stmt, fn_stmt, import_stmt, struct_def, union_def, impl_block, expr_stmt))
    })
    .repeated()
    .map(|stmts| HSharpProgram { stmts })
    .then_ignore(end())
}
