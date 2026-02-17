use crate::ast::*;
use crate::lexer::Token;
use chumsky::prelude::*;
use chumsky::recursive::Recursive;

#[derive(Clone)]
enum IdentSuffix {
    Union(String, Vec<HSharpExpr>),
    Struct(Vec<HSharpExpr>),
    Call(Vec<HSharpExpr>),
    Var,
}

#[derive(Clone)]
enum PostfixOp {
    Field(String),
    Method(String, Vec<HSharpExpr>),
    Index(Box<HSharpExpr>),
    Question, // For optional chaining ?.field
}

pub fn parser() -> impl Parser<Token, HSharpProgram, Error = Simple<Token>> {
    recursive(|stmt| {
        let ty = recursive(|ty| {
            choice((
                select! { Token::I8Type => HType::I8 },
                select! { Token::I32Type => HType::I32 },
                select! { Token::I64Type => HType::I64 },
                select! { Token::U8Type => HType::U8 },
                select! { Token::U16Type => HType::U16 },
                select! { Token::U32Type => HType::U32 },
                select! { Token::U64Type => HType::U64 },
                select! { Token::BoolType => HType::Bool },
                select! { Token::F32Type => HType::F32 },
                select! { Token::F64Type => HType::F64 },
                select! { Token::UnitType => HType::Unit },
                just(Token::Star)
                .ignore_then(ty.clone())
                .map(|t| HType::Pointer(Box::new(t))),
                    // Generics: List<Int>
                    select! { Token::Ident(s) => s }
                    .then(
                        just(Token::Lt)
                        .ignore_then(ty.clone().separated_by(just(Token::Comma)))
                        .then_ignore(just(Token::Gt))
                        .or_not(),
                    )
                    .map(|(name, generics)| HType::Struct(name, generics.unwrap_or_default())),
                    // Array: [T; 10] or Slice: [T]
                    just(Token::LBracket)
                    .ignore_then(ty.clone())
                    .then(
                        just(Token::Semi)
                        .ignore_then(select! { Token::Num(n) => n as usize }.or_not()),
                    )
                    .then_ignore(just(Token::RBracket))
                    .map(|(inner, size)| {
                        if let Some(s) = size {
                            HType::Array(Box::new(inner), s)
                        } else {
                            HType::Slice(Box::new(inner))
                        }
                    }),
                    // Tuple: (T1, T2)
                    just(Token::LParen)
                    .ignore_then(ty.clone().separated_by(just(Token::Comma)).allow_trailing())
                    .then_ignore(just(Token::RParen))
                    .map(HType::Tuple),
                    // Grouping: (T)
                    just(Token::LParen)
                    .ignore_then(ty)
                    .then_ignore(just(Token::RParen)),
            ))
        });

        let expr = recursive(|expr: Recursive<'_, Token, HSharpExpr, Simple<Token>>| {
            let literal = choice((
                select! { Token::Num(n) => HSharpLiteral::Int(n.try_into().unwrap()) },
                                  select! { Token::Float(f) => HSharpLiteral::Float(f) },
                                  select! { Token::True => HSharpLiteral::Bool(true) },
                                  select! { Token::False => HSharpLiteral::Bool(false) },
                                  select! { Token::String(s) => HSharpLiteral::String(s) },
                                  select! { Token::RawString(s) => HSharpLiteral::RawString(s) },
                                  select! { Token::ByteChar(b) => HSharpLiteral::Byte(b) },
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
                .then(
                    just(Token::LParen)
                    .ignore_then(
                        expr.clone()
                        .separated_by(just(Token::Comma))
                        .allow_trailing(),
                    )
                    .then_ignore(just(Token::RParen)),
                )
                .map(|(field, e)| {
                    IdentSuffix::Union(field, e)
                }),
                just(Token::LBrace)
                .ignore_then(
                    expr.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing(),
                )
                .then_ignore(just(Token::RBrace))
                .map(IdentSuffix::Struct),
                                       just(Token::LParen)
                                       .ignore_then(
                                           expr.clone()
                                           .separated_by(just(Token::Comma))
                                           .allow_trailing(),
                                       )
                                       .then_ignore(just(Token::RParen))
                                       .map(IdentSuffix::Call),
                                       empty().to(IdentSuffix::Var),
            ));

            let match_case = expr
            .clone()
            .then_ignore(just(Token::DoubleArrow))
            .then(expr.clone().or(block.clone()));

            let atom = choice((
                literal,
                ident_parser.clone().then(ident_suffix).map(|(name, suffix)| match suffix {
                    IdentSuffix::Union(f, args) => HSharpExpr::MethodCall(Box::new(HSharpExpr::Var(name)), f, args),
                                                            IdentSuffix::Struct(fields) => HSharpExpr::StructLit(name, fields),
                                                            IdentSuffix::Call(args) => HSharpExpr::Call(name, args),
                                                            IdentSuffix::Var => HSharpExpr::Var(name),
                }),
                just(Token::Break).to(HSharpExpr::Break),
                               just(Token::Continue).to(HSharpExpr::Continue),
                               just(Token::Match)
                               .ignore_then(expr.clone())
                               .then(
                                   just(Token::LBrace)
                                   .ignore_then(match_case.separated_by(just(Token::Comma)).allow_trailing())
                                   .then(
                                       just(Token::Else)
                                       .ignore_then(just(Token::DoubleArrow))
                                       .ignore_then(expr.clone().or(block.clone()))
                                       .or_not(),
                                   )
                                   .then_ignore(just(Token::RBrace)),
                               )
                               .map(|(target, (cases, default_))| {
                                   HSharpExpr::Match(Box::new(target), cases, default_.map(Box::new))
                               }),
                               just(Token::Alloc)
                               .ignore_then(
                                   just(Token::LParen)
                                   .ignore_then(expr.clone())
                                   .then_ignore(just(Token::RParen)),
                               )
                               .map(|e| HSharpExpr::Alloc(Box::new(e))),
                               just(Token::Dealloc)
                               .ignore_then(
                                   just(Token::LParen)
                                   .ignore_then(expr.clone())
                                   .then_ignore(just(Token::RParen)),
                               )
                               .map(|e| HSharpExpr::Dealloc(Box::new(e))),
                               just(Token::Write)
                               .ignore_then(
                                   just(Token::LParen)
                                   .ignore_then(expr.clone())
                                   .then_ignore(just(Token::RParen)),
                               )
                               .map(|e| HSharpExpr::Write(Box::new(e))),
                               just(Token::Cast)
                               .ignore_then(just(Token::LParen))
                               .ignore_then(ty.clone())
                               .then_ignore(just(Token::Comma))
                               .then(expr.clone())
                               .then_ignore(just(Token::RParen))
                               .map(|(t, e)| HSharpExpr::Cast(t, Box::new(e))),
                               just(Token::SizeOf)
                               .ignore_then(
                                   just(Token::LParen)
                                   .ignore_then(ty.clone())
                                   .then_ignore(just(Token::RParen)),
                               )
                               .map(|t| HSharpExpr::SizeOf(t)),
                               just(Token::Direct)
                               .ignore_then(block.clone())
                               .map(|b| HSharpExpr::Direct(Box::new(b))),
                               just(Token::If)
                               .ignore_then(expr.clone())
                               .then(block.clone())
                               .then(just(Token::Else).ignore_then(block.clone()).or_not())
                               .map(|((cond, then), else_)| {
                                   HSharpExpr::If(Box::new(cond), Box::new(then), else_.map(Box::new))
                               }),
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
                               .map(|(((var, start), end), body)| {
                                   HSharpExpr::For(var, Box::new(start), Box::new(end), Box::new(body))
                               }),
                               just(Token::Return)
                               .ignore_then(expr.clone())
                               .map(|e| HSharpExpr::Return(Box::new(e))),
                               just(Token::LBracket)
                               .ignore_then(expr.clone().separated_by(just(Token::Comma)).allow_trailing())
                               .then_ignore(just(Token::RBracket))
                               .map(HSharpExpr::ArrayLit),
                               // Tuple literal: (1, 2)
                               just(Token::LParen)
                               .ignore_then(expr.clone().separated_by(just(Token::Comma)).allow_trailing())
                               .then_ignore(just(Token::RParen))
                               .map(HSharpExpr::Tuple),
                               // Closure: |x| x + 1
                               just(Token::BitOr)
                               .ignore_then(ident_parser.clone().separated_by(just(Token::Comma)))
                               .then_ignore(just(Token::BitOr))
                               .then(expr.clone())
                               .map(|(params, body)| HSharpExpr::Closure(params, Box::new(body))),
                               // Range: 1..10 or 1..=10
                               expr.clone()
                               .then(just(Token::DotDot).or(just(Token::DotDotEq)))
                               .then(expr.clone())
                               .map(|((start, op), end)| {
                                   let inclusive = matches!(op, Token::DotDotEq);
                                   HSharpExpr::Range(Box::new(start), Box::new(end), inclusive)
                               }),
                               // Await: await future
                               just(Token::Await)
                               .ignore_then(expr.clone())
                               .map(|e| HSharpExpr::Await(Box::new(e))),
                               just(Token::LParen)
                               .ignore_then(expr.clone())
                               .then_ignore(just(Token::RParen)),
                               block,
            ));

            // Unary operators: -, ~, *, &
            let unary_op = choice((
                just(Token::Minus).to(UnaryOp::Neg),
                                   just(Token::BitNot).to(UnaryOp::BitNot),
                                   just(Token::Star).to(UnaryOp::Deref),
                                   just(Token::Amp).to(UnaryOp::AddrOf),
            ));

            let unary = unary_op
            .repeated()
            .then(atom)
            .map(|(ops, rhs): (Vec<UnaryOp>, HSharpExpr)| {
                ops.into_iter()
                .rev()
                .fold(rhs, |acc, op| HSharpExpr::Unary(op, Box::new(acc)))
            });

            // Postfix: .field, [idx], (args), ?.field
            let postfix_op = choice((
                just(Token::Dot)
                .ignore_then(just(Token::Question).or_not().then(ident_parser.clone()))
                .then(
                    just(Token::LParen)
                    .ignore_then(
                        expr.clone()
                        .separated_by(just(Token::Comma))
                        .allow_trailing(),
                    )
                    .then_ignore(just(Token::RParen))
                    .or_not(),
                )
                .map(|((question_opt, field), args_opt)| {
                    if question_opt.is_some() {
                        // Optional chaining
                        if let Some(args) = args_opt {
                            PostfixOp::Method(field, args) // But with optional
                        } else {
                            PostfixOp::Question // Placeholder, handle in fold
                        }
                    } else if let Some(args) = args_opt {
                        PostfixOp::Method(field, args)
                    } else {
                        PostfixOp::Field(field)
                    }
                }),
                just(Token::LBracket)
                .ignore_then(expr.clone())
                .then_ignore(just(Token::RBracket))
                .map(|i| PostfixOp::Index(Box::new(i))),
            ));

            let postfix = unary.then(postfix_op.repeated()).foldl(|left, op| match op {
                PostfixOp::Field(f) => HSharpExpr::Field(Box::new(left), f),
                                                                  PostfixOp::Method(m, args) => HSharpExpr::MethodCall(Box::new(left), m, args),
                                                                  PostfixOp::Index(i) => HSharpExpr::Index(Box::new(left), i),
                                                                  PostfixOp::Question => HSharpExpr::OptionalChain(Box::new(left)),
            });

            // Cast: as T
            let cast = postfix
            .then(just(Token::As).ignore_then(ty.clone()).or_not())
            .map(|(e, opt_ty)| {
                if let Some(ty) = opt_ty {
                    HSharpExpr::Cast(ty, Box::new(e))
                } else {
                    e
                }
            });

            // Product: * / %
            let product_op = choice((
                just(Token::Star).to(HSharpOp::Mul),
                                     just(Token::Slash).to(HSharpOp::Div),
                                     just(Token::Percent).to(HSharpOp::Mod),
            ));

            let product = cast
            .then(product_op.then(cast).repeated())
            .foldl(|lhs, (op, rhs)| HSharpExpr::BinOp(op, Box::new(lhs), Box::new(rhs)));

            // Sum: + -
            let sum_op = choice((
                just(Token::Plus).to(HSharpOp::Add),
                                 just(Token::Minus).to(HSharpOp::Sub),
            ));

            let sum = product
            .then(sum_op.then(product).repeated())
            .foldl(|lhs, (op, rhs)| HSharpExpr::BinOp(op, Box::new(lhs), Box::new(rhs)));

            // Shift: << >>
            let shift_op = choice((
                just(Token::Shl).to(HSharpOp::Shl),
                                   just(Token::Shr).to(HSharpOp::Shr),
            ));

            let shift = sum
            .then(shift_op.then(sum).repeated())
            .foldl(|lhs, (op, rhs)| HSharpExpr::BinOp(op, Box::new(lhs), Box::new(rhs)));

            // BitAnd: &
            let bitand = shift
            .then(just(Token::Amp).then(shift).repeated())
            .foldl(|lhs, (_, rhs)| {
                HSharpExpr::BinOp(HSharpOp::BitAnd, Box::new(lhs), Box::new(rhs))
            });

            // BitXor: ^
            let bitxor = bitand
            .then(just(Token::BitXor).then(bitand).repeated())
            .foldl(|lhs, (_, rhs)| {
                HSharpExpr::BinOp(HSharpOp::BitXor, Box::new(lhs), Box::new(rhs))
            });

            // BitOr: |
            let bitor = bitxor
            .then(just(Token::BitOr).then(bitxor).repeated())
            .foldl(|lhs, (_, rhs)| {
                HSharpExpr::BinOp(HSharpOp::BitOr, Box::new(lhs), Box::new(rhs))
            });

            // Compare: == != < > <= >=
            let cmp_op = choice((
                just(Token::EqEq).to(HSharpOp::Eq),
                                 just(Token::Ne).to(HSharpOp::Ne),
                                 just(Token::Le).to(HSharpOp::Le),
                                 just(Token::Ge).to(HSharpOp::Ge),
                                 just(Token::Lt).to(HSharpOp::Lt),
                                 just(Token::Gt).to(HSharpOp::Gt),
            ));

            let compare = bitor
            .then(cmp_op.then(bitor).repeated())
            .foldl(|lhs, (op, rhs)| HSharpExpr::BinOp(op, Box::new(lhs), Box::new(rhs)));

            // Logic: && ||
            let logic_op = choice((
                just(Token::AndAnd).to(HSharpOp::And),
                                   just(Token::OrOr).to(HSharpOp::Or),
            ));

            let logic = compare
            .then(logic_op.then(compare).repeated())
            .foldl(|lhs, (op, rhs)| HSharpExpr::BinOp(op, Box::new(lhs), Box::new(rhs)));

            // Assignment and compound
            let compound_op = choice((
                just(Token::PlusEq).to(HSharpOp::Add),
                                      just(Token::MinusEq).to(HSharpOp::Sub),
                                      just(Token::MulEq).to(HSharpOp::Mul),
                                      just(Token::DivEq).to(HSharpOp::Div),
                                      just(Token::ModEq).to(HSharpOp::Mod),
                                      just(Token::AndEq).to(HSharpOp::BitAnd),
                                      just(Token::OrEq).to(HSharpOp::BitOr),
                                      just(Token::XorEq).to(HSharpOp::BitXor),
                                      just(Token::ShlEq).to(HSharpOp::Shl),
                                      just(Token::ShrEq).to(HSharpOp::Shr),
            ));

            let assign = logic
            .clone()
            .then(choice((
                just(Token::Eq)
                .ignore_then(expr.clone())
                .map(|r| (None::<HSharpOp>, Some(r))),
                          compound_op
                          .then(expr.clone())
                          .map(|(op, r)| (Some(op), Some(r))),
                          empty().to((None::<HSharpOp>, None::<HSharpExpr>)),
            )))
            .map(
                |(lhs, (comp_op, rhs_opt)): (
                    HSharpExpr,
                    (Option<HSharpOp>, Option<HSharpExpr>),
                )| {
                    if let Some(r) = rhs_opt {
                        if let Some(op) = comp_op {
                            // Desugar compound: x += y -> x = x + y
                            HSharpExpr::Assign(
                                Box::new(lhs.clone()),
                                               Box::new(HSharpExpr::BinOp(
                                                   op,
                                                   Box::new(lhs),
                                                                          Box::new(r),
                                               )),
                            )
                        } else {
                            HSharpExpr::Assign(Box::new(lhs), Box::new(r))
                        }
                    } else {
                        lhs
                    }
                },
            );

            // Question mark: expr?
            assign
            .then(just(Token::Question).or_not())
            .map(|(e, q): (HSharpExpr, Option<Token>)| {
                if q.is_some() {
                    HSharpExpr::Try(Box::new(e))
                } else {
                    e
                }
            })
        });

        let ident_parser = select! { Token::Ident(s) => s };

        let param = choice((
            ident_parser
            .clone()
            .then(just(Token::Colon).ignore_then(ty.clone()))
            .map(|(name, ty)| (name, ty)),
                            just(Token::Ellipsis).to(("...".to_string(), HType::Unit)),
        ));

        let field_def = ident_parser
        .clone()
        .then_ignore(just(Token::Colon))
        .then(ty.clone());

        let let_stmt = just(Token::Let)
        .ignore_then(ident_parser.clone())
        .then(just(Token::Colon).ignore_then(ty.clone()).or_not())
        .then_ignore(just(Token::Eq))
        .then(expr.clone())
        .then_ignore(just(Token::Semi))
        .map(|((name, ty), e)| HSharpStmt::Let(name, ty, e));

        let expr_stmt = expr
        .clone()
        .then(just(Token::Semi).or_not())
        .map(|(e, _)| HSharpStmt::Expr(e));

        let fn_stmt = just(Token::Async)
        .or_not()
        .then_ignore(just(Token::Fn))
        .then(ident_parser.clone())
        .then(
            just(Token::LParen)
            .ignore_then(param.separated_by(just(Token::Comma)).allow_trailing())
            .then_ignore(just(Token::RParen)),
        )
        .then(just(Token::Arrow).ignore_then(ty.clone()).or_not())
        .then(expr.clone().map(Box::new).or_not())
        .map(|((((async_opt, name), params), ret), body)| {
            let is_async = async_opt.is_some();
            HSharpStmt::FunctionDef(
                name,
                params,
                ret.unwrap_or(HType::Unit),
                                    body,
                                    is_async,
            )
        });

        let struct_def = just(Token::Struct)
        .ignore_then(ident_parser.clone())
        .then(
            just(Token::Lt)
            .ignore_then(
                ident_parser
                .clone()
                .separated_by(just(Token::Comma))
                .allow_trailing(),
            )
            .then_ignore(just(Token::Gt))
            .or_not(),
        )
        .then(
            just(Token::LBrace)
            .ignore_then(field_def.clone().separated_by(just(Token::Comma)).allow_trailing())
            .then_ignore(just(Token::RBrace)),
        )
        .map(|((name, generics), fields)| {
            HSharpStmt::StructDef(name, generics.unwrap_or_default(), fields)
        });

        let union_def = just(Token::Union)
        .ignore_then(ident_parser.clone())
        .then(
            just(Token::LBrace)
            .ignore_then(field_def.separated_by(just(Token::Comma)).allow_trailing())
            .then_ignore(just(Token::RBrace)),
        )
        .map(|(name, fields)| HSharpStmt::UnionDef(name, fields));

        // Enum def: enum E { A, B(i32), C { x: i32 } }
        let enum_variant = ident_parser.clone().then(choice((
            just(Token::LParen)
            .ignore_then(ty.clone().separated_by(just(Token::Comma)).allow_trailing())
            .then_ignore(just(Token::RParen))
            .map(EnumVariant::Tuple),
                                                             just(Token::LBrace)
                                                             .ignore_then(field_def.separated_by(just(Token::Comma)).allow_trailing())
                                                             .then_ignore(just(Token::RBrace))
                                                             .map(EnumVariant::Struct),
                                                             empty().to(EnumVariant::Unit),
        )));

        let enum_def = just(Token::Enum)
        .ignore_then(ident_parser.clone())
        .then(
            just(Token::LBrace)
            .ignore_then(enum_variant.separated_by(just(Token::Comma)).allow_trailing())
            .then_ignore(just(Token::RBrace)),
        )
        .map(|(name, variants)| HSharpStmt::EnumDef(name, variants));

        let impl_block = just(Token::Impl)
        .ignore_then(ident_parser.clone())
        .then(
            just(Token::LBrace)
            .ignore_then(fn_stmt.clone().repeated())
            .then_ignore(just(Token::RBrace)),
        )
        .map(|(name, stmts)| HSharpStmt::Impl(name, stmts));

        // Nested import: from [net::tcp] require [connect];
        let module_path = just(Token::LBracket)
        .ignore_then(ident_parser.clone().separated_by(just(Token::ColonColon)))
        .then_ignore(just(Token::RBracket));

        let require_item = ident_parser
        .clone()
        .then(just(Token::Colon).ignore_then(ident_parser.clone()).or_not())
        .map(|(m, opt_s)| {
            if let Some(s) = opt_s {
                RequireItem::Specific(m, s)
            } else {
                RequireItem::WholeModule(m)
            }
        });

        let import_stmt = just(Token::From)
        .ignore_then(module_path)
        .then(
            just(Token::Require).ignore_then(
                just(Token::LBracket)
                .ignore_then(require_item.separated_by(just(Token::Comma)).allow_trailing())
                .then_ignore(just(Token::RBracket)),
            ),
        )
        .then_ignore(just(Token::Semi))
        .map(|(from, requires)| HSharpStmt::Import(from.join("::"), requires));

        // Type alias: type Alias = Type;
        let type_alias = just(Token::Type)
        .ignore_then(ident_parser.clone())
        .then_ignore(just(Token::Eq))
        .then(ty.clone())
        .then_ignore(just(Token::Semi))
        .map(|(name, ty)| HSharpStmt::TypeAlias(name, ty));

        // Const: const NAME: Type = expr;
        let const_def = just(Token::Const)
        .ignore_then(ident_parser.clone())
        .then(just(Token::Colon).ignore_then(ty.clone()))
        .then_ignore(just(Token::Eq))
        .then(expr.clone())
        .then_ignore(just(Token::Semi))
        .map(|((name, ty), e)| HSharpStmt::ConstDef(name, ty, e));

        choice((
            let_stmt,
            fn_stmt,
            import_stmt,
            struct_def,
            union_def,
            enum_def,
            impl_block,
            type_alias,
            const_def,
            expr_stmt,
        ))
    })
    .repeated()
    .map(|stmts| HSharpProgram { stmts })
    .then_ignore(end())
}
