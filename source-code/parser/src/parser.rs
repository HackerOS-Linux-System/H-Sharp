use crate::ast::*;
use crate::lexer::Token;
use chumsky::prelude::*;

type TParser<'a, T> = BoxedParser<'a, Token, T, Simple<Token>>;

fn ty_parser<'a>() -> TParser<'a, HType> {
    recursive(|ty| {
        let primitive = select! {
            Token::I8Type => HType::I8,
            Token::I32Type => HType::I32,
            Token::I64Type => HType::I64,
            Token::U8Type => HType::U8,
            Token::U16Type => HType::U16,
            Token::U32Type => HType::U32,
            Token::U64Type => HType::U64,
            Token::BoolType => HType::Bool,
            Token::F32Type => HType::F32,
            Token::F64Type => HType::F64,
            Token::UnitType => HType::Unit,
        };

        let ptr = just(Token::Star)
        .ignore_then(ty.clone())
        .map(|t| HType::Pointer(Box::new(t)));

        let generic_struct = select! { Token::Ident(s) => s }
        .then(
            just(Token::Lt)
            .ignore_then(ty.clone().separated_by(just(Token::Comma)))
            .then_ignore(just(Token::Gt))
            .or_not(),
        )
        .map(|(name, generics)| HType::Struct(name, generics.unwrap_or_default()));

        let array_or_slice = just(Token::LBracket)
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
        });

        let tuple = just(Token::LParen)
        .ignore_then(ty.clone().separated_by(just(Token::Comma)).allow_trailing())
        .then_ignore(just(Token::RParen))
        .map(HType::Tuple);

        let grouped = just(Token::LParen)
        .ignore_then(ty.clone())
        .then_ignore(just(Token::RParen));

        primitive
        .or(ptr)
        .or(generic_struct)
        .or(array_or_slice)
        .or(tuple)
        .or(grouped)
    })
    .boxed()
}

fn literal_parser<'a>() -> TParser<'a, HSharpExpr> {
    select! {
        Token::Num(n) => HSharpExpr::Literal(HSharpLiteral::Int(n.try_into().unwrap())),
        Token::Float(f) => HSharpExpr::Literal(HSharpLiteral::Float(f)),
        Token::True => HSharpExpr::Literal(HSharpLiteral::Bool(true)),
        Token::False => HSharpExpr::Literal(HSharpLiteral::Bool(false)),
        Token::Str(s) => HSharpExpr::Literal(HSharpLiteral::String(s)),
        Token::RawString(s) => HSharpExpr::Literal(HSharpLiteral::RawString(s)),
        Token::ByteChar(b) => HSharpExpr::Literal(HSharpLiteral::Byte(b)),
    }
    .boxed()
}

pub fn parser() -> impl Parser<Token, HSharpProgram, Error = Simple<Token>> {
    recursive(|stmt| {
        let expr = recursive(|expr| {
            let ty = ty_parser();
            let ident = select! { Token::Ident(s) => s };

            let block = just(Token::LBrace)
            .ignore_then(stmt.clone().repeated())
            .then_ignore(just(Token::RBrace))
            .map(HSharpExpr::Block)
            .boxed();

            let lit = literal_parser();

            let if_expr = just(Token::If)
            .ignore_then(expr.clone())
            .then(block.clone())
            .then(just(Token::Else).ignore_then(block.clone()).or_not())
            .map(|((cond, then), else_)| {
                HSharpExpr::If(Box::new(cond), Box::new(then), else_.map(Box::new))
            })
            .boxed();

            let while_expr = just(Token::While)
            .ignore_then(expr.clone())
            .then(block.clone())
            .map(|(cond, body)| HSharpExpr::While(Box::new(cond), Box::new(body)))
            .boxed();

            let for_expr = just(Token::For)
            .ignore_then(ident.clone())
            .then_ignore(just(Token::Eq))
            .then(expr.clone())
            .then_ignore(just(Token::Lt))
            .then(expr.clone())
            .then(block.clone())
            .map(|(((var, start), end), body)| {
                HSharpExpr::For(var, Box::new(start), Box::new(end), Box::new(body))
            })
            .boxed();

            let return_expr = just(Token::Return)
            .ignore_then(expr.clone())
            .map(|e| HSharpExpr::Return(Box::new(e)))
            .boxed();

            let match_case = expr
            .clone()
            .then_ignore(just(Token::DoubleArrow))
            .then(expr.clone().or(block.clone()));

            let match_expr = just(Token::Match)
            .ignore_then(expr.clone())
            .then(
                just(Token::LBrace)
                .ignore_then(
                    match_case
                    .separated_by(just(Token::Comma))
                    .allow_trailing(),
                )
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
            })
            .boxed();

            let alloc = just(Token::Alloc)
            .ignore_then(
                just(Token::LParen)
                .ignore_then(expr.clone())
                .then_ignore(just(Token::RParen)),
            )
            .map(|e| HSharpExpr::Alloc(Box::new(e)))
            .boxed();

            let dealloc = just(Token::Dealloc)
            .ignore_then(
                just(Token::LParen)
                .ignore_then(expr.clone())
                .then_ignore(just(Token::RParen)),
            )
            .map(|e| HSharpExpr::Dealloc(Box::new(e)))
            .boxed();

            let write = just(Token::Write)
            .ignore_then(
                just(Token::LParen)
                .ignore_then(expr.clone())
                .then_ignore(just(Token::RParen)),
            )
            .map(|e| HSharpExpr::Write(Box::new(e)))
            .boxed();

            let cast_expr = just(Token::Cast)
            .ignore_then(just(Token::LParen))
            .ignore_then(ty.clone())
            .then_ignore(just(Token::Comma))
            .then(expr.clone())
            .then_ignore(just(Token::RParen))
            .map(|(t, e)| HSharpExpr::Cast(t, Box::new(e)))
            .boxed();

            let sizeof_expr = just(Token::SizeOf)
            .ignore_then(
                just(Token::LParen)
                .ignore_then(ty.clone())
                .then_ignore(just(Token::RParen)),
            )
            .map(HSharpExpr::SizeOf)
            .boxed();

            let direct = just(Token::Direct)
            .ignore_then(block.clone())
            .map(|b| HSharpExpr::Direct(Box::new(b)))
            .boxed();

            let await_expr = just(Token::Await)
            .ignore_then(expr.clone())
            .map(|e| HSharpExpr::Await(Box::new(e)))
            .boxed();

            let array_lit = just(Token::LBracket)
            .ignore_then(
                expr.clone()
                .separated_by(just(Token::Comma))
                .allow_trailing(),
            )
            .then_ignore(just(Token::RBracket))
            .map(HSharpExpr::ArrayLit)
            .boxed();

            let tuple_or_group = just(Token::LParen)
            .ignore_then(
                expr.clone()
                .separated_by(just(Token::Comma))
                .allow_trailing(),
            )
            .then_ignore(just(Token::RParen))
            .map(|mut v: Vec<HSharpExpr>| {
                if v.len() == 1 {
                    v.remove(0)
                } else {
                    HSharpExpr::Tuple(v)
                }
            })
            .boxed();

            let closure = just(Token::BitOr)
            .ignore_then(ident.clone().separated_by(just(Token::Comma)))
            .then_ignore(just(Token::BitOr))
            .then(expr.clone())
            .map(|(params, body)| HSharpExpr::Closure(params, Box::new(body)))
            .boxed();

            // Ident with optional call/struct/union suffix
            let ident_expr = ident
            .clone()
            .then(
                just(Token::Dot)
                .ignore_then(select! { Token::Ident(s) => s })
                .then(
                    just(Token::LParen)
                    .ignore_then(
                        expr.clone()
                        .separated_by(just(Token::Comma))
                        .allow_trailing(),
                    )
                    .then_ignore(just(Token::RParen)),
                )
                .map(|(f, args)| (0u8, Some(f), args))
                .or(
                    just(Token::LBrace)
                    .ignore_then(
                        expr.clone()
                        .separated_by(just(Token::Comma))
                        .allow_trailing(),
                    )
                    .then_ignore(just(Token::RBrace))
                    .map(|fields| (1u8, None, fields)),
                )
                .or(
                    just(Token::LParen)
                    .ignore_then(
                        expr.clone()
                        .separated_by(just(Token::Comma))
                        .allow_trailing(),
                    )
                    .then_ignore(just(Token::RParen))
                    .map(|args| (2u8, None, args)),
                )
                .or(empty().map(|_| (3u8, None, vec![])))
                .or_not(),
            )
            .map(|(name, suffix)| match suffix {
                Some((0, Some(field), args)) => {
                    HSharpExpr::MethodCall(Box::new(HSharpExpr::Var(name)), field, args)
                }
                Some((1, None, fields)) => HSharpExpr::StructLit(name, fields),
                 Some((2, None, args)) => HSharpExpr::Call(name, args),
                 _ => HSharpExpr::Var(name),
            })
            .boxed();

            let atom = lit
            .or(just(Token::Break).to(HSharpExpr::Break))
            .or(just(Token::Continue).to(HSharpExpr::Continue))
            .or(if_expr)
            .or(while_expr)
            .or(for_expr)
            .or(return_expr)
            .or(match_expr)
            .or(alloc)
            .or(dealloc)
            .or(write)
            .or(cast_expr)
            .or(sizeof_expr)
            .or(direct)
            .or(await_expr)
            .or(closure)
            .or(array_lit)
            .or(tuple_or_group)
            .or(block)
            .or(ident_expr)
            .boxed();

            // Unary
            let unary_op = select! {
                Token::Minus => UnaryOp::Neg,
                Token::BitNot => UnaryOp::BitNot,
                Token::Star => UnaryOp::Deref,
                Token::Amp => UnaryOp::AddrOf,
            };

            let unary = unary_op
            .repeated()
            .then(atom)
            .map(|(ops, rhs)| {
                ops.into_iter()
                .rev()
                .fold(rhs, |acc, op| HSharpExpr::Unary(op, Box::new(acc)))
            })
            .boxed();

            // Postfix
            let postfix = unary
            .then(
                just(Token::Dot)
                .ignore_then(just(Token::Question).or_not())
                .then(select! { Token::Ident(s) => s })
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
                .map(|((q, field), args_opt)| {
                    if q.is_some() {
                        if let Some(args) = args_opt {
                            (2u8, field, args, None)
                        } else {
                            (3u8, field, vec![], None)
                        }
                    } else if let Some(args) = args_opt {
                        (1u8, field, args, None)
                    } else {
                        (0u8, field, vec![], None)
                    }
                })
                .or(
                    just(Token::LBracket)
                    .ignore_then(expr.clone())
                    .then_ignore(just(Token::RBracket))
                    .map(|idx| (4u8, String::new(), vec![], Some(idx))),
                )
                .repeated(),
            )
            .foldl(|left, (kind, field, args, idx)| match kind {
                0 => HSharpExpr::Field(Box::new(left), field),
                   1 | 2 => HSharpExpr::MethodCall(Box::new(left), field, args),
                   3 => HSharpExpr::OptionalChain(Box::new(left)),
                   4 => HSharpExpr::Index(Box::new(left), Box::new(idx.unwrap())),
                   _ => left,
            })
            .boxed();

            // as cast
            let cast = postfix
            .then(just(Token::As).ignore_then(ty.clone()).or_not())
            .map(|(e, opt_ty)| {
                if let Some(t) = opt_ty {
                    HSharpExpr::Cast(t, Box::new(e))
                } else {
                    e
                }
            })
            .boxed();

            // Precedence chain — each level boxed to break type inference cycles
            // We must clone the parser when using it in `.then` to avoid "borrow of moved value" errors.

            let product = cast.clone()
            .then(
                select! {
                    Token::Star => HSharpOp::Mul,
                    Token::Slash => HSharpOp::Div,
                    Token::Percent => HSharpOp::Mod,
                }
                .then(cast.clone())
                .repeated(),
            )
            .foldl(|l, (op, r)| HSharpExpr::BinOp(op, Box::new(l), Box::new(r)))
            .boxed();

            let sum = product.clone()
            .then(
                select! {
                    Token::Plus => HSharpOp::Add,
                    Token::Minus => HSharpOp::Sub,
                }
                .then(product.clone())
                .repeated(),
            )
            .foldl(|l, (op, r)| HSharpExpr::BinOp(op, Box::new(l), Box::new(r)))
            .boxed();

            let shift = sum.clone()
            .then(
                select! {
                    Token::Shl => HSharpOp::Shl,
                    Token::Shr => HSharpOp::Shr,
                }
                .then(sum.clone())
                .repeated(),
            )
            .foldl(|l, (op, r)| HSharpExpr::BinOp(op, Box::new(l), Box::new(r)))
            .boxed();

            let bitand = shift.clone()
            .then(
                just(Token::Amp)
                .to(HSharpOp::BitAnd)
                .then(shift.clone())
                .repeated(),
            )
            .foldl(|l, (op, r)| HSharpExpr::BinOp(op, Box::new(l), Box::new(r)))
            .boxed();

            let bitxor = bitand.clone()
            .then(
                just(Token::BitXor)
                .to(HSharpOp::BitXor)
                .then(bitand.clone())
                .repeated(),
            )
            .foldl(|l, (op, r)| HSharpExpr::BinOp(op, Box::new(l), Box::new(r)))
            .boxed();

            let bitor = bitxor.clone()
            .then(
                just(Token::BitOr)
                .to(HSharpOp::BitOr)
                .then(bitxor.clone())
                .repeated(),
            )
            .foldl(|l, (op, r)| HSharpExpr::BinOp(op, Box::new(l), Box::new(r)))
            .boxed();

            let compare = bitor.clone()
            .then(
                select! {
                    Token::EqEq => HSharpOp::Eq,
                    Token::Ne => HSharpOp::Ne,
                    Token::Le => HSharpOp::Le,
                    Token::Ge => HSharpOp::Ge,
                    Token::Lt => HSharpOp::Lt,
                    Token::Gt => HSharpOp::Gt,
                }
                .then(bitor.clone())
                .repeated(),
            )
            .foldl(|l, (op, r)| HSharpExpr::BinOp(op, Box::new(l), Box::new(r)))
            .boxed();

            let logic = compare.clone()
            .then(
                select! {
                    Token::AndAnd => HSharpOp::And,
                    Token::OrOr => HSharpOp::Or,
                }
                .then(compare.clone())
                .repeated(),
            )
            .foldl(|l, (op, r)| HSharpExpr::BinOp(op, Box::new(l), Box::new(r)))
            .boxed();

            let range = logic.clone()
            .then(
                choice((
                    just(Token::DotDotEq).to(true),
                        just(Token::DotDot).to(false),
                ))
                .then(logic.clone())
                .or_not(),
            )
            .map(|(lhs, opt)| {
                if let Some((inclusive, rhs)) = opt {
                    HSharpExpr::Range(Box::new(lhs), Box::new(rhs), inclusive)
                } else {
                    lhs
                }
            })
            .boxed();

            let compound_op = select! {
                Token::PlusEq => HSharpOp::Add,
                Token::MinusEq => HSharpOp::Sub,
                Token::MulEq => HSharpOp::Mul,
                Token::DivEq => HSharpOp::Div,
                Token::ModEq => HSharpOp::Mod,
                Token::AndEq => HSharpOp::BitAnd,
                Token::OrEq => HSharpOp::BitOr,
                Token::XorEq => HSharpOp::BitXor,
                Token::ShlEq => HSharpOp::Shl,
                Token::ShrEq => HSharpOp::Shr,
            };

            let assign = range
            .then(
                just(Token::Eq)
                .ignore_then(expr.clone())
                .map(|r| (None::<HSharpOp>, r))
                .or(compound_op
                .then(expr.clone())
                .map(|(op, r)| (Some(op), r)))
                .or_not(),
            )
            .map(|(lhs, opt)| match opt {
                Some((None, rhs)) => HSharpExpr::Assign(Box::new(lhs), Box::new(rhs)),
                 Some((Some(op), rhs)) => HSharpExpr::Assign(
                     Box::new(lhs.clone()),
                                                             Box::new(HSharpExpr::BinOp(op, Box::new(lhs), Box::new(rhs))),
                 ),
                 None => lhs,
            })
            .boxed();

            assign
            .then(just(Token::Question).or_not())
            .map(|(e, q): (HSharpExpr, Option<Token>)| {
                if q.is_some() {
                    HSharpExpr::Try(Box::new(e))
                } else {
                    e
                }
            })
            .boxed()
        });

        let ident = select! { Token::Ident(s) => s };
        let ty = ty_parser();

        let param = ident
        .clone()
        .then(just(Token::Colon).ignore_then(ty.clone()))
        .map(|(name, t)| (name, t))
        .or(just(Token::Ellipsis).to(("...".to_string(), HType::Unit)));

        let field_def = ident
        .clone()
        .then_ignore(just(Token::Colon))
        .then(ty.clone());

        let let_stmt = just(Token::Let)
        .ignore_then(ident.clone())
        .then(just(Token::Colon).ignore_then(ty.clone()).or_not())
        .then_ignore(just(Token::Eq))
        .then(expr.clone())
        .then_ignore(just(Token::Semi))
        .map(|((name, t), e)| HSharpStmt::Let(name, t, e));

        let fn_stmt = just(Token::Async)
        .or_not()
        .then_ignore(just(Token::Fn))
        .then(ident.clone())
        .then(
            just(Token::LParen)
            .ignore_then(param.separated_by(just(Token::Comma)).allow_trailing())
            .then_ignore(just(Token::RParen)),
        )
        .then(just(Token::Arrow).ignore_then(ty.clone()).or_not())
        .then(expr.clone().map(Box::new).or_not())
        .map(|((((async_opt, name), params), ret), body)| {
            HSharpStmt::FunctionDef(
                name,
                params,
                ret.unwrap_or(HType::Unit),
                                    body,
                                    async_opt.is_some(),
            )
        });

        let struct_def = just(Token::Struct)
        .ignore_then(ident.clone())
        .then(
            just(Token::Lt)
            .ignore_then(
                ident
                .clone()
                .separated_by(just(Token::Comma))
                .allow_trailing(),
            )
            .then_ignore(just(Token::Gt))
            .or_not(),
        )
        .then(
            just(Token::LBrace)
            .ignore_then(
                field_def
                .clone()
                .separated_by(just(Token::Comma))
                .allow_trailing(),
            )
            .then_ignore(just(Token::RBrace)),
        )
        .map(|((name, generics), fields)| {
            HSharpStmt::StructDef(name, generics.unwrap_or_default(), fields)
        });

        let union_def = just(Token::Union)
        .ignore_then(ident.clone())
        .then(
            just(Token::LBrace)
            .ignore_then(
                field_def
                .clone()
                .separated_by(just(Token::Comma))
                .allow_trailing(),
            )
            .then_ignore(just(Token::RBrace)),
        )
        .map(|(name, fields)| HSharpStmt::UnionDef(name, fields));

        let enum_variant = ident.clone().then(
            just(Token::LParen)
            .ignore_then(
                ty.clone()
                .separated_by(just(Token::Comma))
                .allow_trailing(),
            )
            .then_ignore(just(Token::RParen))
            .map(EnumVariant::Tuple)
            .or(
                just(Token::LBrace)
                .ignore_then(
                    field_def
                    .clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing(),
                )
                .then_ignore(just(Token::RBrace))
                .map(EnumVariant::Struct),
            )
            .or(empty().to(EnumVariant::Unit)),
        );

        let enum_def = just(Token::Enum)
        .ignore_then(ident.clone())
        .then(
            just(Token::LBrace)
            .ignore_then(
                enum_variant
                .separated_by(just(Token::Comma))
                .allow_trailing(),
            )
            .then_ignore(just(Token::RBrace)),
        )
        .map(|(name, variants)| HSharpStmt::EnumDef(name, variants));

        let impl_block = just(Token::Impl)
        .ignore_then(ident.clone())
        .then(
            just(Token::LBrace)
            .ignore_then(fn_stmt.clone().repeated())
            .then_ignore(just(Token::RBrace)),
        )
        .map(|(name, stmts)| HSharpStmt::Impl(name, stmts));

        let module_path = just(Token::LBracket)
        .ignore_then(ident.clone().separated_by(just(Token::ColonColon)))
        .then_ignore(just(Token::RBracket));

        let require_item = ident
        .clone()
        .then(just(Token::Colon).ignore_then(ident.clone()).or_not())
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
                .ignore_then(
                    require_item
                    .separated_by(just(Token::Comma))
                    .allow_trailing(),
                )
                .then_ignore(just(Token::RBracket)),
            ),
        )
        .then_ignore(just(Token::Semi))
        .map(|(from, requires)| HSharpStmt::Import(from.join("::"), requires));

        let type_alias = just(Token::Type)
        .ignore_then(ident.clone())
        .then_ignore(just(Token::Eq))
        .then(ty.clone())
        .then_ignore(just(Token::Semi))
        .map(|(name, t)| HSharpStmt::TypeAlias(name, t));

        let const_def = just(Token::Const)
        .ignore_then(ident.clone())
        .then(just(Token::Colon).ignore_then(ty.clone()))
        .then_ignore(just(Token::Eq))
        .then(expr.clone())
        .then_ignore(just(Token::Semi))
        .map(|((name, t), e)| HSharpStmt::ConstDef(name, t, e));

        let expr_stmt = expr.then(just(Token::Semi).or_not()).map(|(e, _)| HSharpStmt::Expr(e));

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
