use anyhow::{Context, Result};
use chumsky::prelude::*;
use chumsky::text::{ident, keyword as text_keyword};
use chumsky::{Parser, Stream};
use chumsky::error::Simple;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::fs;

#[derive(Debug, Deserialize, Serialize, Clone)]
enum HSharpLiteral {
    Int(i32),
    Bool(bool),
    String(String),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
enum HSharpOp {
    Add,
    Eq,
    Lt,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
enum Type {
    I8,
    I32,
    Bool,
    Pointer(Box<Type>),
    Unit,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
enum HSharpExpr {
    Literal(HSharpLiteral),
    Var(String),
    Alloc(Box<HSharpExpr>),
    Dealloc(Box<HSharpExpr>),
    Deref(Box<HSharpExpr>),
    Assign(Box<HSharpExpr>, Box<HSharpExpr>),
    Print(Box<HSharpExpr>),
    Block(Vec<HSharpStmt>),
    Direct(Box<HSharpExpr>),
    BinOp(HSharpOp, Box<HSharpExpr>, Box<HSharpExpr>),
    AddrOf(Box<HSharpExpr>),
    If(Box<HSharpExpr>, Box<HSharpExpr>, Option<Box<HSharpExpr>>),
    While(Box<HSharpExpr>, Box<HSharpExpr>),
    Call(String, Vec<HSharpExpr>),
    Cast(Type, Box<HSharpExpr>),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
enum HSharpStmt {
    Let(String, Option<Type>, HSharpExpr),
    Expr(HSharpExpr),
    FunctionDef(String, Vec<(String, Type)>, Type, Box<HSharpExpr>),
    Import(String, Vec<RequireItem>),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
enum RequireItem {
    WholeModule(String),
    Specific(String, String),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
struct HSharpProgram {
    stmts: Vec<HSharpStmt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Token {
    Num(i32),
    Ident(String),
    Let,
    Direct,
    Alloc,
    Dealloc,
    Print,
    I8Type,
    I32Type,
    BoolType,
    UnitType,
    True,
    False,
    If,
    While,
    Else,
    Star,
    Amp,
    Plus,
    Eq,
    EqEq,
    Lt,
    Colon,
    Semi,
    LParen,
    RParen,
    LBrace,
    RBrace,
    Fn,
    From,
    Require,
    Arrow,
    LBracket,
    RBracket,
    As,
    String(String),
    Comma,
}

type Span = std::ops::Range<usize>;

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: h-sharp-parser <input_source> <output_json>");
        std::process::exit(1);
    }
    let input_source = &args[1];
    let output_json = &args[2];
    let src = fs::read_to_string(input_source).context("Failed to read source file")?;
    let tokens = lexer().parse(src.as_str()).map_err(|errs| {
        for err in errs {
            eprintln!("Lexer error: {:?}", err);
        }
        anyhow::anyhow!("Lexer failed")
    })?;
    let len = src.chars().count();
    let (mut program, parse_errs) = parser().parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));
    if !parse_errs.is_empty() {
        for err in parse_errs {
            eprintln!("Parse error: {:?}", err);
        }
        return Err(anyhow::anyhow!("Parser failed"));
    }
    let mut program = program.context("No program parsed")?;
    let mut visited = HashSet::new();
    resolve_imports(&mut program, &mut visited, input_source)?;
    let json = serde_json::to_string(&program).context("Failed to serialize to JSON")?;
    fs::write(output_json, json).context("Failed to write output JSON")?;
    Ok(())
}

fn resolve_imports(program: &mut HSharpProgram, visited: &mut HashSet<String>, _current_file: &str) -> Result<()> {
    let mut new_stmts = Vec::new();
    for stmt in program.stmts.drain(..) {
        if let HSharpStmt::Import(from, requires) = stmt {
            for require in requires {
                let (mod_name, opt_symbols) = match require {
                    RequireItem::WholeModule(m) => (m, None),
                    RequireItem::Specific(m, s) => (m, Some(vec![s])),
                };
                let file_path = format!("/usr/lib/H-Sharp/libs/{}/{}.h#", from, mod_name);
                if visited.contains(&file_path) {
                    return Err(anyhow::anyhow!("Cycle in imports: {}", file_path));
                }
                visited.insert(file_path.clone());
                let sub_src = fs::read_to_string(&file_path).unwrap_or_else(|_| {
                    eprintln!("Warning: Lib file {} not found", file_path);
                    String::new()
                });
                if sub_src.is_empty() {
                    continue;
                }
                let sub_tokens = lexer().parse(sub_src.as_str()).map_err(|errs| {
                    for err in errs {
                        eprintln!("Sub lexer error: {:?}", err);
                    }
                    anyhow::anyhow!("Sub lexer failed")
                })?;
                let len = sub_src.chars().count();
                let (sub_program_opt, parse_errs) = parser().parse_recovery(Stream::from_iter(len..len + 1, sub_tokens.into_iter()));
                if !parse_errs.is_empty() {
                    for err in parse_errs {
                        eprintln!("Sub parse error: {:?}", err);
                    }
                    return Err(anyhow::anyhow!("Sub parser failed"));
                }
                let mut sub_program = sub_program_opt.context("No sub program parsed")?;
                resolve_imports(&mut sub_program, visited, &file_path)?;
                let added_stmts = if let Some(symbols) = opt_symbols {
                    sub_program.stmts.into_iter().filter(|stmt| {
                        if let HSharpStmt::FunctionDef(n, _, _, _) = stmt {
                            symbols.contains(n)
                        } else {
                            false
                        }
                    }).collect::<Vec<_>>()
                } else {
                    sub_program.stmts
                };
                new_stmts.extend(added_stmts);
            }
        } else {
            new_stmts.push(stmt);
        }
    }
    program.stmts = new_stmts;
    Ok(())
}

fn lexer() -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> {
    let num = text::int(10)
    .map(|s: String| Token::Num(s.parse().unwrap()))
    .padded();

    let ident = ident().map(Token::Ident).padded();

    let kw = choice((
        text_keyword("let").to(Token::Let),
                     text_keyword("direct").to(Token::Direct),
                     text_keyword("alloc").to(Token::Alloc),
                     text_keyword("dealloc").to(Token::Dealloc),
                     text_keyword("print").to(Token::Print),
                     text_keyword("i8").to(Token::I8Type),
                     text_keyword("int").to(Token::I32Type),
                     text_keyword("bool").to(Token::BoolType),
                     text_keyword("unit").to(Token::UnitType),
                     text_keyword("true").to(Token::True),
                     text_keyword("false").to(Token::False),
                     text_keyword("if").to(Token::If),
                     text_keyword("while").to(Token::While),
                     text_keyword("else").to(Token::Else),
                     text_keyword("fn").to(Token::Fn),
                     text_keyword("from").to(Token::From),
                     text_keyword("require").to(Token::Require),
                     text_keyword("as").to(Token::As),
    )).padded();

    let op = choice((
        just('*').to(Token::Star),
                     just('&').to(Token::Amp),
                     just('+').to(Token::Plus),
                     just("==").to(Token::EqEq),
                     just('=').to(Token::Eq),
                     just('<').to(Token::Lt),
                     just(':').to(Token::Colon),
                     just(';').to(Token::Semi),
                     just('(').to(Token::LParen),
                     just(')').to(Token::RParen),
                     just('{').to(Token::LBrace),
                     just('}').to(Token::RBrace),
                     just("->").to(Token::Arrow),
                     just('[').to(Token::LBracket),
                     just(']').to(Token::RBracket),
                     just(',').to(Token::Comma),
    )).padded();

    let string = just('"')
    .ignore_then(filter(|c| *c != '"').repeated())
    .then_ignore(just('"'))
    .map(|chars: Vec<char>| Token::String(chars.into_iter().collect::<String>()))
    .padded();

    let token = num.or(kw).or(ident).or(op).or(string);

    token
    .map_with_span(|tok, span| (tok, span))
    .repeated()
    .then_ignore(end())
}

fn parser() -> impl Parser<Token, HSharpProgram, Error = Simple<Token>> {
    recursive(|stmt: Recursive<'_, Token, HSharpStmt, Simple<Token>>| {
        let expr = recursive(|expr: Recursive<'_, Token, HSharpExpr, Simple<Token>>| {
            let literal = choice((
                select! { Token::Num(n) => HSharpLiteral::Int(n) },
                                  select! { Token::True => HSharpLiteral::Bool(true) },
                                  select! { Token::False => HSharpLiteral::Bool(false) },
                                  select! { Token::String(s) => HSharpLiteral::String(s) },
            )).map(HSharpExpr::Literal);

            let var = select! { Token::Ident(s) => HSharpExpr::Var(s) };

            let alloc = just(Token::Alloc)
            .ignore_then(just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)))
            .map(|e| HSharpExpr::Alloc(Box::new(e)));

            let dealloc = just(Token::Dealloc)
            .ignore_then(just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)))
            .map(|e| HSharpExpr::Dealloc(Box::new(e)));

            let print = just(Token::Print)
            .ignore_then(just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)))
            .map(|e| HSharpExpr::Print(Box::new(e)));

            let block = just(Token::LBrace)
            .ignore_then(stmt.clone().repeated())
            .then_ignore(just(Token::RBrace))
            .map(HSharpExpr::Block);

            let direct_expr = just(Token::Direct)
            .ignore_then(block.clone())
            .map(|b| HSharpExpr::Direct(Box::new(b)));

            let if_expr = just(Token::If)
            .ignore_then(just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)))
            .then(block.clone())
            .then(just(Token::Else).ignore_then(block.clone()).or_not())
            .map(|((cond, then), else_): ((HSharpExpr, HSharpExpr), Option<HSharpExpr>)| HSharpExpr::If(Box::new(cond), Box::new(then), else_.map(Box::new)));

            let while_expr = just(Token::While)
            .ignore_then(just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)))
            .then(block.clone())
            .map(|(cond, body)| HSharpExpr::While(Box::new(cond), Box::new(body)));

            let call = select! { Token::Ident(s) => s }
            .then(just(Token::LParen).ignore_then(expr.clone().separated_by(just(Token::Comma))).then_ignore(just(Token::RParen)))
            .map(|(name, args)| HSharpExpr::Call(name, args));

            let primary = choice((
                literal,
                alloc,
                dealloc,
                print,
                direct_expr,
                if_expr,
                while_expr,
                    var,
                    call,
                    just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)),
                                  block,
            ));

            let unary = choice((
                just(Token::Star).ignore_then(primary.clone()).map(|e| HSharpExpr::Deref(Box::new(e))),
                                just(Token::Amp).ignore_then(primary.clone()).map(|e| HSharpExpr::AddrOf(Box::new(e))),
                                primary,
            ));

            let ty = recursive(|ty| {
                choice((
                    select! { Token::I8Type => Type::I8 },
                    select! { Token::I32Type => Type::I32 },
                    select! { Token::BoolType => Type::Bool },
                    select! { Token::UnitType => Type::Unit },
                    just(Token::Star).ignore_then(ty.clone()).map(|t| Type::Pointer(Box::new(t))),
                        just(Token::LParen).ignore_then(ty).then_ignore(just(Token::RParen)),
                ))
            });

            let cast = unary.clone().then(just(Token::As).ignore_then(ty.clone()).or_not()).map(|(e, opt_ty)| {
                if let Some(ty) = opt_ty {
                    HSharpExpr::Cast(ty, Box::new(e))
                } else {
                    e
                }
            });

            let bin_op = choice((
                just(Token::Plus).to(HSharpOp::Add),
                                 just(Token::EqEq).to(HSharpOp::Eq),
                                 just(Token::Lt).to(HSharpOp::Lt),
            ));

            // Correct way to handle left-associative binary operators in Chumsky
            cast.clone()
            .then(bin_op.then(cast.clone()).repeated())
            .foldl(|lhs, (op, rhs)| HSharpExpr::BinOp(op, Box::new(lhs), Box::new(rhs)))
        });

        let ty = recursive(|ty| {
            choice((
                select! { Token::I8Type => Type::I8 },
                select! { Token::I32Type => Type::I32 },
                select! { Token::BoolType => Type::Bool },
                select! { Token::UnitType => Type::Unit },
                just(Token::Star).ignore_then(ty.clone()).map(|t| Type::Pointer(Box::new(t))),
                    just(Token::LParen).ignore_then(ty).then_ignore(just(Token::RParen)),
            ))
        });

        let ident_parser = select! { Token::Ident(s) => s };

        let param = ident_parser.clone().then(just(Token::Colon).ignore_then(ty.clone())).map(|(name, ty)| (name, ty));

        let let_stmt = just(Token::Let)
        .ignore_then(ident_parser.clone())
        .then(just(Token::Colon).ignore_then(ty.clone()).or_not())
        .then_ignore(just(Token::Eq))
        .then(expr.clone())
        .then_ignore(just(Token::Semi))
        .map(|((name, ty), e)| HSharpStmt::Let(name, ty, e));

        let expr_stmt = expr.clone().then_ignore(just(Token::Semi)).map(HSharpStmt::Expr);

        let fn_stmt = just(Token::Fn)
        .ignore_then(ident_parser.clone())
        .then(just(Token::LParen).ignore_then(param.separated_by(just(Token::Comma))).then_ignore(just(Token::RParen)))
        .then(just(Token::Arrow).ignore_then(ty.clone()).or_not())
        .then(expr.clone())
        .map(|(((name, params), ret), body): (((String, Vec<(String, Type)>), Option<Type>), HSharpExpr)| HSharpStmt::FunctionDef(name, params, ret.unwrap_or(Type::Unit), Box::new(body)));

        let require_item = ident_parser.clone().then(just(Token::Colon).ignore_then(ident_parser.clone()).or_not()).map(|(m, opt_s)| if let Some(s) = opt_s { RequireItem::Specific(m, s) } else { RequireItem::WholeModule(m) });

        let import_stmt = just(Token::From)
        .ignore_then(just(Token::LBracket).ignore_then(ident_parser.clone()).then_ignore(just(Token::RBracket)))
        .then(just(Token::Require).ignore_then(just(Token::LBracket).ignore_then(require_item.separated_by(just(Token::Comma))).then_ignore(just(Token::RBracket))))
        .then_ignore(just(Token::Semi))
        .map(|(from, requires)| HSharpStmt::Import(from, requires));

        choice((let_stmt, expr_stmt, fn_stmt, import_stmt))
    })
    .repeated()
    .map(|stmts| HSharpProgram { stmts })
    .then_ignore(end())
}
