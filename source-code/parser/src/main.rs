use anyhow::{Context, Result};
use chumsky::prelude::*;
use chumsky::text::{ident, keyword, Char};
use chumsky::{Parser, Stream};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;

// Reuse the same AST as in the compiler for consistency.
#[derive(Debug, Deserialize, Serialize, Clone)]
enum HSharpExpr {
    Literal(i32),
    Var(String),
    Alloc(Box<HSharpExpr>),
    Dealloc(Box<HSharpExpr>),
    Deref(Box<HSharpExpr>),
    Assign(Box<HSharpExpr>, Box<HSharpExpr>),
    Print(Box<HSharpExpr>),
    Block(Vec<HSharpStmt>),
    Unsafe(Box<HSharpExpr>),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
enum HSharpStmt {
    Let(String, HSharpExpr),
    Expr(HSharpExpr),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
struct HSharpProgram {
    stmts: Vec<HSharpStmt>,
}

// Token enum for lexer.
#[derive(Clone, Debug, PartialEq)]
enum Token {
    Num(i32),
    Ident(String),
    Let,
    Unsafe,
    Alloc,
    Dealloc,
    Print,
    Star, // *
    Eq,   // =
    LParen,
    RParen,
    LBrace,
    RBrace,
    Semi,
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: h-sharp-parser <input_source> <output_json>");
        std::process::exit(1);
    }
    let input_source = &args[1];
    let output_json = &args[2];

    // Read source code.
    let src = fs::read_to_string(input_source).context("Failed to read source file")?;

    // Lex.
    let tokens = lexer().parse(src.as_str()).map_err(|errs| {
        for err in errs {
            eprintln!("Lexer error: {:?}", err);
        }
        anyhow::anyhow!("Lexer failed")
    })?;

    // Parse.
    let len = src.chars().count();
    let (program, parse_errs) = parser().parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));

    if !parse_errs.is_empty() {
        for err in parse_errs {
            eprintln!("Parse error: {:?}", err);
        }
        return Err(anyhow::anyhow!("Parser failed"));
    }

    let program = program.context("No program parsed")?;

    // Serialize to JSON.
    let json = serde_json::to_string(&program).context("Failed to serialize to JSON")?;
    fs::write(output_json, json).context("Failed to write output JSON")?;

    Ok(())
}

// Lexer using Chumsky.
fn lexer() -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> {
    let num = text::int(10)
        .map(|s: String| Token::Num(s.parse().unwrap()))
        .padded();

    let ident = ident().map(Token::Ident).padded();

    let kw = choice((
        keyword("let").to(Token::Let),
        keyword("unsafe").to(Token::Unsafe),
        keyword("alloc").to(Token::Alloc),
        keyword("dealloc").to(Token::Dealloc),
        keyword("print").to(Token::Print),
    ))
    .padded();

    let op = choice((
        just('*').to(Token::Star),
        just('=').to(Token::Eq),
        just('(').to(Token::LParen),
        just(')').to(Token::RParen),
        just('{').to(Token::LBrace),
        just('}').to(Token::RBrace),
        just(';').to(Token::Semi),
    ))
    .padded();

    let token = num.or(kw).or(ident).or(op);

    token
        .map_with_span(|tok, span| (tok, span))
        .repeated()
        .then_ignore(end())
}

// Parser using Chumsky.
type Span = std::ops::Range<usize>;

fn parser() -> impl Parser<(Token, Span), HSharpProgram, Error = Simple<(Token, Span)>> {
    let ident = select! { Token::Ident(s) => s };

    let expr: Recursive<(Token, Span), HSharpExpr, _> = recursive(|expr| {
        let literal = select! { Token::Num(n) => HSharpExpr::Literal(n) };

        let var = ident.map(HSharpExpr::Var);

        let alloc = keyword(Token::Alloc)
            .ignore_then(just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)))
            .map(|e| HSharpExpr::Alloc(Box::new(e)));

        let dealloc = keyword(Token::Dealloc)
            .ignore_then(just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)))
            .map(|e| HSharpExpr::Dealloc(Box::new(e)));

        let deref = just(Token::Star).ignore_then(expr.clone()).map(|e| HSharpExpr::Deref(Box::new(e)));

        let assign = deref.clone()
            .then_ignore(just(Token::Eq))
            .then(expr.clone())
            .map(|(lhs, rhs)| HSharpExpr::Assign(Box::new(lhs), Box::new(rhs)));

        let print = keyword(Token::Print)
            .ignore_then(just(Token::LParen).ignore_then(expr.clone()).then_ignore(just(Token::RParen)))
            .map(|e| HSharpExpr::Print(Box::new(e)));

        let block = just(Token::LBrace)
            .ignore_then(stmt(expr.clone()).repeated())
            .then_ignore(just(Token::RBrace))
            .map(HSharpExpr::Block);

        let unsafe_expr = keyword(Token::Unsafe)
            .ignore_then(block.clone())
            .map(|b| HSharpExpr::Unsafe(Box::new(b)));

        choice((
            literal,
            var,
            alloc,
            dealloc,
            print,
            assign,
            unsafe_expr,
            block,
        ))
        .labelled("expression")
    });

    let stmt = |expr: Recursive<(Token, Span), HSharpExpr, _>| {
        let let_stmt = keyword(Token::Let)
            .ignore_then(ident)
            .then_ignore(just(Token::Eq))
            .then(expr.clone())
            .then_ignore(just(Token::Semi))
            .map(|(name, e)| HSharpStmt::Let(name, e));

        let expr_stmt = expr.then_ignore(just(Token::Semi)).map(HSharpStmt::Expr);

        choice((let_stmt, expr_stmt)).labelled("statement")
    };

    stmt(expr).repeated().map(|stmts| HSharpProgram { stmts }).then_ignore(end())
}

fn keyword(k: Token) -> impl Parser<(Token, Span), (), Error = Simple<(Token, Span)>> + Clone {
    select! { Token::Let => () if k == Token::Let }
        .or(select! { Token::Unsafe => () if k == Token::Unsafe })
        .or(select! { Token::Alloc => () if k == Token::Alloc })
        .or(select! { Token::Dealloc => () if k == Token::Dealloc })
        .or(select! { Token::Print => () if k == Token::Print })
}

fn just(t: Token) -> impl Parser<(Token, Span), (), Error = Simple<(Token, Span)>> + Clone {
    select! { tok @ _ if tok == (t, _) => () }
}

// For error reporting, you can use ariadne, but omitted for brevity.
// In a real parser, add error handling with ariadne for pretty printing.
