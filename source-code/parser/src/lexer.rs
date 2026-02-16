use chumsky::prelude::*;
use chumsky::text;
use std::hash::{Hash, Hasher};

#[derive(Clone, Debug)]
pub enum Token {
    Num(i32),
    Float(f64),
    Ident(String),
    Let,
    Direct,
    Alloc,
    Dealloc,
    Write,
    Cast, // Added
    SizeOf,
    I8Type,
    I32Type,
    I64Type,
    BoolType,
    UnitType,
    F32Type,
    F64Type,
    True,
    False,
    If,
    While,
    Else,
    Break,
    Continue,
    Match,
    Impl,
    Star,
    Amp,
    Plus,
    Minus,
    Slash,
    Percent,
    Eq,
    EqEq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    AndAnd,
    OrOr,
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
    Struct,
    Union,
    For,
    Return,
    Dot,
    Ellipsis,
    DoubleArrow,
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Token::Num(a), Token::Num(b)) => a == b,
            (Token::Float(a), Token::Float(b)) => a.to_bits() == b.to_bits(),
            (Token::Ident(a), Token::Ident(b)) => a == b,
            (Token::String(a), Token::String(b)) => a == b,
            (a, b) => std::mem::discriminant(a) == std::mem::discriminant(b),
        }
    }
}

impl Eq for Token {}

impl Hash for Token {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Token::Num(i) => i.hash(state),
            Token::Float(f) => f.to_bits().hash(state),
            Token::Ident(s) => s.hash(state),
            Token::String(s) => s.hash(state),
            _ => {}
        }
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Num(n) => write!(f, "{}", n),
            Token::Float(n) => write!(f, "{}", n),
            Token::Ident(s) => write!(f, "{}", s),
            Token::String(s) => write!(f, "{:?}", s),
            Token::Ellipsis => write!(f, "..."),
            _ => write!(f, "{:?}", self),
        }
    }
}

pub type Span = std::ops::Range<usize>;

pub fn lexer() -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> {
    let num_or_float = text::int::<char, Simple<char>>(10)
    .then(just('.').then(text::digits(10)).or_not())
    .map(|(int, frac_opt)| {
        if let Some((_, frac)) = frac_opt {
            Token::Float((int + "." + &frac).parse().unwrap())
        } else {
            Token::Num(int.parse().unwrap())
        }
    });

    let ident = text::ident().map(Token::Ident);

    let kw1 = choice((
        text::keyword("let").to(Token::Let),
                      text::keyword("direct").to(Token::Direct),
                      text::keyword("alloc").to(Token::Alloc),
                      text::keyword("dealloc").to(Token::Dealloc),
                      text::keyword("write").to(Token::Write),
                      text::keyword("cast").to(Token::Cast),
                      text::keyword("sizeof").to(Token::SizeOf),
                      text::keyword("i8").to(Token::I8Type),
                      text::keyword("int").to(Token::I32Type),
                      text::keyword("I32").to(Token::I32Type), // Support alias
                      text::keyword("i64").to(Token::I64Type),
                      text::keyword("bool").to(Token::BoolType),
                      text::keyword("unit").to(Token::UnitType),
                      text::keyword("f32").to(Token::F32Type),
                      text::keyword("f64").to(Token::F64Type),
                      text::keyword("true").to(Token::True),
                      text::keyword("false").to(Token::False),
                      text::keyword("if").to(Token::If),
    ));

    let kw2 = choice((
        text::keyword("while").to(Token::While),
                      text::keyword("else").to(Token::Else),
                      text::keyword("break").to(Token::Break),
                      text::keyword("continue").to(Token::Continue),
                      text::keyword("match").to(Token::Match),
                      text::keyword("impl").to(Token::Impl),
                      text::keyword("fn").to(Token::Fn),
                      text::keyword("from").to(Token::From),
                      text::keyword("require").to(Token::Require),
                      text::keyword("as").to(Token::As),
                      text::keyword("struct").to(Token::Struct),
                      text::keyword("union").to(Token::Union),
                      text::keyword("for").to(Token::For),
                      text::keyword("return").to(Token::Return),
    ));

    let kw = kw1.or(kw2);

    let op1 = choice((
        just("=>").to(Token::DoubleArrow),
                      just("...").to(Token::Ellipsis),
                      just("==").to(Token::EqEq),
                      just("!=").to(Token::Ne),
                      just("<=").to(Token::Le),
                      just(">=").to(Token::Ge),
                      just("&&").to(Token::AndAnd),
                      just("||").to(Token::OrOr),
                      just("->").to(Token::Arrow),
                      just('*').to(Token::Star),
                      just('&').to(Token::Amp),
                      just('+').to(Token::Plus),
                      just('-').to(Token::Minus),
                      just('/').to(Token::Slash),
                      just('%').to(Token::Percent),
                      just('=').to(Token::Eq),
    ));

    let op2 = choice((
        just('<').to(Token::Lt),
                      just('>').to(Token::Gt),
                      just(':').to(Token::Colon),
                      just(';').to(Token::Semi),
                      just('(').to(Token::LParen),
                      just(')').to(Token::RParen),
                      just('{').to(Token::LBrace),
                      just('}').to(Token::RBrace),
                      just('[').to(Token::LBracket),
                      just(']').to(Token::RBracket),
                      just(',').to(Token::Comma),
                      just('.').to(Token::Dot),
    ));

    let op = op1.or(op2);

    let string = just('"')
    .ignore_then(filter(|c| *c != '"').repeated())
    .then_ignore(just('"'))
    .map(|chars: Vec<char>| Token::String(chars.into_iter().collect::<String>()));

    let token = num_or_float.or(kw).or(ident).or(op).or(string);

    // Comments: // ... until newline or EOF
    // Ensure both branches return () to match whitespace
    let comment = just("//")
    .then(take_until(just('\n').to(()).or(end())))
    .to(());

    // Explicit whitespace that returns ()
    // MUST match at least one character to prevent infinite loop in padding.repeated()
    let whitespace = filter(|c: &char| c.is_whitespace())
    .repeated().at_least(1)
    .to(());

    // Padding: whitespace or comments, repeated
    // Both sides of OR return (), so it's typesafe.
    let padding = whitespace.or(comment).repeated();

    token
    .map_with_span(|tok, span| (tok, span))
    .padded_by(padding.clone())
    .repeated()
    .delimited_by(padding, empty())
    .then_ignore(end())
}
