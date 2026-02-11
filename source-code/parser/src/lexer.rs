use chumsky::prelude::*;
use chumsky::text::{ident, keyword as text_keyword};
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
    I8Type,
    I32Type,
    BoolType,
    UnitType,
    F32Type,
    F64Type,
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
    Struct,
    Union,
    For,
    Return,
    Dot,
}

// Manual PartialEq/Eq/Hash for f64 handling to satisfy Chumsky's Simple error requirements
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
    })
    .padded();

    let ident = ident().map(Token::Ident).padded();

    let kw = choice((
        text_keyword("let").to(Token::Let),
                     text_keyword("direct").to(Token::Direct),
                     text_keyword("alloc").to(Token::Alloc),
                     text_keyword("dealloc").to(Token::Dealloc),
                     text_keyword("write").to(Token::Write),
                     text_keyword("i8").to(Token::I8Type),
                     text_keyword("int").to(Token::I32Type),
                     text_keyword("bool").to(Token::BoolType),
                     text_keyword("unit").to(Token::UnitType),
                     text_keyword("f32").to(Token::F32Type),
                     text_keyword("f64").to(Token::F64Type),
                     text_keyword("true").to(Token::True),
                     text_keyword("false").to(Token::False),
                     text_keyword("if").to(Token::If),
                     text_keyword("while").to(Token::While),
                     text_keyword("else").to(Token::Else),
                     text_keyword("fn").to(Token::Fn),
                     text_keyword("from").to(Token::From),
                     text_keyword("require").to(Token::Require),
                     text_keyword("as").to(Token::As),
                     text_keyword("struct").to(Token::Struct),
                     text_keyword("union").to(Token::Union),
                     text_keyword("for").to(Token::For),
                     text_keyword("return").to(Token::Return),
    ))
    .padded();

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
                     just('.').to(Token::Dot),
    ))
    .padded();

    let string = just('"')
    .ignore_then(filter(|c| *c != '"').repeated())
    .then_ignore(just('"'))
    .map(|chars: Vec<char>| Token::String(chars.into_iter().collect::<String>()))
    .padded();

    let token = num_or_float.or(kw).or(ident).or(op).or(string);

    token
    .map_with_span(|tok, span| (tok, span))
    .repeated()
    .then_ignore(end())
}
