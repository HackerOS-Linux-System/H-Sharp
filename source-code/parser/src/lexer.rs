use chumsky::prelude::*;
use chumsky::text;
use std::hash::{Hash, Hasher};

#[derive(Clone, Debug)]
pub enum Token {
    Num(i64),
    TypedNum(i64, String),
    Float(f64),
    TypedFloat(f64, String),
    Ident(String),
    Let,
    Direct,
    Alloc,
    Dealloc,
    Write,
    Cast,
    SizeOf,
    I8Type,
    I32Type,
    I64Type,
    U8Type,
    U16Type,
    U32Type,
    U64Type,
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
    Str(String),   // renamed from String to avoid collision
    Comma,
    Struct,
    Union,
    For,
    Return,
    Dot,
    Ellipsis,
    DoubleArrow,
    BitOr,
    BitXor,
    BitNot,
    Shl,
    Shr,
    PlusEq,
    MinusEq,
    MulEq,
    DivEq,
    ModEq,
    AndEq,
    OrEq,
    XorEq,
    ShlEq,
    ShrEq,
    DotDot,
    DotDotEq,
    Question,
    Enum,
    Const,
    Type,
    Async,
    Await,
    ByteChar(u8),
    RawString(String),
    MultilineString(String),
    HexString(Vec<u8>),
    ByteString(Vec<u8>),
    ColonColon,
    Bang,
    At,
    Hash,
    Tilde,
    Attribute(String),
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Token::Num(a), Token::Num(b)) => a == b,
            (Token::TypedNum(a, sa), Token::TypedNum(b, sb)) => a == b && sa == sb,
            (Token::Float(a), Token::Float(b)) => a.to_bits() == b.to_bits(),
            (Token::TypedFloat(a, sa), Token::TypedFloat(b, sb)) => a.to_bits() == b.to_bits() && sa == sb,
            (Token::Ident(a), Token::Ident(b)) => a == b,
            (Token::Str(a), Token::Str(b)) => a == b,
            (Token::RawString(a), Token::RawString(b)) => a == b,
            (Token::MultilineString(a), Token::MultilineString(b)) => a == b,
            (Token::HexString(a), Token::HexString(b)) => a == b,
            (Token::ByteString(a), Token::ByteString(b)) => a == b,
            (Token::ByteChar(a), Token::ByteChar(b)) => a == b,
            (Token::Attribute(a), Token::Attribute(b)) => a == b,
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
            Token::TypedNum(i, s) => { i.hash(state); s.hash(state); }
            Token::Float(f) => f.to_bits().hash(state),
            Token::TypedFloat(f, s) => { f.to_bits().hash(state); s.hash(state); }
            Token::Ident(s) => s.hash(state),
            Token::Str(s) => s.hash(state),
            Token::RawString(s) => s.hash(state),
            Token::MultilineString(s) => s.hash(state),
            Token::HexString(v) => v.hash(state),
            Token::ByteString(v) => v.hash(state),
            Token::ByteChar(b) => b.hash(state),
            Token::Attribute(s) => s.hash(state),
            _ => {}
        }
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Num(n) => write!(f, "{}", n),
            Token::TypedNum(n, s) => write!(f, "{}{}", n, s),
            Token::Float(n) => write!(f, "{}", n),
            Token::TypedFloat(n, s) => write!(f, "{}{}", n, s),
            Token::Ident(s) => write!(f, "{}", s),
            Token::Str(s) => write!(f, "{:?}", s),
            Token::RawString(s) => write!(f, "r{:?}", s),
            Token::MultilineString(s) => write!(f, "\"\"\"{}\"\"\"", s),
            Token::HexString(v) => write!(f, "x\"{}\"", v.iter().map(|b| format!("{:02X}", b)).collect::<String>()),
            Token::ByteString(v) => write!(f, "b\"{}\"", v.iter().map(|b| format!("{:02X}", b)).collect::<String>()),
            Token::ByteChar(b) => write!(f, "b'{}'", *b as char),
            Token::Attribute(s) => write!(f, "#[{}]", s),
            Token::Ellipsis => write!(f, "..."),
            _ => write!(f, "{:?}", self),
        }
    }
}

pub type Span = std::ops::Range<usize>;

pub fn lexer() -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> {
    // Decimal number
    let decimal = text::int(10)
    .try_map(|s: String, span| {
        s.replace('_', "").parse::<i64>().map_err(|e| Simple::custom(span, e.to_string()))
    });

    // Hex number: 0x...
    let hex = just("0x")
    .ignore_then(
        filter(|c: &char| matches!(*c, '0'..='9' | 'a'..='f' | 'A'..='F' | '_'))
        .repeated()
        .at_least(1),
    )
    .map(|digits: Vec<char>| digits.into_iter().filter(|c| *c != '_').collect::<String>())
    .try_map(|s, span| {
        i64::from_str_radix(&s, 16).map_err(|e| Simple::custom(span, e.to_string()))
    });

    // Binary number: 0b...
    let binary = just("0b")
    .ignore_then(
        filter(|c: &char| matches!(*c, '0' | '1' | '_'))
        .repeated()
        .at_least(1),
    )
    .map(|digits: Vec<char>| digits.into_iter().filter(|c| *c != '_').collect::<String>())
    .try_map(|s, span| {
        i64::from_str_radix(&s, 2).map_err(|e| Simple::custom(span, e.to_string()))
    });

    // Octal number: 0o...
    let octal = just("0o")
    .ignore_then(
        filter(|c: &char| matches!(*c, '0'..='7' | '_'))
        .repeated()
        .at_least(1),
    )
    .map(|digits: Vec<char>| digits.into_iter().filter(|c| *c != '_').collect::<String>())
    .try_map(|s, span| {
        i64::from_str_radix(&s, 8).map_err(|e| Simple::custom(span, e.to_string()))
    });

    // Type suffix for integers
    let int_type_suffix = choice((
        just("u8").to("u8".to_string()),
                                  just("u16").to("u16".to_string()),
                                  just("u32").to("u32".to_string()),
                                  just("u64").to("u64".to_string()),
                                  just("i8").to("i8".to_string()),
                                  just("i32").to("i32".to_string()),
                                  just("i64").to("i64".to_string()),
    ))
    .or_not();

    // Number with optional suffix — hex/binary/octal before decimal to avoid prefix clash
    let num_with_suffix = choice((hex, binary, octal, decimal))
    .then(int_type_suffix)
    .map(|(val, suffix)| {
        if let Some(s) = suffix {
            Token::TypedNum(val, s)
        } else {
            Token::Num(val)
        }
    });

    // Float: integer.fraction
    let float = text::int(10)
    .then_ignore(just('.'))
    .then(text::digits(10))
    .map(|(int, frac): (String, String)| format!("{}.{}", int, frac))
    .try_map(|s: String, span| {
        s.parse::<f64>().map_err(|e| Simple::custom(span, e.to_string()))
    });

    // Float suffix
    let float_suffix = choice((
        just("f32").to("f32".to_string()),
                               just("f64").to("f64".to_string()),
    ))
    .or_not();

    let float_with_suffix = float
    .then(float_suffix)
    .map(|(val, suffix)| {
        if let Some(s) = suffix {
            Token::TypedFloat(val, s)
        } else {
            Token::Float(val)
        }
    });

    // Ident
    let ident = text::ident().map(Token::Ident);

    // Keywords — must come before ident
    let kw1a = choice((
        text::keyword("let").to(Token::Let),
                       text::keyword("direct").to(Token::Direct),
                       text::keyword("alloc").to(Token::Alloc),
                       text::keyword("dealloc").to(Token::Dealloc),
                       text::keyword("write").to(Token::Write),
                       text::keyword("cast").to(Token::Cast),
                       text::keyword("sizeof").to(Token::SizeOf),
                       text::keyword("i8").to(Token::I8Type),
                       text::keyword("i32").to(Token::I32Type),
                       text::keyword("i64").to(Token::I64Type),
    ));
    let kw1b = choice((
        text::keyword("u8").to(Token::U8Type),
                       text::keyword("u16").to(Token::U16Type),
                       text::keyword("u32").to(Token::U32Type),
                       text::keyword("u64").to(Token::U64Type),
                       text::keyword("bool").to(Token::BoolType),
                       text::keyword("unit").to(Token::UnitType),
                       text::keyword("f32").to(Token::F32Type),
                       text::keyword("f64").to(Token::F64Type),
                       text::keyword("true").to(Token::True),
                       text::keyword("false").to(Token::False),
    ));
    let kw1c = choice((
        text::keyword("if").to(Token::If),
                       text::keyword("enum").to(Token::Enum),
                       text::keyword("const").to(Token::Const),
                       text::keyword("type").to(Token::Type),
                       text::keyword("async").to(Token::Async),
                       text::keyword("await").to(Token::Await),
    ));
    let kw2a = choice((
        text::keyword("while").to(Token::While),
                       text::keyword("else").to(Token::Else),
                       text::keyword("break").to(Token::Break),
                       text::keyword("continue").to(Token::Continue),
                       text::keyword("match").to(Token::Match),
                       text::keyword("impl").to(Token::Impl),
                       text::keyword("fn").to(Token::Fn),
    ));
    let kw2b = choice((
        text::keyword("from").to(Token::From),
                       text::keyword("require").to(Token::Require),
                       text::keyword("as").to(Token::As),
                       text::keyword("struct").to(Token::Struct),
                       text::keyword("union").to(Token::Union),
                       text::keyword("for").to(Token::For),
                       text::keyword("return").to(Token::Return),
    ));
    let kw = kw1a.or(kw1b).or(kw1c).or(kw2a).or(kw2b);

    // Operators (longer first to avoid prefix ambiguity)
    let op_group1 = choice((
        just("::").to(Token::ColonColon),
                            just("=>").to(Token::DoubleArrow),
                            just("...").to(Token::Ellipsis),
                            just("..=").to(Token::DotDotEq),
                            just("..").to(Token::DotDot),
                            just("==").to(Token::EqEq),
                            just("!=").to(Token::Ne),
                            just("<=").to(Token::Le),
                            just(">=").to(Token::Ge),
                            just("&&").to(Token::AndAnd),
    ));
    let op_group2 = choice((
        just("||").to(Token::OrOr),
                            just("->").to(Token::Arrow),
                            just("<<=").to(Token::ShlEq),
                            just(">>=").to(Token::ShrEq),
                            just("+=").to(Token::PlusEq),
                            just("-=").to(Token::MinusEq),
                            just("*=").to(Token::MulEq),
                            just("/=").to(Token::DivEq),
                            just("%=").to(Token::ModEq),
                            just("&=").to(Token::AndEq),
    ));
    let op_group3 = choice((
        just("|=").to(Token::OrEq),
                            just("^=").to(Token::XorEq),
                            just("<<").to(Token::Shl),
                            just(">>").to(Token::Shr),
                            just('*').to(Token::Star),
                            just('&').to(Token::Amp),
                            just('+').to(Token::Plus),
                            just('-').to(Token::Minus),
                            just('/').to(Token::Slash),
                            just('%').to(Token::Percent),
    ));
    let op_group4 = choice((
        just('=').to(Token::Eq),
                            just('|').to(Token::BitOr),
                            just('^').to(Token::BitXor),
                            just('~').to(Token::BitNot),
                            just('!').to(Token::Bang),
                            just('@').to(Token::At),
                            just('#').to(Token::Hash),
                            just('>').to(Token::Gt),
                            just('<').to(Token::Lt),
                            just(':').to(Token::Colon),
    ));
    let op_group5 = choice((
        just(';').to(Token::Semi),
                            just('(').to(Token::LParen),
                            just(')').to(Token::RParen),
                            just('{').to(Token::LBrace),
                            just('}').to(Token::RBrace),
                            just('[').to(Token::LBracket),
                            just(']').to(Token::RBracket),
                            just(',').to(Token::Comma),
                            just('.').to(Token::Dot),
                            just('?').to(Token::Question),
    ));
    let op = op_group1.or(op_group2).or(op_group3).or(op_group4).or(op_group5);

    // Escape sequences
    let escape = just('\\').ignore_then(choice((
        just('n').to('\n'),
                                                just('t').to('\t'),
                                                just('r').to('\r'),
                                                just('\\').to('\\'),
                                                just('"').to('"'),
                                                just('0').to('\0'),
                                                just('x')
                                                .ignore_then(
                                                    filter(|c: &char| c.is_ascii_hexdigit())
                                                    .repeated()
                                                    .exactly(2),
                                                )
                                                .map(|hex: Vec<char>| {
                                                    let s: String = hex.into_iter().collect();
                                                    char::from_u32(u32::from_str_radix(&s, 16).unwrap_or(0)).unwrap_or('\u{FFFD}')
                                                }),
                                                just('u')
                                                .ignore_then(
                                                    filter(|c: &char| c.is_ascii_hexdigit())
                                                    .repeated()
                                                    .exactly(4),
                                                )
                                                .map(|hex: Vec<char>| {
                                                    let s: String = hex.into_iter().collect();
                                                    char::from_u32(u32::from_str_radix(&s, 16).unwrap_or(0)).unwrap_or('\u{FFFD}')
                                                }),
                                                just('U')
                                                .ignore_then(
                                                    filter(|c: &char| c.is_ascii_hexdigit())
                                                    .repeated()
                                                    .exactly(8),
                                                )
                                                .map(|hex: Vec<char>| {
                                                    let s: String = hex.into_iter().collect();
                                                    char::from_u32(u32::from_str_radix(&s, 16).unwrap_or(0)).unwrap_or('\u{FFFD}')
                                                }),
    )));

    // String with escapes
    let string_char = filter(|c: &char| *c != '"' && *c != '\\').or(escape.clone());
    let string = just('"')
    .ignore_then(string_char.repeated())
    .then_ignore(just('"'))
    .map(|chars: Vec<char>| Token::Str(chars.into_iter().collect()));

    // Raw string: r"..."
    let raw_string = just("r\"")
    .ignore_then(filter(|c: &char| *c != '"').repeated())
    .then_ignore(just('"'))
    .map(|chars: Vec<char>| Token::RawString(chars.into_iter().collect()));

    // Byte char: b'A'
    let byte_char = just("b'")
    .ignore_then(filter(|c: &char| *c != '\'').map(|c| c as u8))
    .then_ignore(just('\''))
    .map(Token::ByteChar);

    // Multiline string: """..."""  — use take_until to match closing """
    let multiline_string = just("\"\"\"")
    .ignore_then(take_until(just("\"\"\"")))
    .map(|(chars, _): (Vec<char>, _)| Token::MultilineString(chars.into_iter().collect()));

    // Hex string: x"DEADBEEF"
    let hex_string = just("x\"")
    .ignore_then(
        filter(|c: &char| c.is_ascii_hexdigit() || c.is_whitespace()).repeated(),
    )
    .then_ignore(just('"'))
    .try_map(|chars: Vec<char>, span: Span| {
        let s: String = chars.into_iter().filter(|c| !c.is_whitespace()).collect();
        if s.len() % 2 != 0 {
            return Err(Simple::custom(span, "Odd hex string length"));
        }
        (0..s.len())
        .step_by(2)
        .map(|i| {
            u8::from_str_radix(&s[i..i + 2], 16)
            .map_err(|e| Simple::custom(span.clone(), e.to_string()))
        })
        .collect::<Result<Vec<u8>, _>>()
        .map(Token::HexString)
    });

    // Byte string: b"hello"
    let byte_string = just("b\"")
    .ignore_then(filter(|c: &char| *c != '"').repeated())
    .then_ignore(just('"'))
    .map(|chars: Vec<char>| Token::ByteString(chars.into_iter().map(|c| c as u8).collect()));

    // Attributes: #[inline]
    let attribute = just("#[")
    .ignore_then(filter(|c: &char| *c != ']').repeated())
    .then_ignore(just(']'))
    .map(|chars: Vec<char>| Token::Attribute(chars.into_iter().collect()));

    // Token order matters: longer/more specific patterns first
    let token = multiline_string
    .or(hex_string)
    .or(byte_string)
    .or(raw_string)
    .or(byte_char)
    .or(float_with_suffix)
    .or(num_with_suffix)
    .or(attribute)
    .or(kw)
    .or(ident)
    .or(op)
    .or(string);

    // Comments
    let line_comment = just('@')
    .then(take_until(just('\n').to(()).or(end())))
    .ignored();
    let block_comment = just("@*").then(take_until(just("*@"))).ignored();
    let comment = block_comment.or(line_comment);

    // Whitespace
    let whitespace = filter(|c: &char| c.is_whitespace())
    .repeated()
    .at_least(1)
    .ignored();

    let padding = whitespace.or(comment).repeated();

    token
    .map_with_span(|tok, span| (tok, span))
    .padded_by(padding)
    .repeated()
    .then_ignore(end())
}
