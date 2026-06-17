use crate::span::{Span, Position};
use crate::error::{ParseError, ParseErrorKind};

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals
    Integer(i64),
    Float(f64),
    StringLit(String),
    ByteLit(Vec<u8>),
    Bool(bool),
    Nil,
    // Identifiers & keywords
    Ident(String),
    // Keywords
    Fn, Let, Mut, If, Else, Elsif, While, For, In,
    Return, Use, From, Pub, Struct, Enum, Impl, Trait,
    Match, Is, End, Then, Type, As, Self_, New,
    Break, Continue, Unsafe, Extern, Mod, Async, Await,
    Arena, Manual, Write, Using,
    // Directives
    Directive(String),
    FastDirective(String),
    // Doc / block comments
    DocComment(String),
    BlockCommentStart,
    BlockCommentEnd,
    // Primitive types
    TInt, TUint,
    TI8, TI16, TI32, TI64, TI128,
    TU8, TU16, TU32, TU64, TU128,
    TF32, TF64,
    TBool, TString, TBytes, TVoid, TAny,
    // Operators
    Plus, Minus, Star, Slash, Percent,
    Eq, NotEq, Lt, Gt, LtEq, GtEq,
    And, Or, Not,
    BitAnd, BitOr, BitXor, BitNot, Shl, Shr,
    Assign,
    PlusAssign, MinusAssign, StarAssign, SlashAssign,
    Arrow,        // ->
    FatArrow,     // =>
    DotDot,       // ..
    DotDotEq,     // ..=
    Dot,          // .
    ColonColon,   // ::
    Colon,        // :
    Semicolon,    // ;
    Comma,        // ,
    Pipe,         // |
    Question,     // ?
    Hash,         // #
    At,           // @
    // Delimiters
    LParen, RParen,
    LBrace, RBrace,
    LBracket, RBracket,
    // Special
    Newline,
    EOF,
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub text: String,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span, text: impl Into<String>) -> Self {
        Self { kind, span, text: text.into() }
    }
}

pub struct Lexer {
    source: Vec<char>,
    pos:    usize,
    line:   usize,
    col:    usize,
    file:   String,
}

impl Lexer {
    pub fn new(source: &str, file: impl Into<String>) -> Self {
        Self {
            source: source.chars().collect(),
            pos:    0,
            line:   1,
            col:    1,
            file:   file.into(),
        }
    }

    fn current(&self) -> Option<char> { self.source.get(self.pos).copied() }
    fn peek(&self, n: usize) -> Option<char> { self.source.get(self.pos + n).copied() }

    fn advance(&mut self) -> Option<char> {
        let ch = self.source.get(self.pos).copied();
        if let Some(c) = ch {
            self.pos += 1;
            if c == '\n' { self.line += 1; self.col = 1; }
            else          { self.col  += 1; }
        }
        ch
    }

    fn position(&self) -> Position {
        Position { line: self.line, col: self.col, offset: self.pos }
    }

    fn skip_whitespace_no_newline(&mut self) {
        while matches!(self.current(), Some(' ') | Some('\t') | Some('\r')) {
            self.advance();
        }
    }

    // ── String literals ────────────────────────────────────────────────────────
    // Full escape support:
    //   \n \t \r \\ \" \0
    //   \[ \] \( \) \{ \} — pass through as the literal character (shell regex)
    //   \' — single quote (shell strings)
    //   \$ — dollar sign (shell variable prevention)
    //   \x41 — hex escape
    //   \uXXXX — unicode escape
    // All other single-byte non-ASCII (e.g. em-dash —) are passed through as-is.
    // Raw strings: r"..." — no escape processing at all.

    fn read_string(&mut self, start: Position) -> Result<Token, ParseError> {
        let mut s = String::new();
        loop {
            match self.advance() {
                None => return Err(ParseError::new(
                    ParseErrorKind::UnterminatedString,
                    Span::new(start, self.position(), self.file.clone()),
                                                   "unterminated string literal",
                                                   vec!["close the string with `\"`".to_string()],
                )),
                Some('"') => break,
                Some('\\') => {
                    match self.advance() {
                        Some('n')  => s.push('\n'),
                        Some('t')  => s.push('\t'),
                        Some('r')  => s.push('\r'),
                        Some('\\') => s.push('\\'),
                        Some('"')  => s.push('"'),
                        Some('0')  => s.push('\0'),
                        Some('\'') => s.push('\''),
                        // Shell / regex escapes — keep the character as-is
                        Some('[')  => s.push('['),
                        Some(']')  => s.push(']'),
                        Some('(')  => s.push('('),
                        Some(')')  => s.push(')'),
                        Some('{')  => s.push('{'),
                        Some('}')  => s.push('}'),
                        Some('$')  => s.push('$'),
                        Some('?')  => s.push('?'),
                        Some('*')  => s.push('*'),
                        Some('+')  => s.push('+'),
                        Some('.')  => s.push('.'),
                        Some('^')  => s.push('^'),
                        Some('|')  => s.push('|'),
                        Some('/')  => s.push('/'),
                        Some('-')  => s.push('-'),
                        Some('<')  => s.push('<'),
                        Some('>')  => s.push('>'),
                        Some('@')  => s.push('@'),
                        Some('&')  => s.push('&'),
                        Some('!')  => s.push('!'),
                        Some('#')  => s.push('#'),
                        Some('%')  => s.push('%'),
                        Some('=')  => s.push('='),
                        Some(':')  => s.push(':'),
                        Some(';')  => s.push(';'),
                        Some(',')  => s.push(','),
                        Some('_')  => s.push('_'),
                        Some('`')  => s.push('`'),
                        Some('~')  => s.push('~'),
                        Some('x') => {
                            // \xNN hex escape
                            let h1 = self.advance().unwrap_or('0');
                            let h2 = self.advance().unwrap_or('0');
                            let hex_str = format!("{}{}", h1, h2);
                            if let Ok(n) = u8::from_str_radix(&hex_str, 16) {
                                s.push(n as char);
                            } else {
                                s.push('\\'); s.push('x'); s.push(h1); s.push(h2);
                            }
                        }
                        Some('u') => {
                            // \uXXXX unicode escape
                            let mut hex_str = String::new();
                            if self.current() == Some('{') {
                                self.advance();
                                while self.current().map(|c| c.is_ascii_hexdigit()).unwrap_or(false) {
                                    hex_str.push(self.advance().unwrap());
                                }
                                if self.current() == Some('}') { self.advance(); }
                            } else {
                                for _ in 0..4 {
                                    if let Some(c) = self.current() {
                                        if c.is_ascii_hexdigit() { hex_str.push(self.advance().unwrap()); }
                                    }
                                }
                            }
                            if let Ok(n) = u32::from_str_radix(&hex_str, 16) {
                                if let Some(c) = char::from_u32(n) { s.push(c); }
                            }
                        }
                        Some(c) => {
                            // Unknown escape — pass through both backslash and character
                            // This makes the lexer lenient: shell strings work without
                            // writers needing to double-escape everything.
                            s.push('\\');
                            s.push(c);
                        }
                        None => return Err(ParseError::new(
                            ParseErrorKind::UnterminatedString,
                            Span::new(start, self.position(), self.file.clone()),
                                                           "unterminated escape sequence",
                                                           vec![],
                        )),
                    }
                }
                // Single quote inside double-quoted string — allowed as-is
                Some('\'') => s.push('\''),
                // Dollar sign — allowed as-is (shell vars in strings)
                Some('$') => s.push('$'),
                // Any other character (including Unicode like —, ą, ź, …) — pass through
                Some(c) => s.push(c),
            }
        }
        let end = self.position();
        Ok(Token::new(
            TokenKind::StringLit(s.clone()),
                      Span::new(start, end, self.file.clone()),
                      format!("\"{}\"", s),
        ))
    }

    /// Raw string: r"..." — no escape processing
    fn read_raw_string(&mut self, start: Position) -> Result<Token, ParseError> {
        // Consume opening "
        if self.current() != Some('"') {
            return Err(ParseError::new(
                ParseErrorKind::UnexpectedToken,
                Span::new(start, self.position(), self.file.clone()),
                                       "expected `\"` after `r`",
                                       vec![],
            ));
        }
        self.advance();
        let mut s = String::new();
        loop {
            match self.advance() {
                None | Some('\n') => return Err(ParseError::new(
                    ParseErrorKind::UnterminatedString,
                    Span::new(start, self.position(), self.file.clone()),
                                                                "unterminated raw string",
                                                                vec!["close with `\"`".to_string()],
                )),
                Some('"') => break,
                Some(c)   => s.push(c),
            }
        }
        let end = self.position();
        Ok(Token::new(
            TokenKind::StringLit(s.clone()),
                      Span::new(start, end, self.file.clone()),
                      format!("r\"{}\"", s),
        ))
    }

    fn read_number(&mut self, start: Position) -> Token {
        let mut num      = String::new();
        let mut is_float = false;
        let mut is_hex   = false;
        let mut is_bin   = false;

        let first = self.advance().unwrap();
        num.push(first);

        if first == '0' {
            match self.current() {
                Some('x') | Some('X') => {
                    is_hex = true;
                    num.push(self.advance().unwrap());
                    while let Some(c) = self.current() {
                        if c.is_ascii_hexdigit() || c == '_' { num.push(self.advance().unwrap()); }
                        else { break; }
                    }
                }
                Some('b') | Some('B') => {
                    is_bin = true;
                    num.push(self.advance().unwrap());
                    while matches!(self.current(), Some('0') | Some('1') | Some('_')) {
                        num.push(self.advance().unwrap());
                    }
                }
                _ => {}
            }
        }

        if !is_hex && !is_bin {
            while let Some(c) = self.current() {
                if c.is_ascii_digit() || c == '_' { num.push(self.advance().unwrap()); }
                else { break; }
            }
            if self.current() == Some('.')
                && self.peek(1).map(|c| c.is_ascii_digit()).unwrap_or(false)
                {
                    is_float = true;
                    num.push(self.advance().unwrap());
                    while let Some(c) = self.current() {
                        if c.is_ascii_digit() || c == '_' { num.push(self.advance().unwrap()); }
                        else { break; }
                    }
                }
                if matches!(self.current(), Some('e') | Some('E')) {
                    is_float = true;
                    num.push(self.advance().unwrap());
                    if matches!(self.current(), Some('+') | Some('-')) { num.push(self.advance().unwrap()); }
                    while let Some(c) = self.current() {
                        if c.is_ascii_digit() { num.push(self.advance().unwrap()); }
                        else { break; }
                    }
                }
        }

        let end   = self.position();
        let clean = num.replace('_', "");
        let span  = Span::new(start, end, self.file.clone());
        if is_float {
            let v: f64 = clean.parse().unwrap_or(0.0);
            Token::new(TokenKind::Float(v), span, num)
        } else if is_hex {
            let v = i64::from_str_radix(&clean[2..], 16).unwrap_or(0);
            Token::new(TokenKind::Integer(v), span, num)
        } else if is_bin {
            let v = i64::from_str_radix(&clean[2..], 2).unwrap_or(0);
            Token::new(TokenKind::Integer(v), span, num)
        } else {
            let v: i64 = clean.parse().unwrap_or(0);
            Token::new(TokenKind::Integer(v), span, num)
        }
    }

    fn read_ident(&mut self, start: Position) -> Token {
        let mut s = String::new();
        while let Some(c) = self.current() {
            if c.is_alphanumeric() || c == '_' { s.push(self.advance().unwrap()); }
            else { break; }
        }
        let end  = self.position();
        let span = Span::new(start, end, self.file.clone());
        let kind = match s.as_str() {
            "fn"       => TokenKind::Fn,
            "let"      => TokenKind::Let,
            "mut"      => TokenKind::Mut,
            "if"       => TokenKind::If,
            "else"     => TokenKind::Else,
            "elsif"    => TokenKind::Elsif,
            "while"    => TokenKind::While,
            "for"      => TokenKind::For,
            "in"       => TokenKind::In,
            "return"   => TokenKind::Return,
            "use"      => TokenKind::Use,
            "from"     => TokenKind::From,
            "pub"      => TokenKind::Pub,
            "struct"   => TokenKind::Struct,
            "enum"     => TokenKind::Enum,
            "impl"     => TokenKind::Impl,
            "trait"    => TokenKind::Trait,
            "match"    => TokenKind::Match,
            "is"       => TokenKind::Is,
            "end"      => TokenKind::End,
            "then"     => TokenKind::Then,
            "type"     => TokenKind::Type,
            "as"       => TokenKind::As,
            "self"     => TokenKind::Self_,
            "new"      => TokenKind::New,
            "break"    => TokenKind::Break,
            "continue" => TokenKind::Continue,
            "unsafe"   => TokenKind::Unsafe,
            "using"    => TokenKind::Using,
            "arena"    => TokenKind::Arena,
            "manual"   => TokenKind::Manual,
            "extern"   => TokenKind::Extern,
            "mod"      => TokenKind::Mod,
            "async"    => TokenKind::Async,
            "await"    => TokenKind::Await,
            "write"    => TokenKind::Write,
            "true"     => TokenKind::Bool(true),
            "false"    => TokenKind::Bool(false),
            "nil"      => TokenKind::Nil,
            "int"      => TokenKind::TInt,
            "uint"     => TokenKind::TUint,
            "i8"       => TokenKind::TI8,
            "i16"      => TokenKind::TI16,
            "i32"      => TokenKind::TI32,
            "i64"      => TokenKind::TI64,
            "i128"     => TokenKind::TI128,
            "u8"       => TokenKind::TU8,
            "u16"      => TokenKind::TU16,
            "u32"      => TokenKind::TU32,
            "u64"      => TokenKind::TU64,
            "u128"     => TokenKind::TU128,
            "f32"      => TokenKind::TF32,
            "f64"      => TokenKind::TF64,
            "bool"     => TokenKind::TBool,
            "string"   => TokenKind::TString,
            "bytes"    => TokenKind::TBytes,
            "void"     => TokenKind::TVoid,
            "any"      => TokenKind::TAny,
            _          => TokenKind::Ident(s.clone()),
        };
        Token::new(kind, span, s)
    }

    // ── Main tokenize loop ────────────────────────────────────────────────────

    pub fn tokenize(&mut self) -> Result<Vec<Token>, Vec<ParseError>> {
        let mut tokens = Vec::new();
        let mut errors = Vec::new();

        loop {
            self.skip_whitespace_no_newline();
            let start = self.position();

            match self.current() {
                None => {
                    tokens.push(Token::new(
                        TokenKind::EOF,
                        Span::new(start.clone(), start, self.file.clone()),
                                           "",
                    ));
                    break;
                }

                // Doc comment ///
                Some('/') if self.peek(1) == Some('/') && self.peek(2) == Some('/') => {
                    self.advance(); self.advance(); self.advance();
                    let mut doc = String::new();
                    while let Some(c) = self.current() {
                        if c == '\n' { break; }
                        doc.push(self.advance().unwrap());
                    }
                    tokens.push(Token::new(
                        TokenKind::DocComment(doc.trim().to_string()),
                                           Span::new(start, self.position(), self.file.clone()),
                                           "///",
                    ));
                }

                // ;; line comment
                Some(';') if self.peek(1) == Some(';') => {
                    while self.current().map(|c| c != '\n').unwrap_or(false) {
                        self.advance();
                    }
                }

                // // block comment — ends with \\
                Some('/') if self.peek(1) == Some('/') => {
                    self.advance(); self.advance();
                    tokens.push(Token::new(
                        TokenKind::BlockCommentStart,
                        Span::new(start.clone(), self.position(), self.file.clone()),
                                           "//",
                    ));
                    loop {
                        match self.current() {
                            None => break,
                            Some('\\') if self.peek(1) == Some('\\') => {
                                self.advance(); self.advance();
                                tokens.push(Token::new(
                                    TokenKind::BlockCommentEnd,
                                    Span::new(start, self.position(), self.file.clone()),
                                                       "\\\\",
                                ));
                                break;
                            }
                            Some(c) => {
                                if c == '\n' { self.line += 1; self.col = 1; }
                                self.advance();
                            }
                        }
                    }
                }

                // # — attribute or legacy comment
                Some('#') => {
                    self.advance();
                    if self.current() == Some('[') {
                        tokens.push(Token::new(
                            TokenKind::Hash,
                            Span::new(start, self.position(), self.file.clone()),
                                               "#",
                        ));
                    } else {
                        // Legacy # comment — skip to end of line
                        while self.current().map(|c| c != '\n').unwrap_or(false) {
                            self.advance();
                        }
                    }
                }

                // Newline
                Some('\n') => {
                    self.advance();
                    tokens.push(Token::new(
                        TokenKind::Newline,
                        Span::new(start.clone(), self.position(), self.file.clone()),
                                           "\n",
                    ));
                }

                // Raw string: r"..."
                Some('r') if self.peek(1) == Some('"') => {
                    self.advance(); // consume 'r'
                    match self.read_raw_string(start) {
                        Ok(t)  => tokens.push(t),
                        Err(e) => errors.push(e),
                    }
                }

                // Regular string
                Some('"') => {
                    self.advance();
                    match self.read_string(start) {
                        Ok(t)  => tokens.push(t),
                        Err(e) => errors.push(e),
                    }
                }

                // Directives ~ / ~~
                Some('~') => {
                    self.advance();
                    let is_fast = self.current() == Some('~');
                    if is_fast { self.advance(); }
                    self.skip_whitespace_no_newline();
                    if self.current() == Some('"') {
                        self.advance();
                        let s_start = self.position();
                        match self.read_string(s_start) {
                            Ok(t) => {
                                if let TokenKind::StringLit(s) = t.kind {
                                    let kind = if is_fast {
                                        TokenKind::FastDirective(s.clone())
                                    } else {
                                        TokenKind::Directive(s.clone())
                                    };
                                    tokens.push(Token::new(
                                        kind,
                                        Span::new(start, self.position(), self.file.clone()),
                                                           s,
                                    ));
                                }
                            }
                            Err(e) => errors.push(e),
                        }
                    }
                }

                // Numbers
                Some(c) if c.is_ascii_digit() => {
                    tokens.push(self.read_number(start));
                }

                // Identifiers / keywords
                Some(c) if c.is_alphabetic() || c == '_' => {
                    tokens.push(self.read_ident(start));
                }

                // Operators and punctuation
                Some('-') => {
                    self.advance();
                    if self.current() == Some('>') {
                        self.advance();
                        tokens.push(Token::new(TokenKind::Arrow, Span::new(start, self.position(), self.file.clone()), "->"));
                    } else if self.current() == Some('=') {
                        self.advance();
                        tokens.push(Token::new(TokenKind::MinusAssign, Span::new(start, self.position(), self.file.clone()), "-="));
                    } else {
                        tokens.push(Token::new(TokenKind::Minus, Span::new(start, self.position(), self.file.clone()), "-"));
                    }
                }
                Some('+') => {
                    self.advance();
                    if self.current() == Some('=') { self.advance(); tokens.push(Token::new(TokenKind::PlusAssign, Span::new(start, self.position(), self.file.clone()), "+=")); }
                    else { tokens.push(Token::new(TokenKind::Plus, Span::new(start, self.position(), self.file.clone()), "+")); }
                }
                Some('*') => {
                    self.advance();
                    if self.current() == Some('=') { self.advance(); tokens.push(Token::new(TokenKind::StarAssign, Span::new(start, self.position(), self.file.clone()), "*=")); }
                    else { tokens.push(Token::new(TokenKind::Star, Span::new(start, self.position(), self.file.clone()), "*")); }
                }
                Some('/') => {
                    self.advance();
                    if self.current() == Some('=') { self.advance(); tokens.push(Token::new(TokenKind::SlashAssign, Span::new(start, self.position(), self.file.clone()), "/=")); }
                    else { tokens.push(Token::new(TokenKind::Slash, Span::new(start, self.position(), self.file.clone()), "/")); }
                }
                Some('%') => { self.advance(); tokens.push(Token::new(TokenKind::Percent, Span::new(start, self.position(), self.file.clone()), "%")); }
                Some('=') => {
                    self.advance();
                    if self.current() == Some('=') { self.advance(); tokens.push(Token::new(TokenKind::Eq, Span::new(start, self.position(), self.file.clone()), "==")); }
                    else if self.current() == Some('>') { self.advance(); tokens.push(Token::new(TokenKind::FatArrow, Span::new(start, self.position(), self.file.clone()), "=>")); }
                    else { tokens.push(Token::new(TokenKind::Assign, Span::new(start, self.position(), self.file.clone()), "=")); }
                }
                Some('!') => {
                    self.advance();
                    if self.current() == Some('=') { self.advance(); tokens.push(Token::new(TokenKind::NotEq, Span::new(start, self.position(), self.file.clone()), "!=")); }
                    else { tokens.push(Token::new(TokenKind::Not, Span::new(start, self.position(), self.file.clone()), "!")); }
                }
                Some('<') => {
                    self.advance();
                    if self.current() == Some('=') { self.advance(); tokens.push(Token::new(TokenKind::LtEq, Span::new(start, self.position(), self.file.clone()), "<=")); }
                    else if self.current() == Some('<') { self.advance(); tokens.push(Token::new(TokenKind::Shl, Span::new(start, self.position(), self.file.clone()), "<<")); }
                    else { tokens.push(Token::new(TokenKind::Lt, Span::new(start, self.position(), self.file.clone()), "<")); }
                }
                Some('>') => {
                    self.advance();
                    if self.current() == Some('=') { self.advance(); tokens.push(Token::new(TokenKind::GtEq, Span::new(start, self.position(), self.file.clone()), ">=")); }
                    else if self.current() == Some('>') { self.advance(); tokens.push(Token::new(TokenKind::Shr, Span::new(start, self.position(), self.file.clone()), ">>")); }
                    else { tokens.push(Token::new(TokenKind::Gt, Span::new(start, self.position(), self.file.clone()), ">")); }
                }
                Some('&') => {
                    self.advance();
                    if self.current() == Some('&') { self.advance(); tokens.push(Token::new(TokenKind::And, Span::new(start, self.position(), self.file.clone()), "&&")); }
                    else { tokens.push(Token::new(TokenKind::BitAnd, Span::new(start, self.position(), self.file.clone()), "&")); }
                }
                Some('|') => {
                    self.advance();
                    if self.current() == Some('|') { self.advance(); tokens.push(Token::new(TokenKind::Or, Span::new(start, self.position(), self.file.clone()), "||")); }
                    else { tokens.push(Token::new(TokenKind::Pipe, Span::new(start, self.position(), self.file.clone()), "|")); }
                }
                Some('^') => { self.advance(); tokens.push(Token::new(TokenKind::BitXor, Span::new(start, self.position(), self.file.clone()), "^")); }
                Some('.') => {
                    self.advance();
                    if self.current() == Some('.') {
                        self.advance();
                        if self.current() == Some('=') { self.advance(); tokens.push(Token::new(TokenKind::DotDotEq, Span::new(start, self.position(), self.file.clone()), "..=")); }
                        else { tokens.push(Token::new(TokenKind::DotDot, Span::new(start, self.position(), self.file.clone()), "..")); }
                    } else {
                        tokens.push(Token::new(TokenKind::Dot, Span::new(start, self.position(), self.file.clone()), "."));
                    }
                }
                Some(':') => {
                    self.advance();
                    if self.current() == Some(':') { self.advance(); tokens.push(Token::new(TokenKind::ColonColon, Span::new(start, self.position(), self.file.clone()), "::")); }
                    else { tokens.push(Token::new(TokenKind::Colon, Span::new(start, self.position(), self.file.clone()), ":")); }
                }
                Some(';') => { self.advance(); tokens.push(Token::new(TokenKind::Semicolon, Span::new(start, self.position(), self.file.clone()), ";")); }
                Some(',') => { self.advance(); tokens.push(Token::new(TokenKind::Comma, Span::new(start, self.position(), self.file.clone()), ",")); }
                Some('?') => { self.advance(); tokens.push(Token::new(TokenKind::Question, Span::new(start, self.position(), self.file.clone()), "?")); }
                Some('@') => { self.advance(); tokens.push(Token::new(TokenKind::At, Span::new(start, self.position(), self.file.clone()), "@")); }
                Some('(') => { self.advance(); tokens.push(Token::new(TokenKind::LParen, Span::new(start, self.position(), self.file.clone()), "(")); }
                Some(')') => { self.advance(); tokens.push(Token::new(TokenKind::RParen, Span::new(start, self.position(), self.file.clone()), ")")); }
                Some('{') => { self.advance(); tokens.push(Token::new(TokenKind::LBrace, Span::new(start, self.position(), self.file.clone()), "{")); }
                Some('}') => { self.advance(); tokens.push(Token::new(TokenKind::RBrace, Span::new(start, self.position(), self.file.clone()), "}")); }
                Some('[') => { self.advance(); tokens.push(Token::new(TokenKind::LBracket, Span::new(start, self.position(), self.file.clone()), "[")); }
                Some(']') => { self.advance(); tokens.push(Token::new(TokenKind::RBracket, Span::new(start, self.position(), self.file.clone()), "]")); }

                // Any other character: if it's non-ASCII (like em-dash —, or UTF-8 continuation)
                // silently skip. This prevents false errors on Unicode in comments / identifiers.
                Some(c) => {
                    self.advance();
                    if c.is_ascii() {
                        // ASCII unknown character — report error
                        errors.push(ParseError::new(
                            ParseErrorKind::UnexpectedChar(c),
                                                    Span::new(start, self.position(), self.file.clone()),
                                                    format!("unexpected character `{}`", c),
                                                        vec!["remove or replace this character".to_string()],
                        ));
                    }
                    // Non-ASCII (Unicode) outside strings — silently skip
                    // (handles em-dashes in comments, Polish letters in identifiers, etc.)
                }
            }
        }

        if errors.is_empty() { Ok(tokens) } else { Err(errors) }
    }
}
