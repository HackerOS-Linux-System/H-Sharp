use logos::Logos;
use std::fmt;

/// Callback do ręcznego parsowania komentarzy blokowych !== ... ==!
/// logos nie obsługuje non-greedy ani złożonych zagnieżdżeń -
/// robimy to ręcznie w funkcji post-process.
fn lex_block_comment(lex: &mut logos::Lexer<Token>) -> Option<String> {
    let remainder = lex.remainder();
    // Szukamy ==! który kończy komentarz
    if let Some(end) = remainder.find("==!") {
        let content = &remainder[..end + 3]; // włącznie z ==!
        lex.bump(end + 3);
        Some(format!("!=={}", content))
    } else {
        // Brak zamknięcia - konsumujemy do końca
        let len = remainder.len();
        lex.bump(len);
        Some(format!("!=={}", remainder))
    }
}

#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(skip r"[ \t\r]+")]
pub enum Token {

    // ── Komentarze ─────────────────────────────────────────────────────────
    // WAŻNA KOLEJNOŚĆ: bardziej specyficzne tokeny PRZED ogólnymi

    /// Wielolinijkowy komentarz !== ... ==!
    /// Parsowany ręcznie żeby uniknąć crash logos_derive
    #[token("!==", lex_block_comment)]
    BlockComment(String),

    /// Komentarz dokumentacyjny !! (przed zwykłym !)
    #[regex(r"!![^\n]*", |lex| lex.slice()[2..].trim().to_owned())]
    DocComment(String),

    /// Zwykły komentarz ! (priority wyższy niż Bang)
    #[regex(r"![^=!\n][^\n]*", priority = 3, callback = |lex| lex.slice().to_owned())]
    Comment(String),

    /// Samotny ! (bez tekstu po nim, np. na końcu linii)
    #[regex(r"![^\n]*", priority = 2, callback = |lex| lex.slice().to_owned())]
    CommentBang(String),

    // ── Atrybuty *{ ... } ──────────────────────────────────────────────────
    #[regex(r"\*\{[^}]*\}", |lex| lex.slice().to_owned())]
    Attribute(String),

    // ── String literals ────────────────────────────────────────────────────
    #[regex(r#""([^"\\]|\\.)*""#, |lex| {
    let s = lex.slice();
    s[1..s.len()-1].to_owned()
    })]
    StringLit(String),

    #[regex(r"'[^'\\]'|'\\.'", |lex| {
    let s = lex.slice();
    let inner = &s[1..s.len()-1];
    if inner.starts_with('\\') {
        match inner.chars().nth(1).unwrap_or('\0') {
            'n'  => '\n',
            't'  => '\t',
            'r'  => '\r',
            '\\' => '\\',
            '\'' => '\'',
            '0'  => '\0',
            c    => c,
        }
    } else {
        inner.chars().next().unwrap_or('\0')
    }
    })]
    CharLit(char),

    // Float PRZED Int żeby "3.14" nie było parsowane jako Int(3) + Dot + Int(14)
    #[regex(r"[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?", |lex| {
    lex.slice().parse::<f64>().unwrap_or(0.0)
    })]
    FloatLit(f64),

    #[regex(r"[0-9]+", |lex| lex.slice().parse::<i64>().unwrap_or(0))]
    IntLit(i64),

    // Ujemne liczby obsługujemy przez UnaryOp::Neg w parserze

    #[token("true")]
    True,

    #[token("false")]
    False,

    #[token("nil")]
    Nil,

    // ── Słowa kluczowe (przed Ident!) ──────────────────────────────────────
    #[token("fn")]      Fn,
    #[token("Claas")]   Class,
    #[token("write")]   Write,
    #[token("return")]  Return,
    #[token("let")]     Let,
    #[token("mut")]     Mut,
    #[token("const")]   Const,
    #[token("if")]      If,
    #[token("else")]    Else,
    #[token("elsif")]   Elsif,
    #[token("while")]   While,
    #[token("for")]     For,
    #[token("in")]      In,
    #[token("match")]   Match,
    #[token("pub")]     Pub,
    #[token("self")]    SelfKw,
    #[token("super")]   Super,
    #[token("new")]     New,
    #[token("and")]     And,
    #[token("or")]      Or,
    #[token("not")]     Not,
    #[token("break")]   Break,
    #[token("next")]    Next,
    #[token("raise")]   Raise,
    #[token("rescue")]  Rescue,
    #[token("ensure")]  Ensure,
    #[token("trait")]   Trait,
    #[token("impl")]    Impl,
    #[token("enum")]    Enum,
    #[token("type")]    Type,
    #[token("where")]   Where,
    #[token("as")]      As,
    #[token("is")]      Is,
    #[token("do")]      Do,
    #[token("end")]     End,
    #[token("yield")]   Yield,
    #[token("when")]    When,
    #[token("import")]  Import,

    // Typy wbudowane
    #[token("Int")]    TyInt,
    #[token("Float")]  TyFloat,
    #[token("Bool")]   TyBool,
    #[token("Str")]    TyStr,
    #[token("Char")]   TyChar,
    #[token("Void")]   TyVoid,
    #[token("List")]   TyList,
    #[token("Map")]    TyMap,
    #[token("Option")] TyOption,
    #[token("Result")] TyResult,
    #[token("Arc")]    TyArc,
    #[token("Box")]    TyBox,

    // ── Arena allocator :: ─────────────────────────────────────────────────
    #[token("::")]  DoubleColon,

    // ── Import # ───────────────────────────────────────────────────────────
    #[token("#")]   Hash,

    // ── Sekcja skryptowa --- ───────────────────────────────────────────────
    #[token("---")] ScriptOpen,

    // ── Operatory (dłuższe PRZED krótszymi!) ──────────────────────────────
    #[token("..=")] DotDotEq,
    #[token("...")]  DotDotDot,
    #[token("..")]  DotDot,
    #[token("->")]  Arrow,
    #[token("=>")]  FatArrow,
    #[token("==")]  EqEq,
    #[token("!=")]  NotEq,
    #[token("<=")]  LtEq,
    #[token(">=")]  GtEq,
    #[token("+=")]  PlusEq,
    #[token("-=")]  MinusEq,
    #[token("*=")]  StarEq,
    #[token("/=")]  SlashEq,
    #[token("**")]  StarStar,
    #[token("&&")]  AndAnd,
    #[token("||")]  OrOr,
    #[token("<<")]  LShift,
    #[token(">>")]  RShift,
    #[token("<")]   Lt,
    #[token(">")]   Gt,
    #[token("=")]   Eq,
    #[token("+")]   Plus,
    #[token("-")]   Minus,
    #[token("*")]   Star,
    #[token("/")]   Slash,
    #[token("%")]   Percent,
    #[token("&")]   Amp,
    #[token("|")]   Pipe,
    #[token("^")]   Caret,
    #[token("~")]   Tilde,
    #[token("?")]   Question,
    #[token("@")]   At,
    #[token("$")]   Dollar,

    // ── Delimitery ─────────────────────────────────────────────────────────
    #[token("[")] LBracket,
    #[token("]")] RBracket,
    #[token("(")] LParen,
    #[token(")")] RParen,
    #[token("{")] LBrace,
    #[token("}")] RBrace,
    #[token(",")] Comma,
    #[token(";")] Semicolon,
    #[token(":")] Colon,
    #[token(".")] Dot,

    #[token("\n")] Newline,

    // ── Identyfikatory (na końcu!) ─────────────────────────────────────────
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*[?!]?", |lex| lex.slice().to_owned())]
    Ident(String),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Ident(s)        => write!(f, "{}", s),
            Token::StringLit(s)    => write!(f, "\"{}\"", s),
            Token::IntLit(n)       => write!(f, "{}", n),
            Token::FloatLit(n)     => write!(f, "{}", n),
            Token::CharLit(c)      => write!(f, "'{}'", c),
            Token::DocComment(s)   => write!(f, "!! {}", s),
            Token::Comment(s)      => write!(f, "{}", s),
            Token::BlockComment(s) => write!(f, "{}", s),
            Token::Attribute(s)    => write!(f, "{}", s),
            _                      => write!(f, "{:?}", self),
        }
    }
}

// ─── Spanned token ────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct Spanned<T> {
    pub inner: T,
    pub span:  std::ops::Range<usize>,
}

impl<T> Spanned<T> {
    pub fn new(inner: T, span: std::ops::Range<usize>) -> Self {
        Self { inner, span }
    }
}

// ─── Błąd leksowania ─────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct LexError {
    pub span:    std::ops::Range<usize>,
    pub message: String,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Błąd leksowania w {:?}: {}", self.span, self.message)
    }
}

// ─── Publiczne API ────────────────────────────────────────────────────────────

/// Leksuje kod źródłowy H#.
/// Komentarze (poza Doc) są pomijane w strumieniu wynikowym.
pub fn lex(source: &str) -> Result<Vec<Spanned<Token>>, Vec<LexError>> {
    let mut tokens = Vec::new();
    let mut errors  = Vec::new();

    for (result, span) in Token::lexer(source).spanned() {
        match result {
            Ok(tok) => {
                match &tok {
                    // Pomijamy komentarze - nie trafiają do parsera
                    Token::Comment(_)
                    | Token::CommentBang(_)
                    | Token::BlockComment(_) => {}
                    // DocComment zachowujemy (może być użyty do generowania docs)
                    _ => tokens.push(Spanned::new(tok, span)),
                }
            }
            Err(_) => {
                let text = source
                .get(span.clone())
                .unwrap_or("?")
                .to_owned();
                errors.push(LexError {
                    span,
                    message: format!("Nierozpoznany znak: `{}`", text),
                });
            }
        }
    }

    if errors.is_empty() { Ok(tokens) } else { Err(errors) }
}

// ─── Testy ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fn_write() {
        let src = "fn hello [\n    write \"Hello H#\"\n]";
        let toks = lex(src).expect("lex failed");
        assert!(toks.iter().any(|t| t.inner == Token::Fn));
        assert!(toks.iter().any(|t| t.inner == Token::Write));
    }

    #[test]
    fn test_komentarz_pomijany() {
        let src = "! to jest komentarz\nfn foo []";
        let toks = lex(src).expect("lex failed");
        assert!(!toks.iter().any(|t| matches!(&t.inner, Token::Comment(_))));
        assert!(toks.iter().any(|t| t.inner == Token::Fn));
    }

    #[test]
    fn test_doc_comment() {
        let src = "!! Dokumentacja\nfn bar []";
        let toks = lex(src).expect("lex failed");
        assert!(toks.iter().any(|t| matches!(&t.inner, Token::DocComment(_))));
    }

    #[test]
    fn test_liczby() {
        let src = "42 3.14 0";
        let toks = lex(src).expect("lex failed");
        assert!(toks.iter().any(|t| t.inner == Token::IntLit(42)));
        assert!(toks.iter().any(|t| matches!(&t.inner, Token::FloatLit(f) if (*f - 3.14).abs() < 0.001)));
    }

    #[test]
    fn test_string() {
        let src = r#""Cześć świecie""#;
        let toks = lex(src).expect("lex failed");
        assert!(toks.iter().any(|t| matches!(&t.inner, Token::StringLit(s) if s == "Cześć świecie")));
    }

    #[test]
    fn test_operator_kolejnosc() {
        // ** musi być przed *
        let src = "2 ** 8";
        let toks = lex(src).expect("lex failed");
        assert!(toks.iter().any(|t| t.inner == Token::StarStar));
        assert!(!toks.iter().any(|t| t.inner == Token::Star));
    }

    #[test]
    fn test_atrybut() {
        let src = "*{derive(Debug)}";
        let toks = lex(src).expect("lex failed");
        assert!(toks.iter().any(|t| matches!(&t.inner, Token::Attribute(_))));
    }

    #[test]
    fn test_script_open() {
        let src = "---\n> echo test\n---";
        let toks = lex(src).expect("lex failed");
        assert!(toks.iter().any(|t| t.inner == Token::ScriptOpen));
    }
}
