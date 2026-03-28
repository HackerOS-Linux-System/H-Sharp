use serde::{Deserialize, Serialize};
use std::fmt;

/// Zakres w pliku źródłowym
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Default)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: u32,
    pub col: u32,
}

impl Span {
    pub fn new(start: usize, end: usize, line: u32, col: u32) -> Self {
        Self { start, end, line, col }
    }

    pub fn dummy() -> Self {
        Self::default()
    }
}

/// Typ H# (statyczne typowanie)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Ty {
    Int,
    Float,
    Bool,
    Str,
    Char,
    Void,
    /// List[T]
    List(Box<Ty>),
    /// Map[K, V]
    Map(Box<Ty>, Box<Ty>),
    /// Option[T]
    Option(Box<Ty>),
    /// Result[T, E]
    Result(Box<Ty>, Box<Ty>),
    /// Arc[T] - bezpieczny ARC jak w Rust
    Arc(Box<Ty>),
    /// Box[T]
    Box(Box<Ty>),
    /// Typ użytkownika (Claas/enum itp.)
    Named(String),
    /// Generyk: Foo[T, U]
    Generic(String, Vec<Ty>),
    /// Funkcja: fn(A, B) -> C
    Fn(Vec<Ty>, Box<Ty>),
    /// Inferencja typu
    Infer,
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Int => write!(f, "Int"),
            Ty::Float => write!(f, "Float"),
            Ty::Bool => write!(f, "Bool"),
            Ty::Str => write!(f, "Str"),
            Ty::Char => write!(f, "Char"),
            Ty::Void => write!(f, "Void"),
            Ty::List(t) => write!(f, "List[{}]", t),
            Ty::Map(k, v) => write!(f, "Map[{}, {}]", k, v),
            Ty::Option(t) => write!(f, "Option[{}]", t),
            Ty::Result(t, e) => write!(f, "Result[{}, {}]", t, e),
            Ty::Arc(t) => write!(f, "Arc[{}]", t),
            Ty::Box(t) => write!(f, "Box[{}]", t),
            Ty::Named(n) => write!(f, "{}", n),
            Ty::Generic(n, args) => {
                write!(f, "{}[", n)?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", a)?;
                }
                write!(f, "]")
            }
            Ty::Fn(params, ret) => {
                write!(f, "fn(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", p)?;
                }
                write!(f, ") -> {}", ret)
            }
            Ty::Infer => write!(f, "_"),
        }
    }
}

/// Widoczność elementu
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Vis {
    Public,
    Private,
}

/// Parametr funkcji
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Param {
    pub name: String,
    pub ty: Ty,
    pub mutable: bool,
    pub default: Option<Box<Expr>>,
    pub span: Span,
}

/// Deklaracja importu:  # <bytes/lib_name//version:1.0>
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ImportDecl {
    pub source: ImportSource,
    pub name: String,
    pub version: Option<String>,
    pub alias: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ImportSource {
    /// Ekosystem Bytes (pobierany z internetu)
    Bytes,
    /// Biblioteka core z /usr/lib/HackerOS/H#/
    Core,
}

/// Atrybut:  *{derive(Debug)}
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Attribute {
    pub content: String,
    pub span: Span,
}

/// Pole klasy
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Field {
    pub name: String,
    pub ty: Ty,
    pub mutable: bool,
    pub vis: Vis,
    pub default: Option<Box<Expr>>,
    pub attrs: Vec<Attribute>,
    pub span: Span,
}

/// Element traitowy
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TraitItem {
    pub name: String,
    pub params: Vec<Param>,
    pub return_ty: Ty,
    pub default_body: Option<Vec<Stmt>>,
    pub attrs: Vec<Attribute>,
    pub span: Span,
}

/// Wariant enum
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EnumVariant {
    pub name: String,
    pub fields: Vec<Ty>,
    pub span: Span,
}

/// Deklaracja najwyższego poziomu
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Decl {
    /// Import:  # <bytes/std_io>
    Import(ImportDecl),

    /// Funkcja:  fn nazwa(params) -> Ty [ ciało ]
    Function {
        vis: Vis,
        attrs: Vec<Attribute>,
        name: String,
        generics: Vec<String>,
        params: Vec<Param>,
        return_ty: Ty,
        body: Vec<Stmt>,
        span: Span,
    },

    /// Klasa:  Claas Nazwa [ pola i metody ]
    Class {
        vis: Vis,
        attrs: Vec<Attribute>,
        name: String,
        generics: Vec<String>,
        fields: Vec<Field>,
        methods: Vec<Decl>,
        traits_impl: Vec<String>,
        span: Span,
    },

    /// Enum:  enum Nazwa [ warianty ]
    Enum {
        vis: Vis,
        attrs: Vec<Attribute>,
        name: String,
        generics: Vec<String>,
        variants: Vec<EnumVariant>,
        span: Span,
    },

    /// Trait:  trait Nazwa [ elementy ]
    Trait {
        vis: Vis,
        name: String,
        items: Vec<TraitItem>,
        span: Span,
    },

    /// Implementacja:  impl NazwaTraitu dla NazwaKlasy [ ... ]
    Impl {
        trait_name: Option<String>,
        target: String,
        items: Vec<Decl>,
        span: Span,
    },

    /// Stała:  const NAZWA: Ty = wartość
    Const {
        vis: Vis,
        name: String,
        ty: Ty,
        value: Box<Expr>,
        span: Span,
    },

    /// Alias:  type Nowy = Stary
    TypeAlias {
        vis: Vis,
        name: String,
        ty: Ty,
        span: Span,
    },

    /// Sekcja skryptowa
    ScriptSection(ScriptSection),
}

/// ─────────────────────────────────────────────────────────────────────────
/// Sekcja skryptowa  ---  ... ---
/// ─────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ScriptSection {
    pub commands: Vec<ScriptCmd>,
    pub span: Span,
}

/// Komenda w sekcji skryptowej
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ScriptCmd {
    /// > komenda  (zwykła komenda w środowisku)
    Shell {
        cmd: String,
        args: Vec<ScriptArg>,
        span: Span,
    },
    /// >>> komenda  (izolowane środowisko)
    Isolated {
        cmd: String,
        args: Vec<ScriptArg>,
        span: Span,
    },
    /// >> komenda ze zmiennymi
    WithVars {
        cmd: String,
        args: Vec<ScriptArg>,
        env: Vec<(String, ScriptArg)>,
        span: Span,
    },
    /// deps [pkg1, pkg2, ...]  - sprawdza i instaluje zależności
    Deps {
        packages: Vec<String>,
        span: Span,
    },
    /// Przypisanie zmiennej w sekcji skryptowej: let x = "wartość"
    Let {
        name: String,
        value: ScriptArg,
        span: Span,
    },
    /// if / else w sekcji skryptowej
    If {
        cond: Box<ScriptCmd>,
        then: Vec<ScriptCmd>,
        otherwise: Vec<ScriptCmd>,
        span: Span,
    },
    /// for w sekcji skryptowej
    For {
        var: String,
        iterable: ScriptArg,
        body: Vec<ScriptCmd>,
        span: Span,
    },
    /// pipe: cmd1 | cmd2 | cmd3
    Pipe {
        steps: Vec<ScriptCmd>,
        span: Span,
    },
    /// Komentarz (dziedziczony z H#:  !)
    Comment(String),
}

/// Argument w sekcji skryptowej
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ScriptArg {
    Literal(String),
    Var(String),
    EnvVar(String),
    Subshell(Vec<ScriptCmd>),
    Interpolated(Vec<ScriptArgPart>),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ScriptArgPart {
    Literal(String),
    Var(String),
}

/// ─────────────────────────────────────────────────────────────────────────
/// Wyrażenia
/// ─────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Expr {
    // Literały
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Char(char),
    Nil,

    // Zmienna
    Var(String),

    // Operacje
    BinOp {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        span: Span,
    },
    UnaryOp {
        op: UnaryOp,
        expr: Box<Expr>,
        span: Span,
    },

    // Wywołanie funkcji/metody
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
        span: Span,
    },
    MethodCall {
        object: Box<Expr>,
        method: String,
        args: Vec<Expr>,
        span: Span,
    },

    // Dostęp do pola
    FieldAccess {
        object: Box<Expr>,
        field: String,
        span: Span,
    },
    IndexAccess {
        object: Box<Expr>,
        index: Box<Expr>,
        span: Span,
    },

    // Tworzenie instancji klasy
    New {
        class: String,
        args: Vec<(Option<String>, Expr)>,
        span: Span,
    },

    // Kolekcje
    List(Vec<Expr>),
    Map(Vec<(Expr, Expr)>),

    // Blok wyrażeń (zwraca ostatnią wartość)
    Block(Vec<Stmt>),

    // If jako wyrażenie
    If {
        cond: Box<Expr>,
        then: Box<Expr>,
        elsif: Vec<(Expr, Expr)>,
        otherwise: Option<Box<Expr>>,
        span: Span,
    },

    // Match jako wyrażenie
    Match {
        value: Box<Expr>,
        arms: Vec<MatchArm>,
        span: Span,
    },

    // Domknięcie (lambda)
    Closure {
        params: Vec<Param>,
        return_ty: Option<Ty>,
        body: Box<Expr>,
        span: Span,
    },

    // Zakres (range)
    Range {
        from: Box<Expr>,
        to: Box<Expr>,
        inclusive: bool,
        span: Span,
    },

    // Arc::new(x)  - jawne opakowanie w Arc
    ArcNew(Box<Expr>),

    // Arena alloc: :: nazwa [size] [ body ]
    ArenaBlock {
        name: String,
        size: Box<Expr>,
        body: Vec<Stmt>,
        span: Span,
    },

    // write "tekst" lub write wartość
    Write {
        args: Vec<Expr>,
        newline: bool,
        span: Span,
    },

    // self
    SelfExpr,

    // Typa cast:  x as Int
    Cast {
        expr: Box<Expr>,
        ty: Ty,
        span: Span,
    },

    // is typecheck:  x is Str
    TypeCheck {
        expr: Box<Expr>,
        ty: Ty,
        span: Span,
    },

    // Operator ?  (early return on error)
    Try(Box<Expr>),
}

/// Ramię dopasowania (match arm)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub span: Span,
}

/// Wzorzec dopasowania
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Pattern {
    Wildcard,
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Nil,
    Var(String),
    Tuple(Vec<Pattern>),
    List(Vec<Pattern>),
    Enum {
        name: String,
        variant: String,
        fields: Vec<Pattern>,
    },
    Or(Vec<Pattern>),
    Range {
        from: Box<Pattern>,
        to: Box<Pattern>,
        inclusive: bool,
    },
}

/// Operatory binarne
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum BinOp {
    Add, Sub, Mul, Div, Mod, Pow,
    Eq, NotEq, Lt, Gt, LtEq, GtEq,
    And, Or,
    BitAnd, BitOr, BitXor,
    LShift, RShift,
    Assign,
    AddAssign, SubAssign, MulAssign, DivAssign,
}

/// Operatory jednoargumentowe
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum UnaryOp {
    Neg,
    Not,
    BitNot,
}

/// ─────────────────────────────────────────────────────────────────────────
/// Instrukcje (Statements)
/// ─────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Stmt {
    /// let [mut] nazwa: Ty = wartość
    Let {
        name: String,
        ty: Option<Ty>,
        mutable: bool,
        value: Option<Box<Expr>>,
        span: Span,
    },

    /// Wyrażenie jako instrukcja
    Expr(Expr),

    /// return wartość
    Return(Option<Box<Expr>>),

    /// break
    Break(Option<Box<Expr>>),

    /// next (continue)
    Next,

    /// raise wyjatek
    Raise(Box<Expr>),

    /// while cond [ body ]
    While {
        cond: Box<Expr>,
        body: Vec<Stmt>,
        span: Span,
    },

    /// for var in iterable [ body ]
    For {
        var: String,
        iterable: Box<Expr>,
        body: Vec<Stmt>,
        span: Span,
    },

    /// rescue/ensure - obsługa błędów
    Rescue {
        body: Vec<Stmt>,
        handlers: Vec<RescueHandler>,
        ensure: Vec<Stmt>,
        span: Span,
    },

    /// Przypisanie:  x = 5
    Assign {
        target: Box<Expr>,
        value: Box<Expr>,
        span: Span,
    },
}

/// Obsługa błędów: rescue ErrorType => e [ ... ]
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RescueHandler {
    pub error_type: Option<String>,
    pub binding: Option<String>,
    pub body: Vec<Stmt>,
    pub span: Span,
}

/// Kompletny plik H# / moduł
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Module {
    pub name: String,
    pub decls: Vec<Decl>,
    pub source: String,
}

impl Module {
    pub fn new(name: impl Into<String>, source: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            decls: Vec::new(),
            source: source.into(),
        }
    }
}
