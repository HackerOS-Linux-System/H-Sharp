use crate::span::Span;
use serde::{Deserialize, Serialize};

// ─── Types ────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TypeExpr {
    Named(String),
    Generic(String, Vec<TypeExpr>),
    Array(Box<TypeExpr>),
    Slice(Box<TypeExpr>, Option<usize>),
    Tuple(Vec<TypeExpr>),
    Fn(Vec<TypeExpr>, Box<TypeExpr>),
    Optional(Box<TypeExpr>),
    Ref(Box<TypeExpr>),
    RefMut(Box<TypeExpr>),
    Void,
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
    F32, F64,
    Bool, String, Bytes,
}

// ─── Import paths ─────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ImportKind {
    /// use "std -> module -> sub" from "alias"
    Std { path: Vec<String>, alias: Option<String> },
    /// use "core -> runtime" from "alias"
    Core { path: Vec<String>, alias: Option<String> },
    /// use "vira -> pkgname" or "vira -> pkgname/1.2" from "alias"
    Vira { name: String, version: Option<String>, alias: Option<String> },
    /// use "github -> libname" from "alias"
    Github { name: String, alias: Option<String> },
    /// use "python -> numpy" from "np"
    Python { name: String, version: Option<String>, alias: Option<String> },
    /// use "bytes -> pkgname" from "alias"
    BytesRepo { name: String, version: Option<String>, alias: Option<String> },
    /// use "mod -> name" — deprecated, use `mod name` syntax
    #[allow(deprecated)]
    ModFile { path: String, alias: Option<String> },
}

// ─── Literals ─────────────────────────────────────────────────────────────────

#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum InterpPart {
    Text(String),
    Expr(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Literal {
    Int(i64),
    Float(f64),
    Bool(bool),
    String(String),
    Interpolated(Vec<InterpPart>),
    Nil,
    Bytes(Vec<u8>),
}

// ─── Patterns ─────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Pattern {
    Wildcard(Span),
    Ident(String, Span),
    Literal(Literal, Span),
    Tuple(Vec<Pattern>, Span),
    Struct { name: String, fields: Vec<(String, Pattern)>, span: Span },
    Enum { qualified_type: Option<String>, variant: String, inner: Vec<Pattern>, span: Span },
    Or(Vec<Pattern>, Span),
    Range(Box<Pattern>, Box<Pattern>, bool, Span),
}

// ─── Expressions ──────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Expr {
    Literal(Literal, Span),
    Ident(String, Span),
    BinOp(Box<Expr>, BinOp, Box<Expr>, Span),
    UnOp(UnOp, Box<Expr>, Span),
    Assign(Box<Expr>, Box<Expr>, Span),
    CompoundAssign(Box<Expr>, BinOp, Box<Expr>, Span),
    FieldAccess(Box<Expr>, String, Span),
    IndexAccess(Box<Expr>, Box<Expr>, Span),
    MethodCall(Box<Expr>, String, Vec<Expr>, Span),
    Call(Box<Expr>, Vec<Expr>, Span),
    If {
        condition:       Box<Expr>,
        then_body:       Vec<Stmt>,
        elsif_branches:  Vec<(Expr, Vec<Stmt>)>,
        else_body:       Option<Vec<Stmt>>,
            span:            Span,
    },
    Match {
        subject: Box<Expr>,
        arms:    Vec<MatchArm>,
        span:    Span,
    },
    While {
        condition: Box<Expr>,
        body:      Vec<Stmt>,
        span:      Span,
    },
    For {
        pattern:  Pattern,
        iterable: Box<Expr>,
        body:     Vec<Stmt>,
        span:     Span,
    },
    Do {
        body: Vec<Stmt>,
        span: Span,
    },
    StructLit(String, Vec<(String, Expr)>, Span),
    ArrayLit(Vec<Expr>, Span),
    TupleLit(Vec<Expr>, Span),
    Closure {
        params:      Vec<Param>,
        return_type: Option<TypeExpr>,
        body:        Vec<Stmt>,
        span:        Span,
    },
    Cast(Box<Expr>, TypeExpr, Span),
    Range(Box<Expr>, Box<Expr>, bool, Span),
    Unsafe(Vec<Stmt>, Option<ArenaConfig>, Span),
    Return(Option<Box<Expr>>, Span),
    SelfExpr(Span),
    Try(Box<Expr>, Span),
    Await(Box<Expr>, Span),
    /// Module path access: `module::function` or `module::CONST`.
    /// Segments are the dotted/coloned path components (e.g. ["json", "parse"]).
    Path(Vec<String>, Span),
}

impl Expr {
    pub fn span(&self) -> &Span {
        match self {
            Expr::Literal(_, s)                => s,
            Expr::Ident(_, s)                  => s,
            Expr::BinOp(_, _, _, s)            => s,
            Expr::UnOp(_, _, s)                => s,
            Expr::Assign(_, _, s)              => s,
            Expr::CompoundAssign(_, _, _, s)   => s,
            Expr::FieldAccess(_, _, s)         => s,
            Expr::IndexAccess(_, _, s)         => s,
            Expr::MethodCall(_, _, _, s)       => s,
            Expr::Call(_, _, s)                => s,
            Expr::If { span, .. }              => span,
            Expr::Match { span, .. }           => span,
            Expr::While { span, .. }           => span,
            Expr::For { span, .. }             => span,
            Expr::Do { span, .. }              => span,
            Expr::StructLit(_, _, s)           => s,
            Expr::ArrayLit(_, s)               => s,
            Expr::TupleLit(_, s)               => s,
            Expr::Closure { span, .. }         => span,
            Expr::Cast(_, _, s)                => s,
            Expr::Range(_, _, _, s)            => s,
            Expr::Unsafe(_, _, s)              => s,
            Expr::Return(_, s)                 => s,
            Expr::SelfExpr(s)                  => s,
            Expr::Try(_, s)                    => s,
            Expr::Await(_, s)                  => s,
            Expr::Path(_, s)                   => s,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum BinOp {
    Add, Sub, Mul, Div, Mod,
    Eq, NotEq, Lt, Gt, LtEq, GtEq,
    And, Or,
    BitAnd, BitOr, BitXor, Shl, Shr,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum UnOp {
    Neg, Not, BitNot, Ref, RefMut, Deref,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard:   Option<Expr>,
    pub body:    Vec<Stmt>,
    pub span:    Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ArenaKind { General, Fixed, Pool, Page, Ring }

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ManualKind { Modern, Classic }

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum UnsafeMode {
    Arena { kind: ArenaKind, size: Option<usize> },
    Manual(ManualKind),
    Raw,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ArenaConfig {
    pub mode: UnsafeMode,
}

// ─── Statements ───────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Stmt {
    Let {
        name:    String,
        ty:      Option<TypeExpr>,
        mutable: bool,
        value:   Option<Expr>,
        span:    Span,
    },
    Expr(Expr, Span),
    Return(Option<Expr>, Span),
    Import(ImportKind, Option<String>, Span),
    Break(Option<Expr>, Span),
    Continue(Span),
    Item(Item),
}

// ─── Items ────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Item {
    FnDef(FnDef),
    StructDef(StructDef),
    EnumDef(EnumDef),
    TraitDef(TraitDef),
    ImplBlock(ImplBlock),
    TypeAlias { name: String, ty: TypeExpr, pub_: bool, span: Span },
    Extern(ExternBlock),
    ModDecl {
        name:   String,
        pub_:   bool,
        inline: Option<Vec<Item>>,
        span:   Span,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypeParam {
    pub name:   String,
    pub bounds: Vec<String>,
    pub span:   Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Attribute {
    pub name: String,
    pub args: Vec<AttrArg>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum AttrArg {
    Ident(String),
    KeyValue(String, String),
    Lit(String),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FnDef {
    pub attrs:       Vec<Attribute>,
    pub type_params: Vec<TypeParam>,
    pub name:        String,
    pub params:      Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub body:        Vec<Stmt>,
    pub pub_:        bool,
    pub is_unsafe:   bool,
    pub is_async:    bool,
    pub span:        Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Param {
    pub name:    String,
    pub ty:      TypeExpr,
    pub mutable: bool,
    pub span:    Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StructDef {
    pub attrs:       Vec<Attribute>,
    pub type_params: Vec<TypeParam>,
    pub name:        String,
    pub fields:      Vec<StructField>,
    pub pub_:        bool,
    pub span:        Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StructField {
    pub name: String,
    pub ty:   TypeExpr,
    pub pub_: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EnumDef {
    pub attrs:       Vec<Attribute>,
    pub type_params: Vec<TypeParam>,
    pub name:        String,
    pub variants:    Vec<EnumVariant>,
    pub pub_:        bool,
    pub span:        Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EnumVariant {
    pub name:   String,
    pub fields: EnumVariantFields,
    pub span:   Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum EnumVariantFields {
    Unit,
    Tuple(Vec<TypeExpr>),
    Struct(Vec<StructField>),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TraitDef {
    pub attrs:       Vec<Attribute>,
    pub type_params: Vec<TypeParam>,
    pub name:        String,
    pub methods:     Vec<TraitMethod>,
    pub pub_:        bool,
    pub span:        Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TraitMethod {
    pub name:         String,
    pub params:       Vec<Param>,
    pub return_type:  Option<TypeExpr>,
    pub default_body: Option<Vec<Stmt>>,
    pub span:         Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ImplBlock {
    pub type_name:  String,
    pub trait_name: Option<String>,
    pub methods:    Vec<FnDef>,
    pub span:       Span,
}

// ─── Module ───────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Directive {
    pub kind:  DirectiveKind,
    pub value: String,
    pub span:  Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum DirectiveKind {
    Dynamic,
    Fast,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Module {
    pub file:       String,
    pub edition:    Option<String>,
    pub directives: Vec<Directive>,
    pub items:      Vec<Item>,
    pub imports:    Vec<(ImportKind, Option<String>, Span)>,
}

// ─── Extern ───────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExternBlock {
    pub lang:      ExternLang,
    pub link_kind: ExternLinkKind,
    pub library:   Option<String>,
    pub functions: Vec<ExternFnDecl>,
    pub span:      Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ExternLang {
    C,
    Rust,
    Cpp,
    /// extern [python, "numpy"] is ... end
    /// Functions declared here are called via an embedded/subprocess
    /// CPython bridge (see hsh_py_eval / hsh_py_call in the runtime).
    /// Replaces the older `use "python -> numpy" from "np"` form, which
    /// only installed the pip package but had no defined call ABI.
    Python,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ExternLinkKind { Static, Dynamic }

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExternFnDecl {
    pub name:        String,
    pub params:      Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub variadic:    bool,
    pub span:        Span,
}
