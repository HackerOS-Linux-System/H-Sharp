use crate::span::Span;
use serde::{Deserialize, Serialize};

// ─── Types ────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TypeExpr {
    Named(String),
    Generic(String, Vec<TypeExpr>),  // Vec<T>, Map<K, V>
    Array(Box<TypeExpr>),             // [T]
    Slice(Box<TypeExpr>, Option<usize>),
    Tuple(Vec<TypeExpr>),
    Fn(Vec<TypeExpr>, Box<TypeExpr>),
    Optional(Box<TypeExpr>),          // T?
    Ref(Box<TypeExpr>),               // &T
    RefMut(Box<TypeExpr>),            // &mut T
    Void,
    // Explicit numeric aliases (sugar for Named but typed directly)
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
    F32, F64,
    Bool, String, Bytes,
}

// ─── Import paths ─────────────────────────────────────────────────────────────

/// Import path parsed from: use "std -> time -> clock" from "alias"
/// or: use "github.com/user/repo" from "alias"
/// or: use "vira -> pkgname/1.0" from "alias"
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ImportKind {
    /// use "std -> module -> sub" from "alias"
    /// File lives at /usr/lib/HackerOS/H#/std/<module>.h#
    Std { path: Vec<String>, alias: Option<String> },
    /// use "core -> runtime" from "alias"
    /// Built-in — always available, no file on disk needed
    Core { path: Vec<String>, alias: Option<String> },
    /// use "vira -> pkgname" or "vira -> pkgname/1.2" from "alias"
    /// Package declared in vira.hk [dependencies]
    Vira { name: String, version: Option<String>, alias: Option<String> },
    /// use "github -> libname" from "alias"
    /// Library details (URL, version) declared in vira.hk or bytes.hk [github] section
    Github { name: String, alias: Option<String> },
    /// use "python -> numpy" from "np"
    /// Python package — installed via pip, bridged through bytes JIT
    Python { name: String, version: Option<String>, alias: Option<String> },
    /// use "bytes -> pkgname" from "alias"
    /// Package from Bytes-Repository, declared in bytes.hk
    BytesRepo { name: String, version: Option<String>, alias: Option<String> },
    /// use "mod -> name" from "alias" — explicit module file import (use mod instead)
    /// Deprecated: use `mod name` syntax instead
    #[deprecated]
    ModFile { path: String, alias: Option<String> },
}

// ─── Literals ─────────────────────────────────────────────────────────────────

/// Part of an interpolated string literal
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
    /// Interpolated string: "Hello ${name}!" 
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
    Enum { variant: String, inner: Option<Box<Pattern>>, span: Span },
    Or(Vec<Pattern>, Span),
    Range(Box<Pattern>, Box<Pattern>, bool, Span), // bool = inclusive
}

// ─── Expressions ──────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Expr {
    Literal(Literal, Span),
    Ident(String, Span),

    // Operations
    BinOp(Box<Expr>, BinOp, Box<Expr>, Span),
    UnOp(UnOp, Box<Expr>, Span),

    // Assignment
    Assign(Box<Expr>, Box<Expr>, Span),
    CompoundAssign(Box<Expr>, BinOp, Box<Expr>, Span),

    // Access
    FieldAccess(Box<Expr>, String, Span),
    IndexAccess(Box<Expr>, Box<Expr>, Span),
    MethodCall(Box<Expr>, String, Vec<Expr>, Span),

    // Call
    Call(Box<Expr>, Vec<Expr>, Span),

    // Control flow
    If {
        condition: Box<Expr>,
        then_body: Vec<Stmt>,
        elsif_branches: Vec<(Expr, Vec<Stmt>)>,
        else_body: Option<Vec<Stmt>>,
        span: Span,
    },
    Match {
        subject: Box<Expr>,
        arms: Vec<MatchArm>,
        span: Span,
    },
    While {
        condition: Box<Expr>,
        body: Vec<Stmt>,
        span: Span,
    },
    For {
        pattern: Pattern,
        iterable: Box<Expr>,
        body: Vec<Stmt>,
        span: Span,
    },
    Do {
        body: Vec<Stmt>,
        span: Span,
    },

    // Struct/array/tuple constructors
    StructLit(String, Vec<(String, Expr)>, Span),
    ArrayLit(Vec<Expr>, Span),
    TupleLit(Vec<Expr>, Span),

    // Closures
    Closure {
        params: Vec<Param>,
        return_type: Option<TypeExpr>,
        body: Vec<Stmt>,
        span: Span,
    },

    // Type cast
    Cast(Box<Expr>, TypeExpr, Span),

    // Range
    Range(Box<Expr>, Box<Expr>, bool, Span), // bool = inclusive

    // Unsafe block with optional arena
    Unsafe(Vec<Stmt>, Option<ArenaConfig>, Span),

    // Return expression
    Return(Option<Box<Expr>>, Span),

    // Self
    SelfExpr(Span),

    // Question mark operator
    Try(Box<Expr>, Span),
    Await(Box<Expr>, Span),
}

impl Expr {
    pub fn span(&self) -> &Span {
        match self {
            Expr::Literal(_, s) => s,
            Expr::Ident(_, s) => s,
            Expr::BinOp(_, _, _, s) => s,
            Expr::UnOp(_, _, s) => s,
            Expr::Assign(_, _, s) => s,
            Expr::CompoundAssign(_, _, _, s) => s,
            Expr::FieldAccess(_, _, s) => s,
            Expr::IndexAccess(_, _, s) => s,
            Expr::MethodCall(_, _, _, s) => s,
            Expr::Call(_, _, s) => s,
            Expr::If { span, .. } => span,
            Expr::Match { span, .. } => span,
            Expr::While { span, .. } => span,
            Expr::For { span, .. } => span,
            Expr::Do { span, .. } => span,
            Expr::StructLit(_, _, s) => s,
            Expr::ArrayLit(_, s) => s,
            Expr::TupleLit(_, s) => s,
            Expr::Closure { span, .. } => span,
            Expr::Cast(_, _, s) => s,
            Expr::Range(_, _, _, s) => s,
            Expr::Unsafe(_, _, s) => s,
            Expr::Return(_, s) => s,
            Expr::SelfExpr(s) => s,
            Expr::Try(_, s) => s,
            Expr::Await(_, s) => s,
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
    pub guard: Option<Expr>,
    pub body: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ArenaKind {
    /// Default general-purpose arena (like std::heap.GeneralPurposeAllocator in Zig)
    General,
    /// Stack-based fixed buffer — no heap, size known at compile time
    Fixed,
    /// Pool allocator — all objects same size, very fast free
    Pool,
    /// OS page-granular allocator (mmap/VirtualAlloc)
    Page,
    /// Ring/circular buffer allocator — stream processing
    Ring,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ManualKind {
    /// Modern manual: typed Box/Arc semantics, drop on scope exit
    Modern,
    /// Classic C-like: malloc/free, no automatic cleanup
    Classic,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum UnsafeMode {
    /// unsafe arena is...end               — GeneralPurposeAllocator (default)
    /// unsafe arena(fixed) is...end        — FixedBufferAllocator
    /// unsafe arena(pool) is...end         — MemoryPoolAllocator
    /// unsafe arena(page) is...end         — PageAllocator
    /// unsafe arena(ring) is...end         — RingBufferAllocator
    Arena { kind: ArenaKind, size: Option<usize> },
    /// unsafe manual is...end              — modern RAII manual
    /// unsafe manual(classic) is...end     — C-like malloc/free
    Manual(ManualKind),
    /// unsafe is...end                     — raw, no allocator overhead
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
        name: String,
        ty: Option<TypeExpr>,
        mutable: bool,
        value: Option<Expr>,
        span: Span,
    },
    Expr(Expr, Span),
    Return(Option<Expr>, Span),
    Import(ImportKind, Option<String>, Span),  // import "...", alias
    Break(Option<Expr>, Span),
    Continue(Span),
    Item(Item),
}

// ─── Items (top-level or nested) ──────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Item {
    FnDef(FnDef),
    StructDef(StructDef),
    EnumDef(EnumDef),
    TraitDef(TraitDef),
    ImplBlock(ImplBlock),
    TypeAlias { name: String, ty: TypeExpr, pub_: bool, span: Span },
    Extern(ExternBlock),
    /// mod name — include file or directory module
    ModDecl {
        name:   String,   // module name (= filename without .h#)
        pub_:   bool,
        inline: Option<Vec<Item>>,  // Some(items) = inline mod { }, None = external file
        span:   Span,
    },
}


/// Attribute — #[name] or #[name(args)] applied to items/exprs

/// Generic type parameter: T, T: Trait, T: Trait + OtherTrait
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypeParam {
    pub name:   String,
    pub bounds: Vec<String>,  // trait bounds
    pub span:   Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Attribute {
    pub name: String,
    pub args: Vec<AttrArg>,
    pub span: Span,
}

/// Attribute argument: #[name(key = "value", flag, expr)]
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum AttrArg {
    Ident(String),                         // #[inline]
    KeyValue(String, String),              // #[cfg(target = "linux")]
    Lit(String),                           // #[doc("text")]
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FnDef {
    pub attrs:       Vec<Attribute>,
    pub type_params: Vec<TypeParam>,
    pub name:        String,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub body: Vec<Stmt>,
    pub pub_: bool,
    pub is_unsafe: bool,
    pub is_async:  bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Param {
    pub name: String,
    pub ty: TypeExpr,
    pub mutable: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StructDef {
    pub attrs:       Vec<Attribute>,
    pub type_params: Vec<TypeParam>,
    pub name:        String,
    pub fields: Vec<StructField>,
    pub pub_: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StructField {
    pub name: String,
    pub ty: TypeExpr,
    pub pub_: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EnumDef {
    pub attrs:       Vec<Attribute>,
    pub type_params: Vec<TypeParam>,
    pub name:        String,
    pub variants: Vec<EnumVariant>,
    pub pub_: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EnumVariant {
    pub name: String,
    pub fields: EnumVariantFields,
    pub span: Span,
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
    pub methods: Vec<TraitMethod>,
    pub pub_: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TraitMethod {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub default_body: Option<Vec<Stmt>>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ImplBlock {
    pub type_name: String,
    pub trait_name: Option<String>,
    pub methods: Vec<FnDef>,
    pub span: Span,
}

// ─── Module / top-level ───────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Directive {
    pub kind: DirectiveKind,
    pub value: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum DirectiveKind {
    Dynamic,    // ~ "dynamic:..."
    Fast,       // ~~ "fast:..."
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Module {
    pub file: String,
    pub directives: Vec<Directive>,
    pub items: Vec<Item>,
    pub imports: Vec<(ImportKind, Option<String>, Span)>,
}

/// extern static [c] is ... end
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExternBlock {
    pub lang:      ExternLang,
    pub link_kind: ExternLinkKind,
    pub library:   Option<String>,
    pub functions: Vec<ExternFnDecl>,
    pub span:      Span,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ExternLang { C, Rust, Cpp }

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

/// Closure parameter: |x| or |x: int| or |mut x|
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ClosureParam {
    pub name:    String,
    pub ty:      Option<TypeExpr>,
    pub mutable: bool,
    pub span:    Span,
}
