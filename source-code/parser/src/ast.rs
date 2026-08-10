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

    /// Overwrites every span in this expression (and, recursively, every
    /// sub-expression) with `new_span`. Used by `parse_interpolated_string`
    /// (see parser.rs): a `{expr}` interpolation marker's contents are
    /// parsed by re-running the whole parser on a small synthesized
    /// snippet (`fn __interp__() is return {expr} end`) in a fake file
    /// called `"<interp>"`, so every span in the resulting tree pointed at
    /// that fake file and a made-up line/column relative to the snippet —
    /// completely disconnected from where the string literal actually
    /// lives. Any error surfaced later against one of those spans (e.g.
    /// "undefined var" — see codegen.rs) showed `<interp>:2:12` instead of
    /// the real file, which is close to useless for tracking the bug down
    /// in a real multi-file project. Remapping every span in the parsed-
    /// out sub-expression back to the original string literal's real span
    /// isn't perfectly precise (it points at the start of the whole string
    /// literal, not the exact character offset inside it), but "the right
    /// file, roughly the right line" is a large improvement over "a file
    /// that doesn't exist".
    pub fn remap_span(&mut self, new_span: &Span) {
        match self {
            Expr::Literal(_, s) | Expr::Ident(_, s) | Expr::FieldAccess(_, _, s) |
            Expr::MethodCall(_, _, _, s) | Expr::Call(_, _, s) | Expr::StructLit(_, _, s) |
            Expr::ArrayLit(_, s) | Expr::TupleLit(_, s) | Expr::Cast(_, _, s) |
            Expr::Unsafe(_, _, s) | Expr::Return(_, s) | Expr::SelfExpr(s) |
            Expr::Try(_, s) | Expr::Await(_, s) | Expr::Path(_, s) => *s = new_span.clone(),
            Expr::BinOp(l, _, r, s) => { l.remap_span(new_span); r.remap_span(new_span); *s = new_span.clone(); }
            Expr::UnOp(_, e, s) => { e.remap_span(new_span); *s = new_span.clone(); }
            Expr::Assign(l, r, s) | Expr::CompoundAssign(l, _, r, s) => {
                l.remap_span(new_span); r.remap_span(new_span); *s = new_span.clone();
            }
            Expr::IndexAccess(a, b, s) | Expr::Range(a, b, _, s) => {
                a.remap_span(new_span); b.remap_span(new_span); *s = new_span.clone();
            }
            Expr::If { condition, span, .. } => { condition.remap_span(new_span); *span = new_span.clone(); }
            Expr::Match { subject, span, .. } => { subject.remap_span(new_span); *span = new_span.clone(); }
            Expr::While { condition, span, .. } => { condition.remap_span(new_span); *span = new_span.clone(); }
            Expr::For { iterable, span, .. } => { iterable.remap_span(new_span); *span = new_span.clone(); }
            Expr::Do { span, .. } | Expr::Closure { span, .. } => { *span = new_span.clone(); }
        }
        // Note: nested `Vec<Expr>`/`Vec<Stmt>` bodies (function-call args,
        // struct/array literal fields, if/while/for/match/closure bodies)
        // are intentionally left unremapped here — interpolation content
        // that goes this deep (a whole `if`/`match`/closure inline inside
        // `{...}`) is already an unusual edge case, and remapping every
        // statement in a block recursively would need a second traversal
        // over `Stmt` too. The common case (a bare variable, a field
        // access, a simple binary expression, a single function call —
        // exactly what triggered this bug) is fully covered.
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub enum MemoryMode {
    /// No `@...` annotation written at all (or explicit `@default`): the
    /// language's current memory behavior — plain heap allocation, no
    /// automatic reclamation. Kept as the literal default so every
    /// existing FnDef construction site that doesn't care about memory
    /// modes can just use `..Default::default()`/derive without changes.
    #[default]
    Default,
    /// `@safety` — a control-flow-aware move-after-use heuristic
    /// (`Self::check_moves_basic` + `region_drop_audit` in codegen.rs),
    /// **not** a full ownership/borrow checker and **not** a soundness
    /// guarantee. Codegen itself is identical to `Default` — this mode
    /// only adds a static analysis pass, no runtime behavior difference —
    /// and a `note:` is printed at compile time saying exactly that, every
    /// time a `@safety` function is compiled, so this is a documented,
    /// visible limitation rather than a silent one. See the
    /// `MemoryMode::Safety` arm in `compile_fn` for the exact wording.
    Safety,
    /// `@arc` — real atomic refcounting, not a stub: `arc_alloc`/
    /// `arc_retain`/`arc_release`/`arc_count` are genuine builtins, gated
    /// by the typechecker so they're only callable from an `@arc`/
    /// `@pointers` function or an `unsafe ... end` block (see
    /// typechecker.rs). What *isn't* covered: `let`-bindings only reach
    /// automatic retain/release when bound at the function's top level
    /// (not inside `if`/`while`/`for`/`match`/`do`/`unsafe`), and an ARC
    /// pointer stashed inside a struct field or array element instead of
    /// held as a bare local still needs manual `arc_retain`/`arc_release`.
    /// Both boundaries are printed as a compile-time `note:` on every
    /// `@arc` function, not left for the programmer to discover the hard
    /// way — see the `MemoryMode::Arc` arm in `compile_fn`.
    Arc,
    /// `@arena` — bump-allocates everything created during this
    /// function's call into a single arena, freed in one shot on every
    /// exit path. Fully implemented — see `compile_fn`/`build_return_coerced`.
    Arena,
    /// `@pointers` — typed, unchecked-by-design `ptr_read_*`/`ptr_write_*`/
    /// `ptr_add`/`ptr_is_null` builtins (i8/i16/i32/i64/f32/f64/ptr), gated
    /// by the typechecker exactly like `@arc`'s builtins (only reachable
    /// from a `@pointers`/`@arc` function or `unsafe ... end`) — a real,
    /// checked boundary, not a doc-only convention. "Unchecked by design"
    /// here means what it says: these builtins trust the caller (no bounds
    /// checking, no alignment checking) *by design*, same as `unsafe` raw
    /// pointer arithmetic in Rust — that is the feature, not a limitation
    /// to fix later.
    Pointers,
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
    pub mem_mode:    MemoryMode,
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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Module {
    pub file:       String,
    pub edition:    Option<String>,
    /// File-level `@: safety`/`@: arc`/`@: arena`/`@: pointers`/`@: default`
    /// directive (see `parse_module`'s handling of it, and
    /// `apply_file_mem_mode` below) — sets the default `MemoryMode` for
    /// every function in this file that doesn't carry its own `@mode`
    /// annotation, instead of having to write `@mode` above every single
    /// `fn`. A function-level `@mode` annotation always wins over this
    /// when both are present (the file default only fills in functions
    /// that were left at `MemoryMode::Default`, i.e. had no annotation
    /// of their own).
    pub file_mem_mode: Option<MemoryMode>,
    pub items:      Vec<Item>,
    pub imports:    Vec<(ImportKind, Option<String>, Span)>,
}

/// Applies `module.file_mem_mode` (see its doc comment) to every function
/// in the module — top-level `fn`s and `impl` methods alike — that's
/// still at `MemoryMode::Default`, i.e. wasn't given its own `@mode`.
/// A no-op if the file has no `@: mode` directive. Called once, right
/// after parsing, from both the LLVM pipeline (`lib.rs::compile`) and the
/// interpreter (`interp.rs::run_module`/`run_module_register_only`) so
/// the directive has identical effect in both backends.
pub fn apply_file_mem_mode(module: &mut Module) {
    let Some(mode) = module.file_mem_mode else { return; };
    for item in &mut module.items {
        apply_file_mem_mode_item(item, mode);
    }
}

pub fn apply_file_mem_mode_item(item: &mut Item, mode: MemoryMode) {
    match item {
        Item::FnDef(f) => {
            if f.mem_mode == MemoryMode::Default { f.mem_mode = mode; }
        }
        Item::ImplBlock(imp) => {
            for method in &mut imp.methods {
                if method.mem_mode == MemoryMode::Default { method.mem_mode = mode; }
            }
        }
        Item::ModDecl { inline: Some(items), .. } => {
            for sub in items { apply_file_mem_mode_item(sub, mode); }
        }
        _ => {}
    }
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
    Python,
}

impl ExternLang {
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "c"                    => Some(ExternLang::C),
            "rust"                 => Some(ExternLang::Rust),
            "c++" | "cpp" | "cxx" => Some(ExternLang::Cpp),
            "python" | "py"        => Some(ExternLang::Python),
            _                      => None,
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            ExternLang::C      => "c",
            ExternLang::Rust   => "rust",
            ExternLang::Cpp    => "c++",
            ExternLang::Python => "python",
        }
    }

    /// C ABI — these can be directly linked with cc/ld.
    pub fn is_c_abi(&self) -> bool {
        matches!(self, ExternLang::C | ExternLang::Rust | ExternLang::Cpp)
    }

    /// Python bridge — called via subprocess/CPython, not direct link.
    pub fn is_python_bridge(&self) -> bool {
        matches!(self, ExternLang::Python)
    }
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
