use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize, Clone)]
pub enum HSharpLiteral {
    Int(i32),
    Bool(bool),
    String(String),
    RawString(String),
    Byte(u8),
    Float(f64),
}

#[derive(Debug, Deserialize, Serialize, Clone, Copy, PartialEq, Eq)]
pub enum HSharpOp {
    Add, Sub, Mul, Div, Mod,
    Eq, Ne, Lt, Gt, Le, Ge,
    And, Or,
    Shl, Shr, BitAnd, BitXor, BitOr,
}

#[derive(Debug, Deserialize, Serialize, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg, BitNot, Deref, AddrOf
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub enum HType {
    I8,
    I32,
    I64,
    Bool,
    F32,
    F64,
    U8,
    U16,
    U32,
    U64,
    Pointer(Box<HType>),
    Array(Box<HType>, usize),
    Slice(Box<HType>),
    Struct(String, Vec<HType>),
    Generic(String),
    Union(String),
    Unit,
    Tuple(Vec<HType>),
    Enum(String),
    Result(Box<HType>, Box<HType>),
    Option(Box<HType>),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub enum HSharpExpr {
    Literal(HSharpLiteral),
    Var(String),
    Alloc(Box<HSharpExpr>),
    Dealloc(Box<HSharpExpr>),
    Unary(UnaryOp, Box<HSharpExpr>),
    Assign(Box<HSharpExpr>, Box<HSharpExpr>),
    Write(Box<HSharpExpr>),
    Block(Vec<HSharpStmt>),
    Direct(Box<HSharpExpr>),
    BinOp(HSharpOp, Box<HSharpExpr>, Box<HSharpExpr>),
    If(Box<HSharpExpr>, Box<HSharpExpr>, Option<Box<HSharpExpr>>),
    While(Box<HSharpExpr>, Box<HSharpExpr>),
    For(String, Box<HSharpExpr>, Box<HSharpExpr>, Box<HSharpExpr>),
    Break,
    Continue,
    Match(Box<HSharpExpr>, Vec<(HSharpExpr, HSharpExpr)>, Option<Box<HSharpExpr>>),
    Call(String, Vec<HSharpExpr>),
    MethodCall(Box<HSharpExpr>, String, Vec<HSharpExpr>),
    Cast(HType, Box<HSharpExpr>),
    SizeOf(HType),
    StructLit(String, Vec<HSharpExpr>),
    // Enum/Union literal: EnumName, VariantName, Args
    EnumLit(String, String, Vec<HSharpExpr>),
    ArrayLit(Vec<HSharpExpr>),
    Field(Box<HSharpExpr>, String),
    Index(Box<HSharpExpr>, Box<HSharpExpr>),
    Return(Box<HSharpExpr>),
    Tuple(Vec<HSharpExpr>),
    Closure(Vec<String>, Box<HSharpExpr>),
    Await(Box<HSharpExpr>),
    OptionalChain(Box<HSharpExpr>),
    Range(Box<HSharpExpr>, Box<HSharpExpr>, bool),
    Try(Box<HSharpExpr>),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub enum EnumVariant {
    Unit,
    Tuple(Vec<HType>),
    Struct(Vec<(String, HType)>),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub enum HSharpStmt {
    Let(String, Option<HType>, HSharpExpr),
    Expr(HSharpExpr),
    FunctionDef(String, Vec<(String, HType)>, HType, Option<Box<HSharpExpr>>, bool), // Added is_async bool
    StructDef(String, Vec<String>, Vec<(String, HType)>),
    UnionDef(String, Vec<(String, HType)>),
    Impl(String, Vec<HSharpStmt>),
    Import(String, Vec<RequireItem>),
    ConstDef(String, HType, HSharpExpr),
    TypeAlias(String, HType),
    EnumDef(String, Vec<(String, EnumVariant)>), // Variant name + Variant Type
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub enum RequireItem {
    WholeModule(String),
    Specific(String, String),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct HSharpProgram {
    pub stmts: Vec<HSharpStmt>,
}
