use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize, Clone)]
pub enum HSharpLiteral {
    Int(i32),
    Bool(bool),
    String(String),
    Float(f64),
}

#[derive(Debug, Deserialize, Serialize, Clone, Copy, PartialEq, Eq)]
pub enum HSharpOp {
    Add, Sub, Mul, Div, Mod,
    Eq, Ne, Lt, Gt, Le, Ge,
    And, Or,
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub enum HType {
    I8,
    I32,
    I64, // Added for pointer-sized integers / lengths
    Bool,
    F32,
    F64,
    Pointer(Box<HType>),
    Array(Box<HType>, usize),
    Slice(Box<HType>), // Dynamic array: { ptr, len }
    Struct(String),
    Union(String),
    Unit,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub enum HSharpExpr {
    Literal(HSharpLiteral),
    Var(String),
    Alloc(Box<HSharpExpr>),
    Dealloc(Box<HSharpExpr>),
    Deref(Box<HSharpExpr>),
    Assign(Box<HSharpExpr>, Box<HSharpExpr>),
    Write(Box<HSharpExpr>),
    Block(Vec<HSharpStmt>),
    Direct(Box<HSharpExpr>),
    BinOp(HSharpOp, Box<HSharpExpr>, Box<HSharpExpr>),
    AddrOf(Box<HSharpExpr>),
    If(Box<HSharpExpr>, Box<HSharpExpr>, Option<Box<HSharpExpr>>),
    While(Box<HSharpExpr>, Box<HSharpExpr>),
    For(String, Box<HSharpExpr>, Box<HSharpExpr>, Box<HSharpExpr>),
    Break,
    Continue,
    Match(Box<HSharpExpr>, Vec<(HSharpExpr, HSharpExpr)>, Option<Box<HSharpExpr>>), // target, cases (val, body), default
    Call(String, Vec<HSharpExpr>),
    MethodCall(Box<HSharpExpr>, String, Vec<HSharpExpr>), // obj.method(args)
    Cast(HType, Box<HSharpExpr>),
    SizeOf(HType),
    StructLit(String, Vec<HSharpExpr>),
    UnionLit(String, String, Box<HSharpExpr>),
    ArrayLit(Vec<HSharpExpr>),
    Field(Box<HSharpExpr>, String),
    Index(Box<HSharpExpr>, Box<HSharpExpr>),
    Return(Box<HSharpExpr>),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub enum HSharpStmt {
    Let(String, Option<HType>, HSharpExpr),
    Expr(HSharpExpr),
    FunctionDef(String, Vec<(String, HType)>, HType, Box<HSharpExpr>),
    StructDef(String, Vec<(String, HType)>),
    UnionDef(String, Vec<(String, HType)>),
    Impl(String, Vec<HSharpStmt>), // Methods for a struct
    Import(String, Vec<RequireItem>),
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
