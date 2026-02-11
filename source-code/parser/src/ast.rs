use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize, Clone)]
pub enum HSharpLiteral {
    Int(i32),
    Bool(bool),
    String(String),
    Float(f64),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub enum HSharpOp {
    Add,
    Eq,
    Lt,
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub enum HType {
    I8,
    I32,
    Bool,
    F32,
    F64,
    Pointer(Box<HType>),
    Array(Box<HType>, usize),
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
    Call(String, Vec<HSharpExpr>),
    Cast(HType, Box<HSharpExpr>),
    StructLit(String, Vec<HSharpExpr>),
    UnionLit(String, String, Box<HSharpExpr>),
    ArrayLit(Vec<HSharpExpr>),
    Field(Box<HSharpExpr>, String),
    Index(Box<HSharpExpr>, Box<HSharpExpr>),
    For(String, Box<HSharpExpr>, Box<HSharpExpr>, Box<HSharpExpr>),
    Return(Box<HSharpExpr>),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub enum HSharpStmt {
    Let(String, Option<HType>, HSharpExpr),
    Expr(HSharpExpr),
    FunctionDef(String, Vec<(String, HType)>, HType, Box<HSharpExpr>),
    StructDef(String, Vec<(String, HType)>),
    UnionDef(String, Vec<(String, HType)>),
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
