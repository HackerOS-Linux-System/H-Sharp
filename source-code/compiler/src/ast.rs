use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use cranelift::prelude::types;

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

#[derive(Debug, Clone)]
pub enum StructOrUnion {
    Struct(Vec<(String, HType)>),
    Union(Vec<(String, HType)>),
}

impl HType {
    pub fn size(&self, type_map: &HashMap<String, StructOrUnion>) -> u32 {
        match self {
            HType::I8 | HType::Bool => 1,
            HType::I32 | HType::F32 => 4,
            HType::F64 | HType::Pointer(_) => 8,
            HType::Unit => 0,
            HType::Array(inner, len) => inner.size(type_map) * *len as u32,
            HType::Struct(name) | HType::Union(name) => type_map
            .get(name)
            .map(|s| s.calculate_size(type_map))
            .unwrap_or(0),
        }
    }

    pub fn alignment(&self, type_map: &HashMap<String, StructOrUnion>) -> u32 {
        match self {
            HType::I8 | HType::Bool => 1,
            HType::I32 | HType::F32 => 4,
            HType::F64 | HType::Pointer(_) => 8,
            HType::Unit => 1,
            HType::Array(inner, _) => inner.alignment(type_map),
            HType::Struct(name) | HType::Union(name) => type_map
            .get(name)
            .map(|s| s.calculate_alignment(type_map))
            .unwrap_or(1),
        }
    }

    pub fn cl_type(&self) -> types::Type {
        match self {
            HType::I8 | HType::Bool => types::I8,
            HType::I32 => types::I32,
            HType::F32 => types::F32,
            HType::F64 => types::F64,
            HType::Pointer(_) => types::I64,
            _ => types::INVALID,
        }
    }

    pub fn is_value_type(&self) -> bool {
        self.cl_type() != types::INVALID
    }

    pub fn param_type(&self) -> types::Type {
        if self.is_value_type() {
            self.cl_type()
        } else {
            types::I64
        }
    }
}

impl StructOrUnion {
    pub fn calculate_size(&self, type_map: &HashMap<String, StructOrUnion>) -> u32 {
        match self {
            StructOrUnion::Struct(fields) => {
                let mut size = 0;
                for (_, t) in fields {
                    let align = t.alignment(type_map);
                    size = ((size + align - 1) / align) * align + t.size(type_map);
                }
                let overall_align = self.calculate_alignment(type_map);
                ((size + overall_align - 1) / overall_align) * overall_align
            }
            StructOrUnion::Union(fields) => fields
            .iter()
            .map(|(_, t)| t.size(type_map))
            .max()
            .unwrap_or(0),
        }
    }

    pub fn calculate_alignment(&self, type_map: &HashMap<String, StructOrUnion>) -> u32 {
        match self {
            StructOrUnion::Struct(fields) | StructOrUnion::Union(fields) => fields
            .iter()
            .map(|(_, t)| t.alignment(type_map))
            .max()
            .unwrap_or(1),
        }
    }

    pub fn field_offset(&self, field: &str, type_map: &HashMap<String, StructOrUnion>) -> u32 {
        match self {
            StructOrUnion::Struct(fields) => {
                let mut offset = 0;
                for (name, t) in fields {
                    if name == field {
                        return offset;
                    }
                    let align = t.alignment(type_map);
                    offset = ((offset + align - 1) / align) * align + t.size(type_map);
                }
                0
            }
            StructOrUnion::Union(_) => 0,
        }
    }

    pub fn field_type(&self, field: &str) -> Option<HType> {
        match self {
            StructOrUnion::Struct(fields) | StructOrUnion::Union(fields) => fields
            .iter()
            .find(|(n, _)| n == field)
            .map(|(_, t)| t.clone()),
        }
    }
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
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct HSharpProgram {
    pub stmts: Vec<HSharpStmt>,
}
