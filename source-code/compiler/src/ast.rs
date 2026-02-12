use std::collections::HashMap;
use cranelift::prelude::types;

// Re-export AST types from the parser crate so both crates share the same types.
// This fixes the mismatched types error in the main CLI.
pub use h_sharp_parser::ast::{
    HSharpExpr, HSharpLiteral, HSharpOp, HSharpProgram, HSharpStmt, HType, RequireItem
};

// Helper enum for internal compiler layout tracking (not part of AST)
#[derive(Debug, Clone)]
pub enum StructOrUnion {
    Struct(Vec<(String, HType)>),
    Union(Vec<(String, HType)>),
}

// Extension trait to add methods to the external HType
// This allows us to keep layout logic in the compiler while using the parser's AST.
pub trait HTypeExt {
    fn size(&self, type_map: &HashMap<String, StructOrUnion>) -> u32;
    fn alignment(&self, type_map: &HashMap<String, StructOrUnion>) -> u32;
    fn cl_type(&self) -> types::Type;
    fn is_value_type(&self) -> bool;
    fn param_type(&self) -> types::Type;
}

impl HTypeExt for HType {
    fn size(&self, type_map: &HashMap<String, StructOrUnion>) -> u32 {
        match self {
            HType::I8 | HType::Bool => 1,
            HType::I32 | HType::F32 => 4,
            HType::F64 | HType::I64 | HType::Pointer(_) => 8,
            HType::Slice(_) => 16, // Ptr(8) + Len(8)
            HType::Unit => 0,
            HType::Array(inner, len) => inner.size(type_map) * *len as u32,
            HType::Struct(name) | HType::Union(name) => type_map.get(name).map(|s| s.calculate_size(type_map)).unwrap_or(0),
        }
    }

    fn alignment(&self, type_map: &HashMap<String, StructOrUnion>) -> u32 {
        match self {
            HType::I8 | HType::Bool => 1,
            HType::I32 | HType::F32 => 4,
            HType::F64 | HType::I64 | HType::Pointer(_) | HType::Slice(_) => 8,
            HType::Unit => 1,
            HType::Array(inner, _) => inner.alignment(type_map),
            HType::Struct(name) | HType::Union(name) => type_map.get(name).map(|s| s.calculate_alignment(type_map)).unwrap_or(1),
        }
    }

    fn cl_type(&self) -> types::Type {
        match self {
            HType::I8 | HType::Bool => types::I8,
            HType::I32 => types::I32,
            HType::I64 => types::I64,
            HType::F32 => types::F32,
            HType::F64 => types::F64,
            HType::Pointer(_) => types::I64,
            HType::Slice(_) => types::I128,
            _ => types::INVALID,
        }
    }

    fn is_value_type(&self) -> bool {
        self.cl_type() != types::INVALID
    }

    fn param_type(&self) -> types::Type {
        if let HType::Unit = self {
            return types::INVALID;
        }
        if self.is_value_type() && !matches!(self, HType::Slice(_)) {
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
            StructOrUnion::Union(fields) => fields.iter().map(|(_, t)| t.size(type_map)).max().unwrap_or(0),
        }
    }

    pub fn calculate_alignment(&self, type_map: &HashMap<String, StructOrUnion>) -> u32 {
        match self {
            StructOrUnion::Struct(fields) | StructOrUnion::Union(fields) => fields.iter().map(|(_, t)| t.alignment(type_map)).max().unwrap_or(1),
        }
    }

    pub fn field_offset(&self, field: &str, type_map: &HashMap<String, StructOrUnion>) -> u32 {
        match self {
            StructOrUnion::Struct(fields) => {
                let mut offset = 0;
                for (name, t) in fields {
                    if name == field { return offset; }
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
            StructOrUnion::Struct(fields) | StructOrUnion::Union(fields) => fields.iter().find(|(n, _)| n == field).map(|(_, t)| t.clone()),
        }
    }
}
