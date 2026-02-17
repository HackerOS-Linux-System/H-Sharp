use crate::ast::HType;
use cranelift::prelude::types as cl_types; // Alias to avoid conflict with module name
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum StructOrUnion {
    Struct(Vec<(String, HType)>),
    Union(Vec<(String, HType)>),
}

pub trait HTypeExt {
    fn size(&self, type_map: &HashMap<String, StructOrUnion>) -> u32;
    fn alignment(&self, type_map: &HashMap<String, StructOrUnion>) -> u32;
    fn cl_type(&self) -> cl_types::Type;
    fn is_value_type(&self) -> bool;
    fn param_type(&self) -> cl_types::Type;
}

impl HTypeExt for HType {
    fn size(&self, type_map: &HashMap<String, StructOrUnion>) -> u32 {
        match self {
            HType::I8 | HType::U8 | HType::Bool => 1,
            HType::I16 | HType::U16 => 2,
            HType::I32 | HType::U32 | HType::F32 => 4,
            HType::I64 | HType::U64 | HType::F64 | HType::Pointer(_) => 8,
            HType::Slice(_) => 16, // Ptr(8) + Len(8)
            HType::Unit => 0,
            HType::Array(inner, len) => inner.size(type_map) * *len as u32,
            // FIX: Ignore generic args vector with `_`, we rely on the mangled name in type_map
            HType::Struct(name, _) | HType::Union(name) => type_map
            .get(name)
            .map(|s| s.calculate_size(type_map))
            .unwrap_or(0),
            HType::Generic(g) => panic!(
                "Generic type '{}' should have been monomorphized before size calculation! Compiler Error.",
                g
            ),
        }
    }

    fn alignment(&self, type_map: &HashMap<String, StructOrUnion>) -> u32 {
        match self {
            HType::I8 | HType::U8 | HType::Bool => 1,
            HType::I16 | HType::U16 => 2,
            HType::I32 | HType::U32 | HType::F32 => 4,
            HType::I64 | HType::U64 | HType::F64 | HType::Pointer(_) | HType::Slice(_) => 8,
            HType::Unit => 1,
            HType::Array(inner, _) => inner.alignment(type_map),
            // FIX: Ignore generic args vector with `_`
            HType::Struct(name, _) | HType::Union(name) => type_map
            .get(name)
            .map(|s| s.calculate_alignment(type_map))
            .unwrap_or(1),
            HType::Generic(g) => panic!(
                "Generic type '{}' should have been monomorphized before alignment calculation! Compiler Error.",
                g
            ),
        }
    }

    fn cl_type(&self) -> cl_types::Type {
        match self {
            HType::I8 | HType::U8 | HType::Bool => cl_types::I8,
            HType::I16 | HType::U16 => cl_types::I16,
            HType::I32 | HType::U32 => cl_types::I32,
            HType::I64 | HType::U64 => cl_types::I64,
            HType::F32 => cl_types::F32,
            HType::F64 => cl_types::F64,
            HType::Pointer(_) => cl_types::I64,
            HType::Slice(_) => cl_types::I128,
            _ => cl_types::INVALID,
        }
    }

    fn is_value_type(&self) -> bool {
        self.cl_type() != cl_types::INVALID
    }

    fn param_type(&self) -> cl_types::Type {
        if let HType::Unit = self {
            return cl_types::INVALID;
        }
        if self.is_value_type() && !matches!(self, HType::Slice(_)) {
            self.cl_type()
        } else {
            cl_types::I64
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
            StructOrUnion::Union(fields) => {
                let max_size = fields
                .iter()
                .map(|(_, t)| t.size(type_map))
                .max()
                .unwrap_or(0);
                let overall_align = self.calculate_alignment(type_map);
                ((max_size + overall_align - 1) / overall_align) * overall_align
            }
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
