/// H# type → Cranelift type mappings and helpers

use cranelift_codegen::ir::{types, Type, AbiParam, Signature};
use cranelift_codegen::isa::CallConv;
use hsharp_parser::ast::TypeExpr;

/// Map H# AST type to Cranelift IR type
pub fn htype_to_cl(ty: &TypeExpr) -> Option<Type> {
    match ty {
        TypeExpr::Named(n) => match n.as_str() {
            "int"    | "i64"  => Some(types::I64),
            "uint"   | "u64"  => Some(types::I64),
            "i32"             => Some(types::I32),
            "u32"             => Some(types::I32),
            "i16"    | "u16"  => Some(types::I16),
            "i8"     | "u8"   => Some(types::I8),
            "f64"             => Some(types::F64),
            "f32"             => Some(types::F32),
            "bool"            => Some(types::I8),  // 0/1
            "string"          => Some(types::I64), // pointer
            "bytes"           => Some(types::I64), // pointer to hsh_bytes struct
            "any"             => Some(types::I64), // opaque pointer
            _                 => Some(types::I64), // struct pointer
        },
        TypeExpr::Void      => None,
        TypeExpr::Optional(_) => Some(types::I64), // nullable pointer/value
        TypeExpr::Ref(_)
        | TypeExpr::RefMut(_) => Some(types::I64), // pointer
        TypeExpr::Array(_)    => Some(types::I64), // slice header pointer
        TypeExpr::Generic(n, _) => match n.as_str() {
            "Vec" | "Map"  => Some(types::I64),
            _              => Some(types::I64),
        },
        TypeExpr::Tuple(_)  => Some(types::I64), // heap pointer
        TypeExpr::Fn(_, _)  => Some(types::I64), // function pointer
        TypeExpr::Slice(_, _) => Some(types::I64),
        TypeExpr::I8  => Some(types::I8),
        TypeExpr::I16 => Some(types::I16),
        TypeExpr::I32 => Some(types::I32),
        TypeExpr::I64 => Some(types::I64),
        TypeExpr::I128 => Some(types::I64), // truncated for now
        TypeExpr::U8  => Some(types::I8),
        TypeExpr::U16 => Some(types::I16),
        TypeExpr::U32 => Some(types::I32),
        TypeExpr::U64 => Some(types::I64),
        TypeExpr::U128 => Some(types::I64),
        TypeExpr::F32 => Some(types::F32),
        TypeExpr::F64 => Some(types::F64),
        TypeExpr::Bool => Some(types::I8),
        TypeExpr::String => Some(types::I64),
        TypeExpr::Bytes  => Some(types::I64),
    }
}

/// Build Cranelift ABI signature for H# function
pub fn build_signature(
    params: &[TypeExpr],
    ret: Option<&TypeExpr>,
    call_conv: CallConv,
) -> Signature {
    let mut sig = Signature::new(call_conv);
    for p in params {
        if let Some(cl_ty) = htype_to_cl(p) {
            sig.params.push(AbiParam::new(cl_ty));
        }
    }
    if let Some(r) = ret {
        if let Some(cl_ty) = htype_to_cl(r) {
            sig.returns.push(AbiParam::new(cl_ty));
        }
    }
    sig
}

/// Compute stack slot size for a type
pub fn type_stack_size(ty: &TypeExpr) -> u32 {
    match htype_to_cl(ty) {
        Some(t) => t.bytes() as u32,
        None    => 0,
    }
}
