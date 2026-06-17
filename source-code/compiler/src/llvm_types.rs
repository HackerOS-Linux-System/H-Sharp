use inkwell::context::Context;
use inkwell::AddressSpace;
use inkwell::types::{BasicMetadataTypeEnum, BasicTypeEnum};
use hsharp_parser::ast::TypeExpr;

pub fn htype_to_llvm<'ctx>(ctx: &'ctx Context, ty: &TypeExpr) -> Option<BasicTypeEnum<'ctx>> {
    match ty {
        TypeExpr::Named(n) => match n.as_str() {
            "int"  | "i64"  => Some(ctx.i64_type().into()),
            "uint" | "u64"  => Some(ctx.i64_type().into()),
            "i32"  | "u32"  => Some(ctx.i32_type().into()),
            "i16"  | "u16"  => Some(ctx.i16_type().into()),
            "i8"   | "u8"   => Some(ctx.i8_type().into()),
            "f64"           => Some(ctx.f64_type().into()),
            "f32"           => Some(ctx.f32_type().into()),
            "bool"          => Some(ctx.i8_type().into()),
            "string"        => Some(ctx.ptr_type(AddressSpace::default()).into()),
            "bytes"         => Some(ctx.ptr_type(AddressSpace::default()).into()),
            _               => Some(ctx.i64_type().into()), // opaque ptr
        },
        TypeExpr::Void        => None,
        TypeExpr::Optional(_) => Some(ctx.i64_type().into()),
        TypeExpr::Ref(_) | TypeExpr::RefMut(_) => Some(ctx.i64_type().into()),
        TypeExpr::Array(_) | TypeExpr::Slice(_, _) => Some(ctx.i64_type().into()),
        TypeExpr::Tuple(_) | TypeExpr::Generic(_, _) => Some(ctx.i64_type().into()),
        TypeExpr::Fn(_, _) => Some(ctx.i64_type().into()),
        TypeExpr::I8  | TypeExpr::U8  | TypeExpr::Bool   => Some(ctx.i8_type().into()),
        TypeExpr::I16 | TypeExpr::U16                     => Some(ctx.i16_type().into()),
        TypeExpr::I32 | TypeExpr::U32                     => Some(ctx.i32_type().into()),
        TypeExpr::I64 | TypeExpr::U64 | TypeExpr::I128 | TypeExpr::U128 => Some(ctx.i64_type().into()),
        TypeExpr::F32         => Some(ctx.f32_type().into()),
        TypeExpr::F64         => Some(ctx.f64_type().into()),
        TypeExpr::String | TypeExpr::Bytes => Some(ctx.ptr_type(AddressSpace::default()).into()),
    }
}

pub fn htype_to_meta<'ctx>(ctx: &'ctx Context, ty: &TypeExpr) -> Option<BasicMetadataTypeEnum<'ctx>> {
    htype_to_llvm(ctx, ty).map(|t| t.into())
}
