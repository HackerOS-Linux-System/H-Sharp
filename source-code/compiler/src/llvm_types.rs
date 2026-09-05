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
            // Catch-all for "any", every user struct/enum name, and
            // anything else this function doesn't otherwise recognize.
            //
            // ── READ THIS BEFORE "fixing" the `i64_type()` below ──────
            // The comment used to say "opaque ptr" while the code
            // returned a plain 64-bit *integer* type — which looks like
            // a bug (and was reported as a suspected one), but isn't:
            // this `i64` slot width is the same uniform representation
            // *every* struct field uses on this backend, not something
            // specific to `any`. See `codegen.rs`'s `Expr::StructLit`
            // handling (`hsh_struct_new`/`hsh_struct_set`) and
            // `core.c`'s `hsh_struct_new`/`hsh_struct_get`/`hsh_struct_set`:
            // a struct is a raw `int64_t[n_fields]` array with **no type
            // tag stored per slot at all** — a string field's pointer is
            // bitcast to `i64` to go in, and bitcast back to `char*` to
            // come out, purely based on the *static* H# type the caller
            // already knows at that specific read/write site. It's the
            // same trick a `union`-of-same-width-members does in C: safe
            // as long as every read site agrees with whatever the last
            // write site's real type was, entirely by programmer
            // convention, with zero runtime enforcement.
            //
            // What this means for `any` specifically: an `any`-typed
            // struct field or hashmap value on THIS backend is exactly
            // as safe as any other struct field — i.e. safe as long as
            // it only ever holds one real underlying type end-to-end
            // (e.g. `std/collections.h#`'s hashmap-based wrappers in
            // `cli.h#`/`config.h#`/`cache.h#`/`template.h#`/`toml.h#`/
            // `yaml.h#`, which today only ever store `string` values,
            // and are always read back with an explicit `-> string`
            // annotation at the call site). It is NOT a real tagged
            // dynamic value the way `hsharp-interpreter`'s `Value` enum
            // is — mixing types through the same `any` slot (storing an
            // `int` somewhere and later reading it as a `string`, or
            // vice versa) has zero runtime check here and would silently
            // reinterpret garbage bits rather than raise an error the
            // way the interpreter would.
            //
            // Changing this fallback (e.g. to a real pointer type, or to
            // an actual tagged union) would ripple through every struct
            // field of every type in every H#-on-AOT program that
            // exists today — this is not a narrow, `any`-specific fix,
            // it's a change to this backend's fundamental value
            // representation, and isn't something to attempt without a
            // compiler on hand to verify against.
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
