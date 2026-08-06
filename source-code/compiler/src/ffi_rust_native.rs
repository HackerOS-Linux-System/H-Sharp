use hsharp_parser::ast::TypeExpr;
use crate::ffi::ExternFn;

#[derive(Debug, Clone, PartialEq)]
pub enum RsTy {
    Unit,
    Bool,
    I8, I16, I32, I64, Isize,
    U8, U16, U32, U64, Usize,
    F32, F64,
    Str,                 // &str
    Bytes,               // &[u8]
    Vec(Box<RsTy>),       // &[T] / Vec<T>, primitive T only
    Option(Box<RsTy>),
    Result(Box<RsTy>, Box<RsTy>), // Ok(T), Err(E) — E must itself be Str for the message-style shape
    Opaque(String),
}

#[derive(Debug)]
pub enum RustFfiError {
    Unsupported(String),
}

impl std::fmt::Display for RustFfiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RustFfiError::Unsupported(s) => write!(f, "extern [rust]: {}", s),
        }
    }
}

pub fn hsh_type_to_rust_native(ty: &TypeExpr) -> RsTy {
    match ty {
        TypeExpr::Void   => RsTy::Unit,
        TypeExpr::Bool   => RsTy::Bool,
        TypeExpr::I8     => RsTy::I8,  TypeExpr::U8  => RsTy::U8,
        TypeExpr::I16    => RsTy::I16, TypeExpr::U16 => RsTy::U16,
        TypeExpr::I32    => RsTy::I32, TypeExpr::U32 => RsTy::U32,
        TypeExpr::I64    => RsTy::I64, TypeExpr::U64 => RsTy::U64,
        TypeExpr::F32    => RsTy::F32, TypeExpr::F64 => RsTy::F64,
        TypeExpr::String => RsTy::Str,
        TypeExpr::Bytes  => RsTy::Bytes,
        TypeExpr::Array(inner) | TypeExpr::Slice(inner, _) => RsTy::Vec(Box::new(hsh_type_to_rust_native(inner))),
        TypeExpr::Optional(inner) => RsTy::Option(Box::new(hsh_type_to_rust_native(inner))),
        TypeExpr::Generic(n, args) if n == "Result" && args.len() == 2 =>
            RsTy::Result(Box::new(hsh_type_to_rust_native(&args[0])), Box::new(hsh_type_to_rust_native(&args[1]))),
        TypeExpr::Generic(n, args) if (n == "vec" || n == "Vec") && args.len() == 1 =>
            RsTy::Vec(Box::new(hsh_type_to_rust_native(&args[0]))),
        TypeExpr::Named(n) => named_to_rs(n),
        _ => RsTy::Opaque("()".to_string()),
    }
}

fn named_to_rs(n: &str) -> RsTy {
    match n {
        "i8" => RsTy::I8, "u8" => RsTy::U8,
        "i16" => RsTy::I16, "u16" => RsTy::U16,
        "i32" => RsTy::I32, "u32" => RsTy::U32,
        "i64" | "int" => RsTy::I64, "u64" | "uint" => RsTy::U64,
        "isize" => RsTy::Isize, "usize" => RsTy::Usize,
        "f32" => RsTy::F32, "f64" => RsTy::F64,
        "bool" => RsTy::Bool,
        "string" | "str" => RsTy::Str,
        "bytes" => RsTy::Bytes,
        "void" => RsTy::Unit,
        other => RsTy::Opaque(other.to_string()),
    }
}

fn c_flat_type(ty: &RsTy) -> &'static str {
    match ty {
        RsTy::Unit => "()",
        RsTy::Bool => "bool",
        RsTy::I8 => "i8", RsTy::U8 => "u8",
        RsTy::I16 => "i16", RsTy::U16 => "u16",
        RsTy::I32 => "i32", RsTy::U32 => "u32",
        RsTy::I64 | RsTy::Isize => "i64",
        RsTy::U64 | RsTy::Usize => "u64",
        RsTy::F32 => "f32", RsTy::F64 => "f64",
        _ => "*const u8", // marshaled types cross as a tagged buffer, see below
    }
}

/// Generates a real, compilable Rust source file: one `#[no_mangle] pub
/// extern "C" fn hsh_rs_shim_<name>` per extern fn, wrapping the user's real
/// function `user_crate::<name>` (imported idiomatically, not redeclared
/// with a foreign ABI).
///
/// Marshaled types cross the boundary as a `(ptr: *const u8, len: i64)` pair
/// (or, for `Option<T>`/`Result<T,E>`, an extra `i32` tag word ahead of the
/// payload: `0` = None/Err, `1` = Some/Ok) — the same flat tagged-union shape
/// H#'s own codegen already uses for `Optional<T>`, so no new ABI concept is
/// introduced on the H# side; only this generated shim needs to know Rust.
pub fn generate_shim(user_crate: &str, f: &ExternFn) -> Result<String, RustFfiError> {
    let ret_rs = f.return_type.as_ref().map(hsh_type_to_rust_native).unwrap_or(RsTy::Unit);
    let param_rs: Vec<RsTy> = f.params.iter().map(|p| hsh_type_to_rust_native(&p.ty)).collect();

    // ABI NOTE: H#'s own LLVM codegen (`llvm_types::htype_to_llvm`)
    // represents `string` as exactly one pointer argument — a plain
    // null-terminated C string (`hsh_strlen` scans for the terminator, it
    // doesn't read a stored length) — and `bytes`/`Array`/`Slice` as a bare
    // pointer with *no* bundled length at all. So only `&str` (via a
    // null-terminated reconstruction, matching H# exactly) is auto-wired
    // here; anything that would need an invented length or tag word this
    // codebase doesn't actually carry is refused rather than guessed.
    for (p, rty) in f.params.iter().zip(&param_rs) {
        match rty {
            RsTy::Opaque(name) => return Err(RustFfiError::Unsupported(format!(
                "parameter `{}` has type `{}`, which has no known stable layout to \
                 cross the FFI boundary by value — pass a `ref`/`ref mut` (opaque \
                 pointer) instead, or add it to hsh_type_to_rust_native's known shapes",
                p.name, name
            ))),
            RsTy::Bytes | RsTy::Vec(_) => return Err(RustFfiError::Unsupported(format!(
                "parameter `{}` (&[u8]/Vec<T>) has no bundled length at the ABI level \
                 this shim can read — H#'s `bytes`/`Array`/`Slice` are bare pointers. \
                 Declare an explicit paired `len: int` parameter and slice it by hand \
                 in a thin wrapper instead of relying on the auto-generated shim here",
                p.name
            ))),
            RsTy::Option(_) => return Err(RustFfiError::Unsupported(format!(
                "parameter `{}` (Option<T>) needs a presence tag H#'s extern ABI has \
                 no slot for on the *parameter* side — accept the payload type \
                 directly plus a separate `has_value: bool` parameter instead",
                p.name
            ))),
            RsTy::Result(_, err) if !matches!(**err, RsTy::Str) => {
                return Err(RustFfiError::Unsupported(
                    "Result<T, E> parameters are not supported (only Result<T, String> \
                     return values are) — Results only make sense as outcomes, not inputs".into()
                ));
            }
            _ => {}
        }
    }
    if matches!(ret_rs, RsTy::Option(_) | RsTy::Result(_, _)) {
        return Err(RustFfiError::Unsupported(
            "Option<T>/Result<T, E> return values need an explicit out-param the H# \
             side must declare and codegen must know to pass — not yet wired into \
             `build_extern_fn_type`. Return the payload type directly and use a \
             sentinel value (e.g. -1) for the error/None case for now".to_string()
        ));
    }
    if matches!(ret_rs, RsTy::Bytes | RsTy::Vec(_)) {
        return Err(RustFfiError::Unsupported(
            "&[u8]/Vec<T> return values have no bundled-length convention on the H# \
             side to read them back with — return `string` (null-terminated, fully \
             supported) instead, or add an explicit `out_len: ref mut int` output \
             parameter and marshal it by hand".to_string()
        ));
    }

    let mut out = String::new();
    out.push_str("// Auto-generated by hsharp's ffi_rust_native shim generator. Do not edit\n");
    out.push_str("// by hand — regenerated on every `hsharp compile` / `bytes build` that sees\n");
    out.push_str("// this `extern [rust]` block. See ffi_rust_native.rs for the generator.\n");
    out.push_str(&format!("extern crate {} as __user;\n\n", sanitize_ident(user_crate)));
    out.push_str("use std::panic::{catch_unwind, AssertUnwindSafe};\n\n");

    let shim_name = format!("hsh_rs_shim_{}", f.name);
    let mut shim_params: Vec<String> = Vec::new();
    let mut prelude: Vec<String> = Vec::new(); // reconstruction statements
    let mut call_args: Vec<String> = Vec::new();

    for p in &f.params {
        let rty = hsh_type_to_rust_native(&p.ty);
        match &rty {
            RsTy::Str => {
                // One pointer parameter, null-terminated — matches
                // `htype_to_llvm`'s `string` mapping exactly (see the ABI
                // note above `generate_shim`). `CStr` stops at the same
                // NUL byte H#'s own `hsh_strlen` does, so this is a
                // faithful reconstruction of what H# actually passes.
                shim_params.push(format!("{n}_ptr: *const std::os::raw::c_char", n = p.name));
                prelude.push(format!(
                    "        let {n} = unsafe {{ std::ffi::CStr::from_ptr({n}_ptr) }}.to_str().unwrap_or(\"\");",
                    n = p.name));
                call_args.push(p.name.clone());
            }
            _ => {
                shim_params.push(format!("{}: {}", p.name, c_flat_type(&rty)));
                call_args.push(p.name.clone());
            }
        }
    }

    // Option<T>/Result<T,E>/&[u8]/Vec<T> returns are rejected above before
    // we get here, so this is just string-vs-primitive at this point.
    let flat_ret = match &ret_rs {
        RsTy::Str => "*mut std::os::raw::c_char".to_string(),
        other => c_flat_type(other).to_string(),
    };
    let extra_out_param = false;

    out.push_str(&format!("#[no_mangle]\npub extern \"C\" fn {}({}) -> {} {{\n",
        shim_name, shim_params.join(", "), flat_ret));
    for line in &prelude { out.push_str(line); out.push('\n'); }
    out.push_str("    let __result = catch_unwind(AssertUnwindSafe(|| {\n");
    out.push_str(&format!("        __user::{}({})\n", f.name, call_args.join(", ")));
    out.push_str("    }));\n\n");
    out.push_str("    match __result {\n");
    out.push_str("        Ok(__v) => {\n");
    out.push_str(&render_success_arm(&ret_rs, extra_out_param));
    out.push_str("        }\n");
    out.push_str("        Err(_panic_payload) => {\n");
    out.push_str("            // A Rust panic must never unwind across this `extern \"C\"`\n");
    out.push_str("            // frame into H#'s LLVM-generated code — that's undefined\n");
    out.push_str("            // behavior. Convert it into H#'s sentinel failure value.\n");
    out.push_str(&render_panic_arm(&ret_rs, extra_out_param));
    out.push_str("        }\n");
    out.push_str("    }\n");
    out.push_str("}\n");

    Ok(out)
}

fn render_success_arm(ret_rs: &RsTy, _extra_out_param: bool) -> String {
    match ret_rs {
        RsTy::Unit => "            return ();\n".to_string(),
        RsTy::Str => {
            // Null-terminated, freed via `CString::from_raw` (no stored
            // length needed — matches H#'s own `string` convention exactly,
            // see the ABI note above `generate_shim`).
            "            let __s = __v.to_string();\n".to_string()
                + "            let __c = std::ffi::CString::new(__s).unwrap_or_default();\n"
                + "            return __c.into_raw(); // H# runtime frees via hsh_rs_free_string\n"
        }
        _ => "            return __v;\n".to_string(),
    }
}

fn render_panic_arm(ret_rs: &RsTy, _extra_out_param: bool) -> String {
    match ret_rs {
        RsTy::Unit => "            return ();\n".to_string(),
        RsTy::Str => "            return std::ptr::null_mut();\n".to_string(),
        RsTy::F32 | RsTy::F64 => "            return -1.0 as _;\n".to_string(),
        _ => "            return Default::default();\n".to_string(),
    }
}

fn sanitize_ident(s: &str) -> String {
    s.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect()
}

/// A tiny paired free function for whatever `generate_shim` heap-allocates
/// on the Rust side (`CString::into_raw` above) — H#'s runtime must call
/// this instead of its own C `free()`, since the allocation was made with
/// Rust's global allocator, not libc's, on targets where they differ.
/// Matches `CString::into_raw`'s contract exactly: no stored length needed,
/// `CString::from_raw` re-scans for the NUL terminator itself.
pub fn generate_free_fn() -> &'static str {
    "#[no_mangle]\npub extern \"C\" fn hsh_rs_free_string(ptr: *mut std::os::raw::c_char) {\n    \
     if ptr.is_null() { return; }\n    \
     unsafe { drop(std::ffi::CString::from_raw(ptr)); }\n}\n"
}
