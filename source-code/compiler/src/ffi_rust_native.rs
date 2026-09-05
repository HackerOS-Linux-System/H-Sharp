use hsharp_parser::ast::{TypeExpr, StructField};
use crate::ffi::ExternFn;
use std::collections::HashMap;

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

/// True for the element types `bytes`/`Vec<T>` marshaling (below) knows how
/// to reconstruct a slice of — i.e. everything with a fixed-width, self-
/// contained flat representation. Deliberately excludes `Str`/`Vec`/
/// `Option`/`Result`/`Opaque` elements: a `Vec<String>`, `Vec<Vec<T>>`, etc.
/// would need a real nested marshaling scheme (each element itself needing
/// its own length/tag), which is a different, bigger feature than "read N
/// fixed-size elements out of a flat buffer".
fn is_flat_primitive(ty: &RsTy) -> bool {
    matches!(ty,
        RsTy::Bool | RsTy::I8 | RsTy::U8 | RsTy::I16 | RsTy::U16 |
        RsTy::I32 | RsTy::U32 | RsTy::I64 | RsTy::U64 |
        RsTy::Isize | RsTy::Usize | RsTy::F32 | RsTy::F64)
}

/// True for the `T` inside `Option<T>` that the sentinel convention (see
/// `generate_shim`'s ABI note on `Option`/`Result`) knows an unambiguous
/// "absent" value for: any flat primitive (sentinel `0`/`0.0`) or `Str`
/// (sentinel: null pointer, which is genuinely unambiguous, unlike the
/// numeric case — see that note). `Option<Vec<_>>`, `Option<Option<_>>`,
/// and `Option<Opaque>` are excluded, same rationale as `is_flat_primitive`.
fn is_sentinel_representable(ty: &RsTy) -> bool {
    is_flat_primitive(ty) || matches!(ty, RsTy::Str)
}

/// The literal Rust expression for "absent"/"error" in the flat, sentinel-
/// based encoding this shim uses for `Option<T>`/`Result<T, E>` — see the
/// ABI note on `generate_shim`. Matches H#'s own existing convention of a
/// single flat `i64`/pointer value per `Optional<T>` (`nil` == `0`/null;
/// see `llvm_types::htype_to_llvm`'s `TypeExpr::Optional(_) => i64`) rather
/// than inventing a separate tag-word scheme the rest of the compiler
/// doesn't actually use.
fn sentinel_expr(ty: &RsTy) -> &'static str {
    match ty {
        RsTy::F32 | RsTy::F64 => "0.0",
        RsTy::Str => "std::ptr::null_mut()",
        _ => "0",
    }
}

/// True when every field of an H# struct is a shape this shim's opaque-
/// by-value flattening (see `generate_shim`'s `RsTy::Opaque` handling)
/// knows how to marshal: a flat primitive or `string` — same restriction
/// as `is_flat_primitive`/`is_sentinel_representable` elsewhere in this
/// file, for the same reason (a field that's itself a struct/array/Option
/// would need real nested marshaling).
fn struct_is_flattenable(fields: &[StructField]) -> bool {
    fields.iter().all(|f| {
        let rty = hsh_type_to_rust_native(&f.ty);
        is_flat_primitive(&rty) || matches!(rty, RsTy::Str)
    })
}

/// Emits the Rust statement(s) that read one struct field out of H#'s
/// boxed-struct runtime representation (a heap array of `int64_t` slots,
/// `hsh_struct_get(ptr, idx)` — see `compiler/runtime/core.c`) and produce
/// a value of the field's real Rust type, bound to `out_var`.
///
/// Numeric fields are a plain narrowing/widening `as` cast (H#'s own
/// codegen — `FnCx::coerce_basic_value` — stores them the same way: a
/// value-preserving int-to-int conversion, not a bitcast). Floats are the
/// one case that's *not* a plain cast: H#'s codegen stores an f32/f64
/// struct field via `build_bit_cast` into the `int64_t` slot (see
/// `coerce_basic_value` in codegen.rs), i.e. the *bit pattern* is
/// preserved, not the numeric value — so reconstructing it needs
/// `f64::from_bits`/`f32::from_bits`, not `as f64`, or the value would be
/// silently corrupted (an `int64_t` holding the bits of `3.14_f64`
/// reinterpreted as an integer and then `as f64`'d back gives garbage).
fn emit_struct_field_read(struct_ptr_var: &str, idx: usize, field: &StructField, out_var: &str) -> String {
    let rty = hsh_type_to_rust_native(&field.ty);
    let raw = format!("unsafe {{ hsh_struct_get({}, {}) }}", struct_ptr_var, idx);
    match rty {
        RsTy::F64 => format!("        let {v} = f64::from_bits(({raw}) as u64);\n", v = out_var, raw = raw),
        RsTy::F32 => format!("        let {v} = f32::from_bits(({raw}) as u32);\n", v = out_var, raw = raw),
        RsTy::Bool => format!("        let {v} = ({raw}) != 0;\n", v = out_var, raw = raw),
        RsTy::Str => format!(
            "        let {v}_ptr = ({raw}) as *const std::os::raw::c_char;\n        let {v} = unsafe {{ std::ffi::CStr::from_ptr({v}_ptr) }}.to_str().unwrap_or(\"\");\n",
            v = out_var, raw = raw),
        RsTy::I8  => format!("        let {v} = ({raw}) as i8;\n",  v = out_var, raw = raw),
        RsTy::U8  => format!("        let {v} = ({raw}) as u8;\n",  v = out_var, raw = raw),
        RsTy::I16 => format!("        let {v} = ({raw}) as i16;\n", v = out_var, raw = raw),
        RsTy::U16 => format!("        let {v} = ({raw}) as u16;\n", v = out_var, raw = raw),
        RsTy::I32 => format!("        let {v} = ({raw}) as i32;\n", v = out_var, raw = raw),
        RsTy::U32 => format!("        let {v} = ({raw}) as u32;\n", v = out_var, raw = raw),
        RsTy::U64 | RsTy::Usize => format!("        let {v} = ({raw}) as u64;\n", v = out_var, raw = raw),
        _ /* I64/Isize */       => format!("        let {v} = {raw};\n", v = out_var, raw = raw),
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
pub fn generate_shim(user_crate: &str, f: &ExternFn, structs: &HashMap<String, Vec<StructField>>) -> Result<String, RustFfiError> {
    let ret_rs = f.return_type.as_ref().map(hsh_type_to_rust_native).unwrap_or(RsTy::Unit);
    let param_rs: Vec<RsTy> = f.params.iter().map(|p| hsh_type_to_rust_native(&p.ty)).collect();

    // ── `bytes`/`Vec<T>` parameters: paired-length convention ──────────────
    // H#'s own LLVM codegen passes `bytes`/`Array`/`Slice` as a bare pointer
    // with no bundled length (see the ABI note below). This shim can still
    // marshal one safely when the H# `extern` signature pairs it with an
    // explicit length parameter named `<name>_len` (any integer type) right
    // there in the declaration — that's a real, already-expressible H#
    // parameter the *caller* passes normally (e.g. `read_chunk(buf, buf.len())`),
    // not anything invented at the ABI level. `data_param_len_idx` maps a
    // data param's index to its paired length param's index;
    // `len_param_consumed` marks length params that are folded into a
    // reconstructed slice rather than forwarded to the user fn on their own.
    let mut data_param_len_idx: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
    let mut len_param_consumed: std::collections::HashSet<usize> = std::collections::HashSet::new();
    for (i, (p, rty)) in f.params.iter().zip(&param_rs).enumerate() {
        let is_flat_seq = matches!(rty, RsTy::Bytes) || matches!(rty, RsTy::Vec(inner) if is_flat_primitive(inner));
        if !is_flat_seq { continue; }
        let expected_len_name = format!("{}_len", p.name);
        if let Some(j) = f.params.iter().position(|q| q.name == expected_len_name) {
            if matches!(param_rs[j], RsTy::I64 | RsTy::U64 | RsTy::Isize | RsTy::Usize | RsTy::I32 | RsTy::U32) {
                data_param_len_idx.insert(i, j);
                len_param_consumed.insert(j);
            }
        }
    }

    // ABI NOTE: H#'s own LLVM codegen (`llvm_types::htype_to_llvm`)
    // represents `string` as exactly one pointer argument — a plain
    // null-terminated C string (`hsh_strlen` scans for the terminator, it
    // doesn't read a stored length) — and `bytes`/`Array`/`Slice` as a bare
    // pointer with *no* bundled length at all, and `Optional<T>` as a
    // single flat value (`nil` == `0`/null; see `is_sentinel_representable`/
    // `sentinel_expr` above). So: `&str` (null-terminated reconstruction),
    // paired-length `bytes`/`Vec<T>` (see above), and sentinel-representable
    // `Option<T>` are all auto-wired; anything else that would need a
    // length or tag this codebase doesn't actually carry at that call site
    // is refused rather than guessed.
    for (i, (p, rty)) in f.params.iter().zip(&param_rs).enumerate() {
        match rty {
            RsTy::Opaque(name) if structs.get(name).map(|fs| struct_is_flattenable(fs)).unwrap_or(false) => {}
            RsTy::Opaque(name) => return Err(RustFfiError::Unsupported(format!(
                "parameter `{}` has type `{}`, which has no known stable layout to \
                 cross the FFI boundary by value — either pass a `ref`/`ref mut` \
                 (opaque pointer) instead, or declare `{}` as an H# `struct` with only \
                 flat-primitive/`string` fields (see `struct_is_flattenable`) so this \
                 shim can flatten it; the real Rust struct on the other side must have \
                 the identical name and public fields in the same order — this shim \
                 mirrors the layout, it doesn't invent one",
                p.name, name, name
            ))),
            RsTy::Bytes | RsTy::Vec(_) if !data_param_len_idx.contains_key(&i) => {
                return Err(RustFfiError::Unsupported(format!(
                    "parameter `{}` (&[u8]/Vec<T>) has no bundled length at the ABI level \
                     this shim can read on its own — H#'s `bytes`/`Array`/`Slice` are bare \
                     pointers. Add a paired `{}_len: int` parameter right after it in the \
                     `extern` signature (and pass the real length at the call site) so this \
                     shim can reconstruct a slice; only element types `is_flat_primitive` \
                     recognizes (bool/ints/floats — not nested `Vec`/`String`/opaque types) \
                     are supported this way",
                    p.name, p.name
                )));
            }
            RsTy::Option(inner) if !is_sentinel_representable(inner) => {
                return Err(RustFfiError::Unsupported(format!(
                    "parameter `{}` is `Option<T>` with a `T` this shim has no unambiguous \
                     sentinel for (only flat primitives and `string` are supported — see \
                     `is_sentinel_representable`); accept the payload type directly plus a \
                     separate `has_value: bool` parameter instead",
                    p.name
                )));
            }
            RsTy::Result(_, err) if !matches!(**err, RsTy::Str) => {
                return Err(RustFfiError::Unsupported(
                    "Result<T, E> parameters are not supported (only Result<T, String> \
                     return values are) — Results only make sense as outcomes, not inputs".into()
                ));
            }
            _ => {}
        }
    }
    match &ret_rs {
        RsTy::Bytes | RsTy::Vec(_) => return Err(RustFfiError::Unsupported(
            "&[u8]/Vec<T> return values have no bundled-length convention on the H# \
             side to read them back with — return `string` (null-terminated, fully \
             supported) instead, or add an explicit `out_len: ref mut int` output \
             parameter and marshal it by hand".to_string()
        )),
        RsTy::Option(inner) | RsTy::Result(inner, _) if !is_sentinel_representable(inner) => {
            return Err(RustFfiError::Unsupported(format!(
                "return type wraps a `{:?}` payload, which this shim has no unambiguous \
                 sentinel for on return (only flat primitives and `string` are supported — \
                 see `is_sentinel_representable`); return the payload type directly and use \
                 a sentinel value (e.g. -1) for the error/None case for now",
                inner
            )));
        }
        RsTy::Opaque(name) => return Err(RustFfiError::Unsupported(format!(
            "return type `{}` would need to cross the FFI boundary by value with no \
             known stable layout on the H# side to receive it into (H#'s codegen only \
             has a single flat `i64` return slot for any `extern` call — see \
             `llvm_types::htype_to_llvm`) — opaque-by-value flattening (see the \
             parameter-side `RsTy::Opaque` handling above) is deliberately only \
             supported for *parameters*, not return values, since a multi-field struct \
             doesn't fit in one flat i64 return slot without new H#-side codegen support \
             this shim generator alone can't add; return a single scalar/`string` field, \
             or write an accessor function per field instead",
            name
        ))),
        _ => {}
    }

    let mut out = String::new();
    out.push_str("// Auto-generated by hsharp's ffi_rust_native shim generator. Do not edit\n");
    out.push_str("// by hand — regenerated on every `hsharp compile` / `bytes build` that sees\n");
    out.push_str("// this `extern [rust]` block. See ffi_rust_native.rs for the generator.\n");
    out.push_str(&format!("extern crate {} as __user;\n\n", sanitize_ident(user_crate)));
    out.push_str("use std::panic::{catch_unwind, AssertUnwindSafe};\n\n");
    // Only declared/linked when at least one param actually needs it (see
    // the `RsTy::Opaque` arm below) — this is the *same* runtime function
    // H#'s own LLVM codegen calls for its native struct-field access
    // (`FnCx::compile_pattern_cond`/struct field reads in codegen.rs), so
    // reusing it here (rather than re-deriving the boxed-struct memory
    // layout by hand) guarantees this shim can never drift out of sync
    // with what H#'s own struct representation actually is.
    let uses_struct_get = f.params.iter().zip(&param_rs)
        .any(|(_, rty)| matches!(rty, RsTy::Opaque(name) if structs.get(name).map(|fs| struct_is_flattenable(fs)).unwrap_or(false)));
    if uses_struct_get {
        out.push_str("extern \"C\" { fn hsh_struct_get(s: i64, idx: i64) -> i64; }\n\n");
    }

    let shim_name = format!("hsh_rs_shim_{}", f.name);
    let mut shim_params: Vec<String> = Vec::new();
    let mut prelude: Vec<String> = Vec::new(); // reconstruction statements
    let mut call_args: Vec<String> = Vec::new();

    for (i, p) in f.params.iter().enumerate() {
        let rty = &param_rs[i];
        if len_param_consumed.contains(&i) {
            // Still a real, separate parameter on the shim's C ABI (H#'s
            // call site passes it as its own argument) — just not
            // forwarded to `__user::<fn>` on its own, since it's folded
            // into the slice reconstructed for its paired data param
            // below instead.
            shim_params.push(format!("{}: {}", p.name, c_flat_type(rty)));
            continue;
        }
        match rty {
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
            RsTy::Bytes | RsTy::Vec(_) => {
                // Paired-length reconstruction — see the
                // `data_param_len_idx` note above `generate_shim`.
                // Guaranteed present by the validation loop above (any
                // param that reached here without a pairing was already
                // rejected), so the `expect` is unreachable in practice,
                // not a real panic risk.
                let len_idx = *data_param_len_idx.get(&i)
                    .expect("bytes/Vec param without a paired length slipped past validation");
                let len_name = &f.params[len_idx].name;
                let elem_rs = match rty { RsTy::Vec(inner) => inner.as_ref().clone(), _ => RsTy::U8 };
                let elem_ty = c_flat_type(&elem_rs);
                shim_params.push(format!("{n}_ptr: *const {t}", n = p.name, t = elem_ty));
                prelude.push(format!(
                    "        let {n} = unsafe {{ std::slice::from_raw_parts({n}_ptr, {l} as usize) }};",
                    n = p.name, l = len_name));
                call_args.push(p.name.clone());
            }
            RsTy::Option(inner) => {
                // Sentinel reconstruction — see `is_sentinel_representable`/
                // `sentinel_expr` and the ABI note above `generate_shim`.
                // Validation already restricted `inner` to a flat
                // primitive or `Str`.
                if matches!(**inner, RsTy::Str) {
                    shim_params.push(format!("{n}_ptr: *const std::os::raw::c_char", n = p.name));
                    prelude.push(format!(
                        "        let {n} = if {n}_ptr.is_null() {{ None }} else {{ Some(unsafe {{ std::ffi::CStr::from_ptr({n}_ptr) }}.to_str().unwrap_or(\"\")) }};",
                        n = p.name));
                } else {
                    let flat = c_flat_type(inner);
                    shim_params.push(format!("{n}: {t}", n = p.name, t = flat));
                    // `0 as bool` isn't valid Rust (only the bool -> int
                    // cast direction is allowed), so `bool`'s sentinel
                    // check needs its own spelling — `false` is the
                    // sentinel there, same idea as `0`/`0.0` elsewhere.
                    let check = if matches!(**inner, RsTy::Bool) {
                        format!("!{n}", n = p.name)
                    } else {
                        format!("{n} == 0 as {t}", n = p.name, t = flat)
                    };
                    prelude.push(format!(
                        "        let {n} = if {check} {{ None }} else {{ Some({n}) }};",
                        n = p.name, check = check));
                }
                call_args.push(p.name.clone());
            }
            RsTy::Opaque(name) => {
                // Flattened struct-by-value — see `struct_is_flattenable`/
                // `emit_struct_field_read` and the validation error above
                // for the exact convention this relies on. H#'s own
                // codegen already passes *any* user-named type as a
                // single `i64` (the boxed struct pointer — see
                // `llvm_types::htype_to_llvm`'s `_ => i64` fallback for
                // `TypeExpr::Named`), so the shim's own parameter list
                // doesn't need to change shape at all here — only what
                // this shim does *with* that one i64 changes.
                let fields = structs.get(name).expect("validated flattenable struct missing from `structs`");
                shim_params.push(format!("{n}: i64", n = p.name));
                for (fi, field) in fields.iter().enumerate() {
                    let var = format!("{n}_{f}", n = p.name, f = field.name);
                    prelude.push(emit_struct_field_read(&p.name, fi, field, &var).trim_end().to_string());
                }
                let ctor_fields = fields.iter()
                    .map(|field| format!("{f}: {n}_{f}", n = p.name, f = field.name))
                    .collect::<Vec<_>>().join(", ");
                prelude.push(format!("        let {n} = __user::{ty} {{ {fs} }};", n = p.name, ty = name, fs = ctor_fields));
                call_args.push(p.name.clone());
            }
            _ => {
                shim_params.push(format!("{}: {}", p.name, c_flat_type(rty)));
                call_args.push(p.name.clone());
            }
        }
    }

    // &[u8]/Vec<T> returns are rejected above before we get here (still no
    // bundled-length convention on return), so this is string/primitive/
    // sentinel-wrapped-Option-or-Result at this point.
    let flat_ret = match &ret_rs {
        RsTy::Str => "*mut std::os::raw::c_char".to_string(),
        RsTy::Option(inner) | RsTy::Result(inner, _) => match **inner {
            RsTy::Str => "*mut std::os::raw::c_char".to_string(),
            _ => c_flat_type(inner).to_string(),
        },
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
        // Sentinel encoding (see `sentinel_expr`/the ABI note above
        // `generate_shim`): `Some(x)`/`Ok(x)` -> the payload, flattened the
        // same way a bare (non-Option) return of that type would be;
        // `None`/`Err(e)` -> the sentinel. The `Err` message isn't silently
        // dropped — H#'s flat ABI has no channel to carry it back today, so
        // it's logged to stderr instead of vanishing, which at least keeps
        // it visible while developing/debugging the binding.
        RsTy::Option(inner) | RsTy::Result(inner, _) => {
            let is_result = matches!(ret_rs, RsTy::Result(_, _));
            let (present_pat, absent_pat) = if is_result { ("Ok(__x)", "Err(__e)") } else { ("Some(__x)", "None") };
            let mut s = format!("            match __v {{\n                {} => {{\n", present_pat);
            match **inner {
                RsTy::Str => {
                    s.push_str("                    let __s = __x.to_string();\n");
                    s.push_str("                    let __c = std::ffi::CString::new(__s).unwrap_or_default();\n");
                    s.push_str("                    return __c.into_raw();\n");
                }
                _ => s.push_str("                    return __x;\n"),
            }
            s.push_str(&format!("                }}\n                {} => {{\n", absent_pat));
            if is_result {
                s.push_str("                    eprintln!(\"extern [rust] call returned Err: {:?}\", __e);\n");
            }
            s.push_str(&format!("                    return {};\n                }}\n            }}\n", sentinel_expr(inner)));
            s
        }
        _ => "            return __v;\n".to_string(),
    }
}

fn render_panic_arm(ret_rs: &RsTy, _extra_out_param: bool) -> String {
    match ret_rs {
        RsTy::Unit => "            return ();\n".to_string(),
        RsTy::Str => "            return std::ptr::null_mut();\n".to_string(),
        RsTy::F32 | RsTy::F64 => "            return -1.0 as _;\n".to_string(),
        RsTy::Option(inner) | RsTy::Result(inner, _) => format!("            return {};\n", sentinel_expr(inner)),
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
