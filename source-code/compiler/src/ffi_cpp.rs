use hsharp_parser::ast::{TypeExpr, StructField};
use crate::ffi::ExternFn;
use std::collections::HashMap;

// ─── Public entry points ──────────────────────────────────────────────────────

/// A C++ symbol path, e.g. `["hackeros", "Config", "load"]` for
/// `hackeros::Config::load`. H# spells this as a dotted/`::`-joined name in
/// the `extern` header; the parser hands it to us pre-split.
#[derive(Debug, Clone, Default)]
pub struct CppPath {
    pub namespaces: Vec<String>,
    pub class_name:  Option<String>,
    pub fn_name:     String,
    pub is_const:    bool, // `const` member function
}

#[derive(Debug, Clone, PartialEq)]
pub enum CppTy {
    Void,
    Bool,
    Char,
    I8, I16, I32, I64,
    U8, U16, U32, U64,
    F32, F64,
    Ptr(Box<CppTy>, bool /*is_const*/),
    Ref(Box<CppTy>, bool /*is_const*/),
    StdString,
    StdVector(Box<CppTy>),
    StdOptional(Box<CppTy>),
    Opaque(String), // user type we can only pass by opaque pointer
}

#[derive(Debug)]
pub enum CppFfiError {
    Unsupported(String),
}

impl std::fmt::Display for CppFfiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CppFfiError::Unsupported(s) => write!(f, "extern [c++]: {}", s),
        }
    }
}

// ─── H# type → CppTy ───────────────────────────────────────────────────────────

/// Maps an H# `TypeExpr` to the *real* C++ type it should bind to, using the
/// `Generic("vector"/"optional", [inner])` / `Named("string")` shapes the
/// parser already produces for these — as opposed to `ffi.rs::type_to_c`,
/// which flattens everything to a pointer immediately.
pub fn hsh_type_to_cpp(ty: &TypeExpr) -> CppTy {
    match ty {
        TypeExpr::Void   => CppTy::Void,
        TypeExpr::Bool   => CppTy::Bool,
        TypeExpr::I8     => CppTy::I8,
        TypeExpr::I16    => CppTy::I16,
        TypeExpr::I32    => CppTy::I32,
        TypeExpr::I64    => CppTy::I64,
        TypeExpr::U8     => CppTy::U8,
        TypeExpr::U16    => CppTy::U16,
        TypeExpr::U32    => CppTy::U32,
        TypeExpr::U64    => CppTy::U64,
        TypeExpr::F32    => CppTy::F32,
        TypeExpr::F64    => CppTy::F64,
        TypeExpr::String => CppTy::StdString,
        TypeExpr::Bytes  => CppTy::StdVector(Box::new(CppTy::U8)),
        TypeExpr::Ref(inner)    => CppTy::Ref(Box::new(hsh_type_to_cpp(inner)), true),
        TypeExpr::RefMut(inner) => CppTy::Ref(Box::new(hsh_type_to_cpp(inner)), false),
        TypeExpr::Optional(inner) => CppTy::StdOptional(Box::new(hsh_type_to_cpp(inner))),
        TypeExpr::Array(inner) | TypeExpr::Slice(inner, _) =>
            CppTy::StdVector(Box::new(hsh_type_to_cpp(inner))),
        TypeExpr::Generic(n, args) if n == "vector" && args.len() == 1 =>
            CppTy::StdVector(Box::new(hsh_type_to_cpp(&args[0]))),
        TypeExpr::Generic(n, args) if n == "optional" && args.len() == 1 =>
            CppTy::StdOptional(Box::new(hsh_type_to_cpp(&args[0]))),
        TypeExpr::Named(n) => named_to_cpp(n),
        _ => CppTy::Opaque("void".to_string()),
    }
}

fn named_to_cpp(n: &str) -> CppTy {
    match n {
        "i8"  => CppTy::I8,  "u8"  => CppTy::U8,
        "i16" => CppTy::I16, "u16" => CppTy::U16,
        "i32" => CppTy::I32, "u32" => CppTy::U32,
        "i64" | "int" | "isize" => CppTy::I64,
        "u64" | "uint" | "usize" => CppTy::U64,
        "f32" => CppTy::F32, "f64" => CppTy::F64,
        "bool" => CppTy::Bool,
        "char" => CppTy::Char,
        "string" | "str" => CppTy::StdString,
        "void" => CppTy::Void,
        other => CppTy::Opaque(other.to_string()),
    }
}

// ─── Itanium name mangling ─────────────────────────────────────────────────────

/// Mangle a C++ symbol per the Itanium C++ ABI, for the subset described in
/// the module docs above. Returns e.g. `_ZN8hackeros6Config4loadEv` for
/// `hackeros::Config::load()`.
pub fn mangle(path: &CppPath, params: &[CppTy]) -> Result<String, CppFfiError> {
    let mut out = String::from("_Z");
    let has_qualified_name = !path.namespaces.is_empty() || path.class_name.is_some();

    if has_qualified_name {
        out.push('N');
        if path.is_const {
            out.push('K');
        }
        for ns in &path.namespaces {
            out.push_str(&format!("{}{}", ns.len(), ns));
        }
        if let Some(c) = &path.class_name {
            out.push_str(&format!("{}{}", c.len(), c));
        }
        out.push_str(&format!("{}{}", path.fn_name.len(), path.fn_name));
        out.push('E');
    } else {
        out.push_str(&format!("{}{}", path.fn_name.len(), path.fn_name));
    }

    if params.is_empty() {
        out.push('v');
    } else {
        // Itanium substitution compression (S_, S0_, S1_...) is a
        // correctness requirement for repeated compound types, not just an
        // optimization — real C++ mangled names for e.g.
        // `f(std::string, std::string)` rely on it
        // (`_Z1fNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEES2_`,
        // not the type spelled out twice). We track substitutions the same
        // way `mangle_one` needs them.
        let mut subs: Vec<String> = Vec::new();
        for p in params {
            out.push_str(&mangle_one(p, &mut subs)?);
        }
    }
    Ok(out)
}

fn mangle_one(ty: &CppTy, subs: &mut Vec<String>) -> Result<String, CppFfiError> {
    // Returns this type's mangled fragment; registers it (and any inner
    // compound type) into `subs` for later substitution back-references.
    let frag = match ty {
        CppTy::Void  => "v".to_string(),
        CppTy::Bool  => "b".to_string(),
        CppTy::Char  => "c".to_string(),
        CppTy::I8    => "a".to_string(),
        CppTy::U8    => "h".to_string(),
        CppTy::I16   => "s".to_string(),
        CppTy::U16   => "t".to_string(),
        CppTy::I32   => "i".to_string(),
        CppTy::U32   => "j".to_string(),
        CppTy::I64   => "x".to_string(),
        CppTy::U64   => "y".to_string(),
        CppTy::F32   => "f".to_string(),
        CppTy::F64   => "d".to_string(),
        CppTy::Ptr(inner, is_const) => {
            let inner_m = mangle_one(inner, subs)?;
            let with_const = if *is_const { format!("PK{}", inner_m) } else { format!("P{}", inner_m) };
            return Ok(register_sub(&with_const, subs));
        }
        CppTy::Ref(inner, is_const) => {
            let inner_m = mangle_one(inner, subs)?;
            let with_const = if *is_const { format!("RK{}", inner_m) } else { format!("R{}", inner_m) };
            return Ok(register_sub(&with_const, subs));
        }
        CppTy::StdString => {
            // libstdc++'s std::string is std::__cxx11::basic_string<char,
            // std::char_traits<char>, std::allocator<char>> — this is the
            // real, GCC-ABI-tag-aware mangling (not a placeholder), because
            // getting this one wrong is the single most common reason a
            // hand-rolled `extern [c++]` binding fails to link.
            let frag = "NSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEE".to_string();
            return Ok(register_sub(&frag, subs));
        }
        CppTy::StdVector(inner) => {
            let inner_m = mangle_one(inner, subs)?;
            let frag = format!("St6vectorI{}SaI{}EE", inner_m, inner_m);
            return Ok(register_sub(&frag, subs));
        }
        CppTy::StdOptional(inner) => {
            let inner_m = mangle_one(inner, subs)?;
            let frag = format!("St8optionalI{}E", inner_m);
            return Ok(register_sub(&frag, subs));
        }
        CppTy::Opaque(name) => {
            // Mangles as a plain (global-namespace) user-defined-type
            // fragment — Itanium ABI: length-prefixed name, same shape as
            // the namespace/class-name fragments in `mangle()`'s
            // qualified-name path above. Only reached with a real,
            // meaningful target layout when the caller is `generate_shim`,
            // which validates *before* calling `mangle()` that any
            // `CppTy::Opaque` still present here is backed by a known H#
            // `struct` whose fields are all flattenable (see
            // `struct_is_flattenable_cpp`) — i.e. this always mangles as
            // if `name` names a real, ordinary (non-template,
            // non-namespaced) C++ class/struct passed by value, because
            // by the time we get here that's the only case `generate_shim`
            // still lets through.
            let frag = format!("{}{}", name.len(), name);
            return Ok(register_sub(&frag, subs));
        }
    };
    Ok(frag)
}

/// Itanium substitution table: once a compound type fragment has been
/// emitted, later occurrences of the *identical* fragment become a
/// back-reference (`S_`, `S0_`, `S1_`, ...) instead of being spelled out
/// again. Only compound fragments (P/R/std:: types) are substitutable —
/// bare builtins (`i`, `d`, `b`, ...) never are, per the ABI spec.
fn register_sub(frag: &str, subs: &mut Vec<String>) -> String {
    if let Some(idx) = subs.iter().position(|s| s == frag) {
        return if idx == 0 { "S_".to_string() } else { format!("S{}_", idx - 1) };
    }
    subs.push(frag.to_string());
    frag.to_string()
}

// ─── Generated shim (the part hand-written extern "C" bindings can't do) ──────

/// IMPORTANT ABI NOTE: H#'s own LLVM codegen (`llvm_types::htype_to_llvm`)
/// represents `string` as exactly one pointer argument — a plain
/// null-terminated C string (`hsh_strlen` is a `strlen`-style scan, not a
/// stored-length read), not a `(ptr, len)` pair. The shim below matches that
/// *exactly* (one `const char*` parameter, reconstructed via `strlen`) —
/// deliberately, not as a simplification of "the real" ABI. Do not add a
/// companion `_len` parameter to *this* convention without also changing
/// `build_extern_fn_type` on the H# codegen side, or the two will disagree
/// on argument count and the call will be broken at the LLVM level.
///
/// `std::vector<T>`/`std::optional<T>` marshaling: paired-length and
/// sentinel conventions, mirroring `ffi_rust_native.rs`'s
/// `is_flat_primitive`/`is_sentinel_representable`/`sentinel_expr` — see
/// those for the rationale (only fixed-width, self-contained element/
/// payload types are supported; nested `std::vector`/`std::optional`/
/// opaque types would need real nested marshaling, a bigger feature).
fn is_flat_primitive_cpp(ty: &CppTy) -> bool {
    matches!(ty,
        CppTy::Bool | CppTy::Char |
        CppTy::I8 | CppTy::U8 | CppTy::I16 | CppTy::U16 |
        CppTy::I32 | CppTy::U32 | CppTy::I64 | CppTy::U64 |
        CppTy::F32 | CppTy::F64)
}

fn is_sentinel_representable_cpp(ty: &CppTy) -> bool {
    is_flat_primitive_cpp(ty) || matches!(ty, CppTy::StdString)
}

/// The C++ "absent"/"error" sentinel literal for a given payload type —
/// same rationale and same `0`/null convention as
/// `ffi_rust_native.rs::sentinel_expr` (matching H#'s own `nil == 0/null`
/// `Optional<T>` representation, see that function's doc comment).
fn sentinel_expr_cpp(ty: &CppTy) -> String {
    match ty {
        CppTy::F32 | CppTy::F64 => "0".to_string(),
        CppTy::StdString => "nullptr".to_string(),
        CppTy::Bool => "false".to_string(),
        _ => "0".to_string(),
    }
}

/// True when every field of an H# struct is a shape this shim's opaque-
/// by-value flattening (see `generate_shim`'s `CppTy::Opaque` handling)
/// knows how to marshal — mirrors `ffi_rust_native.rs::struct_is_flattenable`
/// exactly (same restriction, same reason: nested struct/vector/optional
/// fields would need real nested marshaling).
fn struct_is_flattenable_cpp(fields: &[StructField]) -> bool {
    fields.iter().all(|f| {
        let cty = hsh_type_to_cpp(&f.ty);
        is_flat_primitive_cpp(&cty) || matches!(cty, CppTy::StdString)
    })
}

/// C++ counterpart of `ffi_rust_native.rs::emit_struct_field_read` — reads
/// one field out of H#'s boxed-struct runtime representation via the
/// *same* `hsh_struct_get` runtime function H#'s own codegen uses (see
/// that function's doc comment for why calling the real runtime function
/// beats re-deriving the memory layout by hand), and produces a value of
/// the field's real C++ type, bound to `out_var`.
///
/// Floats need `std::memcpy` rather than a `static_cast`/C-style cast:
/// H#'s codegen stores an f32/f64 struct field via LLVM `bitcast` into the
/// `int64_t` slot (bit pattern preserved, not the numeric value — see the
/// Rust-side doc comment this mirrors), so reconstructing with a numeric
/// cast would silently corrupt the value. `memcpy` into a same-size
/// destination is the portable, strict-aliasing-safe way to reinterpret
/// the bits in C++ (pre-C++20; `std::bit_cast` isn't assumed available).
fn emit_struct_field_read_cpp(struct_ptr_var: &str, idx: usize, field: &StructField, out_var: &str) -> String {
    let cty = hsh_type_to_cpp(&field.ty);
    let raw = format!("hsh_struct_get({}, {})", struct_ptr_var, idx);
    match cty {
        CppTy::F64 => format!(
            "        int64_t {v}_bits = {raw}; double {v}; std::memcpy(&{v}, &{v}_bits, sizeof(double));\n",
            v = out_var, raw = raw),
        CppTy::F32 => format!(
            "        int32_t {v}_bits = static_cast<int32_t>({raw}); float {v}; std::memcpy(&{v}, &{v}_bits, sizeof(float));\n",
            v = out_var, raw = raw),
        CppTy::Bool => format!("        bool {v} = ({raw}) != 0;\n", v = out_var, raw = raw),
        CppTy::StdString => format!(
            "        const char* {v}_ptr = reinterpret_cast<const char*>({raw});\n        std::string {v}({v}_ptr ? {v}_ptr : \"\");\n",
            v = out_var, raw = raw),
        _ => format!("        {t} {v} = static_cast<{t}>({raw});\n", t = cpp_type_name(&cty), v = out_var, raw = raw),
    }
}

/// Generates a real, compilable C++ translation unit: a `noexcept`
/// `extern "C"` entry point per extern fn that
///   1. reconstructs `std::string`/`std::vector<T>`/`std::optional<T>` from
///      the flat (ptr, len) / (ptr, len, has_value) pairs H#'s codegen
///      already knows how to pass,
///   2. calls the *real*, mangled C++ function (declared via a forward
///      declaration using the exact mangled symbol from `mangle()`, so no
///      header from the target library is required),
///   3. wraps the call in `try/catch (...)`, because an uncaught C++
///      exception unwinding across an `extern "C"` frame into H#'s LLVM-
///      generated code is undefined behavior — the shim converts any
///      exception into a sentinel error return instead,
///   4. converts the C++ return value back to the flat representation.
///
/// H#'s own codegen only ever calls `hsh_cpp_shim_<fn_name>`, a plain
/// `int64_t/double/pointer`-only C ABI function — all the C++-specific
/// complexity lives in this generated `.cpp` file, compiled by the H# build
/// pipeline (`ffi_linker`) with the user's C++ compiler, not hand-maintained.
pub fn generate_shim(path: &CppPath, f: &ExternFn, structs: &HashMap<String, Vec<StructField>>) -> Result<String, CppFfiError> {
    let ret_cpp: CppTy = f.return_type.as_ref().map(hsh_type_to_cpp).unwrap_or(CppTy::Void);
    let param_cpps: Vec<CppTy> = f.params.iter().map(|p| hsh_type_to_cpp(&p.ty)).collect();

    // ── `std::vector<T>` parameters: paired-length convention ──────────────
    // Mirrors `ffi_rust_native.rs::generate_shim`'s `data_param_len_idx` —
    // see that function's doc comment for the full rationale. `bytes`/
    // `Array`/`Slice` in the H# `extern` signature map to `std::vector<T>`
    // here (`hsh_type_to_cpp`), and are only auto-marshaled when paired
    // with an explicit `<name>_len: int` parameter the H# call site passes
    // for real (not an invented ABI concept).
    let mut data_param_len_idx: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
    let mut len_param_consumed: std::collections::HashSet<usize> = std::collections::HashSet::new();
    for (i, (p, cty)) in f.params.iter().zip(&param_cpps).enumerate() {
        let elem = match cty { CppTy::StdVector(inner) => Some(inner.as_ref()), _ => None };
        let Some(elem) = elem else { continue };
        if !is_flat_primitive_cpp(elem) { continue; }
        let expected_len_name = format!("{}_len", p.name);
        if let Some(j) = f.params.iter().position(|q| q.name == expected_len_name) {
            if matches!(param_cpps[j], CppTy::I64 | CppTy::U64 | CppTy::I32 | CppTy::U32) {
                data_param_len_idx.insert(i, j);
                len_param_consumed.insert(j);
            }
        }
    }

    // The *real* target function's mangled symbol must be computed from
    // its actual, idiomatic C++ signature — e.g. `std::vector<int32_t>
    // sum_vec(std::vector<int32_t> v)`, not `sum_vec(std::vector<int32_t>,
    // int64_t)`. The paired `_len` parameter is a shim-only reconstruction
    // aid (see above); it's never part of the real function's own
    // parameter list, so it's excluded here — using the full flat
    // `param_cpps` (with the length param still in it) to mangle would
    // compute the wrong symbol *and* leave the forward declaration's
    // arity mismatched against the actual call the shim body makes below.
    let logical_param_cpps: Vec<CppTy> = param_cpps.iter().enumerate()
        .filter(|(i, _)| !len_param_consumed.contains(i))
        .map(|(_, t)| t.clone())
        .collect();
    let mangled = mangle(path, &logical_param_cpps)?;

    for (i, (p, cty)) in f.params.iter().zip(&param_cpps).enumerate() {
        match cty {
            CppTy::StdVector(_) if !data_param_len_idx.contains_key(&i) => {
                return Err(CppFfiError::Unsupported(format!(
                    "parameter `{}` (std::vector<T>) has no bundled length at the ABI \
                     level this shim can read on its own — add a paired `{}_len: int` \
                     parameter right after it in the `extern` signature (and pass the \
                     real length at the call site) so this shim can reconstruct a \
                     std::vector; only fixed-width element types \
                     (`is_flat_primitive_cpp`) are supported this way",
                    p.name, p.name
                )));
            }
            CppTy::StdOptional(inner) if !is_sentinel_representable_cpp(inner) => {
                return Err(CppFfiError::Unsupported(format!(
                    "parameter `{}` is std::optional<T> with a T this shim has no \
                     unambiguous sentinel for (only fixed-width scalars and \
                     std::string are supported — see `is_sentinel_representable_cpp`); \
                     accept the payload type directly plus a separate `has_value: bool` \
                     parameter instead",
                    p.name
                )));
            }
            CppTy::Opaque(name) if !structs.get(name).map(|fs| struct_is_flattenable_cpp(fs)).unwrap_or(false) => {
                return Err(CppFfiError::Unsupported(format!(
                    "parameter `{}` has opaque/user type `{}`, which has no known \
                     stable layout to cross the FFI boundary by value — either pass a \
                     `ref`/`ref mut` (pointer) instead, or declare `{}` as an H# \
                     `struct` with only fixed-width/`string` fields (see \
                     `struct_is_flattenable_cpp`) so this shim can flatten it; the real \
                     C++ struct/class on the other side must have the identical name \
                     (global namespace) and members in the same declared order — this \
                     shim mirrors the layout, it doesn't invent one",
                    p.name, name, name
                )));
            }
            _ => {}
        }
    }
    match &ret_cpp {
        CppTy::StdVector(_) => return Err(CppFfiError::Unsupported(
            "std::vector<T> return values have no bundled-length convention on the H# \
             side to read them back with — return std::string (supported) instead, or \
             add an explicit `out_len: ref mut int` output parameter and marshal it by \
             hand".to_string()
        )),
        CppTy::StdOptional(inner) if !is_sentinel_representable_cpp(inner) => {
            return Err(CppFfiError::Unsupported(
                "std::optional<T> return value wraps a T this shim has no unambiguous \
                 sentinel for on return (only fixed-width scalars and std::string are \
                 supported — see `is_sentinel_representable_cpp`); return the payload \
                 type directly and use a sentinel value (e.g. -1) for the empty case \
                 for now".to_string()
            ));
        }
        CppTy::Opaque(name) => return Err(CppFfiError::Unsupported(format!(
            "return type `{}` would need to cross the FFI boundary by value with no \
             known stable layout on the H# side to receive it into (H#'s codegen only \
             has a single flat `i64` return slot for any `extern` call — see \
             `llvm_types::htype_to_llvm`) — opaque-by-value flattening (see the \
             parameter-side `CppTy::Opaque` handling above) is deliberately only \
             supported for *parameters*, not return values: a multi-field struct \
             returned by value uses a *different* platform calling convention (e.g. \
             SysV register-pair or hidden-pointer return) than the flat `i64` H#'s \
             codegen expects at the call site, so this would silently miscompile rather \
             than just fail to build, unlike the equivalent Rust-side case. Return a \
             single scalar/std::string field, or write an accessor function per field \
             instead",
            name
        ))),
        _ => {}
    }

    let mut out = String::new();
    out.push_str("// Auto-generated by hsharp's ffi_cpp shim generator. Do not edit by hand —\n");
    out.push_str("// regenerated on every `hsharp compile` / `bytes build` that sees this\n");
    out.push_str("// `extern [c++]` block. See ffi_cpp.rs for the generator.\n");
    out.push_str("#include <cstdint>\n#include <cstring>\n#include <cstdlib>\n#include <string>\n#include <vector>\n#include <optional>\n#include <new>\n\n");
    // Only declared/linked when at least one param actually needs it (see
    // the `CppTy::Opaque` arm below) — the *same* runtime function H#'s
    // own LLVM codegen calls for its native struct-field access, reused
    // here rather than re-deriving the boxed-struct memory layout by hand
    // (see `emit_struct_field_read_cpp`'s doc comment).
    let uses_struct_get = f.params.iter().zip(&param_cpps)
        .any(|(_, cty)| matches!(cty, CppTy::Opaque(name) if structs.get(name).map(|fs| struct_is_flattenable_cpp(fs)).unwrap_or(false)));
    if uses_struct_get {
        out.push_str("extern \"C\" int64_t hsh_struct_get(int64_t s, int64_t idx);\n\n");
    }

    // Locally-defined mirror struct(s) for every opaque-by-value parameter
    // — the shim needs a *complete* type (known size/layout) to pass a
    // `Point` by value or aggregate-initialize `Point p{x, y};`, so it
    // can't get away with only forward-declaring `struct Point;` the way
    // it does for the target *function* (which only needs the mangled
    // name, not a header). This struct is standard-layout (only
    // fixed-width scalar/`std::string` members, no virtual functions —
    // guaranteed by `struct_is_flattenable_cpp`), and its members are
    // emitted in the exact same order as the H# `struct` declaration —
    // matching field order (documented in the validation error above) is
    // what makes this *nominally different* `Point` type ABI-compatible
    // (same size/alignment/offsets) with the real target's own `Point`,
    // even though they're technically distinct types in different
    // translation units — mangled-symbol linkage only cares about layout
    // compatibility here, not nominal type identity.
    let mut emitted_structs: std::collections::HashSet<String> = std::collections::HashSet::new();
    for cty in param_cpps.iter().chain(std::iter::once(&ret_cpp)) {
        if let CppTy::Opaque(name) = cty {
            if emitted_structs.contains(name) { continue; }
            if let Some(fields) = structs.get(name) {
                if struct_is_flattenable_cpp(fields) {
                    out.push_str(&format!("struct {} {{\n", name));
                    for fld in fields {
                        out.push_str(&format!("    {} {};\n", cpp_type_name(&hsh_type_to_cpp(&fld.ty)), fld.name));
                    }
                    out.push_str("};\n\n");
                    emitted_structs.insert(name.clone());
                }
            }
        }
    }

    // Forward-declare the real target symbol at its exact mangled name so we
    // don't need the target library's header — only its compiled object/lib.
    out.push_str(&format!(
        "extern \"C\" {} {}({});\n",
        cpp_type_name(&ret_cpp), mangled,
        logical_param_cpps.iter().map(|t| cpp_type_name(t)).collect::<Vec<_>>().join(", ")
    ));
    out.push_str(&format!("// ^ real symbol, reconstructed via Itanium mangling of:\n//   {}\n\n", describe(path, &logical_param_cpps)));

    // Shim signature: flat C ABI only (pointers + fixed-width ints/floats),
    // exactly what H#'s codegen already emits calls with for any `extern`.
    let shim_name = format!("hsh_cpp_shim_{}", f.name);
    let mut shim_params: Vec<String> = Vec::new();
    for (i, p) in f.params.iter().enumerate() {
        let cty = &param_cpps[i];
        if len_param_consumed.contains(&i) {
            // Real, separate flat param on the shim's own C ABI (H#'s call
            // site passes it as its own argument) — folded into the
            // std::vector reconstruction for its paired data param below,
            // not forwarded to the real function on its own.
            shim_params.push(format!("{} {}", cpp_type_name(cty), p.name));
            continue;
        }
        match cty {
            CppTy::StdString => shim_params.push(format!("const char* {}_ptr", p.name)),
            CppTy::StdVector(inner) => {
                shim_params.push(format!("const {}* {}_ptr", cpp_type_name(inner), p.name));
            }
            CppTy::StdOptional(inner) if matches!(**inner, CppTy::StdString) => {
                shim_params.push(format!("const char* {}_ptr", p.name));
            }
            CppTy::StdOptional(inner) => {
                shim_params.push(format!("{} {}", cpp_type_name(inner), p.name));
            }
            CppTy::Opaque(_) => {
                // Boxed-struct pointer, bit-cast to an `int64_t` — matches
                // `llvm_types::htype_to_llvm`'s existing fallback for any
                // user-named type exactly, so (like the Rust side) no
                // change is needed to what H#'s codegen actually passes
                // at the call site; only what this shim does with it.
                shim_params.push(format!("int64_t {}", p.name));
            }
            _ => shim_params.push(format!("{} {}", cpp_type_name(cty), p.name)),
        }
    }
    let flat_ret = match &ret_cpp {
        CppTy::StdString => "const char*".to_string(),
        CppTy::StdOptional(inner) if matches!(**inner, CppTy::StdString) => "const char*".to_string(),
        CppTy::StdOptional(inner) => cpp_type_name(inner),
        other => cpp_type_name(other),
    };

    out.push_str(&format!(
        "extern \"C\" {} {}({}) noexcept {{\n",
        flat_ret, shim_name, shim_params.join(", ")
    ));
    out.push_str("    try {\n");

    // Reconstruct rich args from the flat ones. `std::string`'s
    // pointer-constructor stops at the first NUL just like H#'s own
    // `hsh_strlen` does, so this is a faithful reconstruction, not a
    // truncation risk beyond what H# strings already have.
    let mut call_args: Vec<String> = Vec::new();
    for (i, p) in f.params.iter().enumerate() {
        if len_param_consumed.contains(&i) { continue; }
        let cty = &param_cpps[i];
        match cty {
            CppTy::StdString => {
                out.push_str(&format!(
                    "        std::string {n}({n}_ptr ? {n}_ptr : \"\");\n", n = p.name));
                call_args.push(p.name.clone());
            }
            CppTy::StdVector(inner) => {
                let len_idx = *data_param_len_idx.get(&i)
                    .expect("std::vector<T> param without a paired length slipped past validation");
                let len_name = &f.params[len_idx].name;
                out.push_str(&format!(
                    "        std::vector<{t}> {n}({n}_ptr, {n}_ptr + {l});\n",
                    t = cpp_type_name(inner), n = p.name, l = len_name));
                call_args.push(p.name.clone());
            }
            CppTy::StdOptional(inner) if matches!(**inner, CppTy::StdString) => {
                out.push_str(&format!(
                    "        std::optional<std::string> {n} = {n}_ptr ? std::optional<std::string>({n}_ptr) : std::nullopt;\n",
                    n = p.name));
                call_args.push(p.name.clone());
            }
            CppTy::StdOptional(inner) => {
                // Sentinel reconstruction — see `is_sentinel_representable_cpp`/
                // `sentinel_expr_cpp`. `bool`'s sentinel is `false` itself
                // (there's no separate int-to-bool cast pitfall in C++ the
                // way there is in Rust, but we still spell it as an
                // explicit comparison for symmetry/clarity).
                let check = if matches!(**inner, CppTy::Bool) {
                    format!("!{}", p.name)
                } else {
                    format!("{} == {}", p.name, sentinel_expr_cpp(inner))
                };
                out.push_str(&format!(
                    "        std::optional<{t}> {n}_opt = ({chk}) ? std::nullopt : std::optional<{t}>({n});\n",
                    t = cpp_type_name(inner), n = p.name, chk = check));
                call_args.push(format!("{}_opt", p.name));
            }
            CppTy::Opaque(name) => {
                // Field-by-field flatten via `hsh_struct_get` — see
                // `struct_is_flattenable_cpp`/`emit_struct_field_read_cpp`
                // and the validation error above for the exact contract.
                // Positional aggregate init (not designated initializers,
                // to stay valid pre-C++20): relies on the real struct's
                // member declaration order matching H#'s field order,
                // which the validation error message says explicitly.
                let fields = structs.get(name).expect("validated flattenable struct missing from `structs`");
                let mut field_vars = Vec::with_capacity(fields.len());
                for (fi, field) in fields.iter().enumerate() {
                    let var = format!("{}_{}", p.name, field.name);
                    out.push_str(&emit_struct_field_read_cpp(&p.name, fi, field, &var));
                    field_vars.push(var);
                }
                out.push_str(&format!("        {t} {n}{{{fs}}};\n", t = name, n = p.name, fs = field_vars.join(", ")));
                call_args.push(p.name.clone());
            }
            _ => call_args.push(p.name.clone()),
        }
    }

    let call_expr = format!("{}({})", mangled, call_args.join(", "));
    match &ret_cpp {
        CppTy::Void => {
            out.push_str(&format!("        {};\n", call_expr));
            out.push_str("        return;\n");
        }
        CppTy::StdString => {
            out.push_str(&format!("        std::string __r = {};\n", call_expr));
            out.push_str("        char* __buf = static_cast<char*>(std::malloc(__r.size() + 1));\n");
            out.push_str("        if (!__buf) return nullptr;\n");
            out.push_str("        std::memcpy(__buf, __r.data(), __r.size());\n");
            out.push_str("        __buf[__r.size()] = '\\0';\n");
            out.push_str("        return __buf; // caller (H# runtime) owns this and must free() it\n");
        }
        CppTy::StdOptional(inner) => {
            out.push_str(&format!("        auto __r = {};\n", call_expr));
            out.push_str("        if (__r.has_value()) {\n");
            match **inner {
                CppTy::StdString => {
                    out.push_str("            const std::string& __s = *__r;\n");
                    out.push_str("            char* __buf = static_cast<char*>(std::malloc(__s.size() + 1));\n");
                    out.push_str("            if (!__buf) return nullptr;\n");
                    out.push_str("            std::memcpy(__buf, __s.data(), __s.size());\n");
                    out.push_str("            __buf[__s.size()] = '\\0';\n");
                    out.push_str("            return __buf; // caller (H# runtime) owns this and must free() it\n");
                }
                _ => out.push_str("            return *__r;\n"),
            }
            out.push_str("        }\n");
            out.push_str(&format!("        return {};\n", sentinel_expr_cpp(inner)));
        }
        _ => {
            out.push_str(&format!("        return {};\n", call_expr));
        }
    }

    out.push_str("    } catch (...) {\n");
    out.push_str("        // A C++ exception must never unwind across this `extern \"C\"` frame\n");
    out.push_str("        // into H#'s LLVM-generated code — that's undefined behavior. Convert\n");
    out.push_str("        // it into H#'s sentinel failure value instead.\n");
    match &ret_cpp {
        CppTy::Void => out.push_str("        return;\n"),
        CppTy::StdString => out.push_str("        return nullptr;\n"),
        CppTy::F32 | CppTy::F64 => out.push_str("        return -1;\n"),
        CppTy::StdOptional(inner) => out.push_str(&format!("        return {};\n", sentinel_expr_cpp(inner))),
        _ => out.push_str("        return static_cast<decltype(0)>(-1);\n"),
    }
    out.push_str("    }\n}\n");

    Ok(out)
}

fn cpp_type_name(t: &CppTy) -> String {
    match t {
        CppTy::Void => "void".into(),
        CppTy::Bool => "bool".into(),
        CppTy::Char => "char".into(),
        CppTy::I8  => "int8_t".into(),  CppTy::U8  => "uint8_t".into(),
        CppTy::I16 => "int16_t".into(), CppTy::U16 => "uint16_t".into(),
        CppTy::I32 => "int32_t".into(), CppTy::U32 => "uint32_t".into(),
        CppTy::I64 => "int64_t".into(), CppTy::U64 => "uint64_t".into(),
        CppTy::F32 => "float".into(),   CppTy::F64 => "double".into(),
        CppTy::Ptr(inner, is_const) => if *is_const { format!("const {}*", cpp_type_name(inner)) } else { format!("{}*", cpp_type_name(inner)) },
        CppTy::Ref(inner, is_const) => if *is_const { format!("const {}&", cpp_type_name(inner)) } else { format!("{}&", cpp_type_name(inner)) },
        CppTy::StdString => "std::string".into(),
        CppTy::StdVector(inner) => format!("std::vector<{}>", cpp_type_name(inner)),
        CppTy::StdOptional(inner) => format!("std::optional<{}>", cpp_type_name(inner)),
        // A *bare* `Opaque(n)` (not wrapped in `Ptr`/`Ref`, which already
        // add their own `*`/`&` suffix around a recursive call to this
        // function) always means "by value" in this type mapping — H#'s
        // `ref`/`ref mut T` map to `CppTy::Ptr`/`CppTy::Ref` wrapping an
        // inner `Opaque`, never to a bare `Opaque` directly (see
        // `hsh_type_to_cpp`). So this must be the plain class/struct name,
        // not a pointer — see `generate_shim`'s `CppTy::Opaque` handling
        // (opaque-by-value flattening) for the only place this is now
        // actually reachable from (previously by-value opaque types were
        // always rejected before any `cpp_type_name` call, so this arm's
        // old `"{}*".format(n)` — appropriate for the `Ptr`/`Ref` cases
        // but wrong for a bare by-value occurrence — was latent/dead).
        CppTy::Opaque(n) => n.clone(),
    }
}

fn describe(path: &CppPath, params: &[CppTy]) -> String {
    let qualified = path.namespaces.iter().cloned()
        .chain(path.class_name.clone())
        .chain(std::iter::once(path.fn_name.clone()))
        .collect::<Vec<_>>()
        .join("::");
    format!("{}({})", qualified, params.iter().map(cpp_type_name).collect::<Vec<_>>().join(", "))
}
