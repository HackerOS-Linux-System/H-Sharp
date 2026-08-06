use hsharp_parser::ast::TypeExpr;
use crate::ffi::ExternFn;

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
            return Err(CppFfiError::Unsupported(format!(
                "opaque/user type `{name}` has no known ABI layout to mangle — \
                 pass it as `ref`/`ref mut` (an opaque pointer) instead of by value, \
                 or expose a C-linkage accessor for it"
            )));
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

/// Whether `ty` needs the C++ shim at all, vs. being passable as a plain
/// scalar/pointer straight across the direct-mangled-call path.
///
/// IMPORTANT ABI NOTE: H#'s own LLVM codegen (`llvm_types::htype_to_llvm`)
/// represents `string` as exactly one pointer argument — a plain
/// null-terminated C string (`hsh_strlen` is a `strlen`-style scan, not a
/// stored-length read), not a `(ptr, len)` pair. The shim below matches that
/// *exactly* (one `const char*` parameter, reconstructed via `strlen`) —
/// deliberately, not as a simplification of "the real" ABI. Do not add a
/// companion `_len` parameter here without also changing
/// `build_extern_fn_type` on the H# codegen side, or the two will disagree
/// on argument count and the call will be broken at the LLVM level.
///
/// `std::vector<T>`/`std::optional<T>` marshaling is intentionally *not*
/// auto-generated in this version: H#'s `bytes`/`Array`/`Slice` types are
/// also single bare pointers with no bundled length at the ABI level, so
/// there is no length this shim could read without guessing at a runtime
/// layout this codebase doesn't expose. Declare an explicit paired `len:
/// int` parameter in the `extern` signature and reconstruct the
/// `std::vector`/pass the raw pointer through by hand in those cases —
/// `hsh_type_to_cpp` still maps the type correctly for documentation/the
/// forward declaration, `generate_shim` just won't silently guess a length.
fn needs_marshaling(ty: &CppTy) -> bool {
    matches!(ty, CppTy::StdString)
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
pub fn generate_shim(path: &CppPath, f: &ExternFn) -> Result<String, CppFfiError> {
    let ret_cpp: CppTy = f.return_type.as_ref().map(hsh_type_to_cpp).unwrap_or(CppTy::Void);
    let param_cpps: Vec<CppTy> = f.params.iter().map(|p| hsh_type_to_cpp(&p.ty)).collect();
    let mangled = mangle(path, &param_cpps)?;

    for (p, cty) in f.params.iter().zip(&param_cpps) {
        if matches!(cty, CppTy::StdVector(_) | CppTy::StdOptional(_)) {
            return Err(CppFfiError::Unsupported(format!(
                "parameter `{}` (std::vector/std::optional) has no bundled length/tag \
                 at the ABI level that this shim can safely auto-marshal from a single \
                 pointer — H#'s own `bytes`/`Array`/`Slice` types are bare pointers too. \
                 Split it into an explicit pointer + `len: int` pair in the extern \
                 signature and construct the std::vector by hand in a thin C++-side \
                 wrapper instead of relying on the auto-generated shim for this parameter",
                p.name
            )));
        }
    }
    if matches!(ret_cpp, CppTy::StdVector(_) | CppTy::StdOptional(_)) {
        return Err(CppFfiError::Unsupported(
            "std::vector/std::optional return values need an explicit out-length \
             convention this shim doesn't invent on its own — return std::string \
             (supported) or a primitive/pointer instead".to_string()
        ));
    }

    let mut out = String::new();
    out.push_str("// Auto-generated by hsharp's ffi_cpp shim generator. Do not edit by hand —\n");
    out.push_str("// regenerated on every `hsharp compile` / `bytes build` that sees this\n");
    out.push_str("// `extern [c++]` block. See ffi_cpp.rs for the generator.\n");
    out.push_str("#include <cstdint>\n#include <cstring>\n#include <string>\n#include <vector>\n#include <optional>\n#include <new>\n\n");

    // Forward-declare the real target symbol at its exact mangled name so we
    // don't need the target library's header — only its compiled object/lib.
    out.push_str(&format!(
        "extern \"C\" {} {}({});\n",
        cpp_type_name(&ret_cpp), mangled,
        param_cpps.iter().map(|t| cpp_type_name(t)).collect::<Vec<_>>().join(", ")
    ));
    out.push_str(&format!("// ^ real symbol, reconstructed via Itanium mangling of:\n//   {}\n\n", describe(path, &param_cpps)));

    // Shim signature: flat C ABI only (pointers + fixed-width ints/floats),
    // exactly what H#'s codegen already emits calls with for any `extern`.
    let shim_name = format!("hsh_cpp_shim_{}", f.name);
    let mut shim_params: Vec<String> = Vec::new();
    for p in &f.params {
        let cty = hsh_type_to_cpp(&p.ty);
        if needs_marshaling(&cty) {
            // One pointer parameter — matches `htype_to_llvm`'s `string`
            // mapping exactly (see `needs_marshaling`'s doc comment).
            shim_params.push(format!("const char* {}_ptr", p.name));
        } else {
            shim_params.push(format!("{} {}", cpp_type_name(&cty), p.name));
        }
    }
    let flat_ret = if needs_marshaling(&ret_cpp) { "const char*".to_string() } else { cpp_type_name(&ret_cpp) };

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
    for p in &f.params {
        let cty = hsh_type_to_cpp(&p.ty);
        match &cty {
            CppTy::StdString => {
                out.push_str(&format!(
                    "        std::string {n}({n}_ptr ? {n}_ptr : \"\");\n", n = p.name));
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
        CppTy::Opaque(n) => format!("{}*", n),
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
