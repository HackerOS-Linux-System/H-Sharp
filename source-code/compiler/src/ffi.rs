use hsharp_parser::ast::TypeExpr;

// ─── ExternBlock description (compiler-internal, separate from AST) ───────────

#[derive(Debug, Clone)]
pub struct ExternBlock {
    pub lang:      ExternLang,
    pub link_kind: LinkKind,
    pub library:   Option<String>,
    pub functions: Vec<ExternFn>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExternLang { C, Rust, Cpp, Python }

#[derive(Debug, Clone, PartialEq)]
pub enum LinkKind { Static, Dynamic }

#[derive(Debug, Clone)]
pub struct ExternFn {
    pub name:        String,
    pub params:      Vec<ExternParam>,
    pub return_type: Option<TypeExpr>,
    pub variadic:    bool,
}

#[derive(Debug, Clone)]
pub struct ExternParam {
    pub name: String,
    pub ty:   TypeExpr,
}

// ─── C / C++ ─────────────────────────────────────────────────────────────────

/// Build a C function prototype declaration.
///
/// Works equally for `extern [c]` and `extern [c++]` since the prototype
/// syntax is identical (both use C linkage for FFI).
///
/// ```c
/// int64_t my_fn(uint8_t* buf, int64_t len, ...);
/// ```
pub fn c_decl(f: &ExternFn) -> String {
    let ret = match &f.return_type {
        None    => "void".to_string(),
        Some(t) => type_to_c(t),
    };
    let mut params: Vec<String> = f.params.iter()
        .map(|p| format!("{} {}", type_to_c(&p.ty), p.name))
        .collect();
    if f.variadic { params.push("...".to_string()); }
    let params_str = if params.is_empty() { "void".to_string() } else { params.join(", ") };
    format!("{} {}({});", ret, f.name, params_str)
}

/// Build a complete C header block for a group of extern functions with
/// the required `#include`s for fixed-width integer types.
pub fn c_header_block(fns: &[ExternFn]) -> String {
    let mut out = String::from("#include <stdint.h>\n#include <stdbool.h>\n\n");
    for f in fns {
        out.push_str(&c_decl(f));
        out.push('\n');
    }
    out
}

// ─── Rust ─────────────────────────────────────────────────────────────────────

/// Build a Rust `extern "C"` fn declaration line (no surrounding block).
///
/// ```rust
/// pub fn my_fn(buf: *mut u8, len: i64, ...) -> i64;
/// ```
pub fn rust_extern_decl(f: &ExternFn) -> String {
    let ret = match &f.return_type {
        None    => String::new(),
        Some(t) => format!(" -> {}", type_to_rust(t)),
    };
    let mut params: Vec<String> = f.params.iter()
        .map(|p| format!("{}: {}", p.name, type_to_rust(&p.ty)))
        .collect();
    if f.variadic { params.push("...".to_string()); }
    format!("    pub fn {}({}){};", f.name, params.join(", "), ret)
}

/// Build a complete `unsafe extern "C" { ... }` block.
pub fn rust_extern_block(fns: &[ExternFn]) -> String {
    let mut out = String::from("unsafe extern \"C\" {\n");
    for f in fns {
        out.push_str(&rust_extern_decl(f));
        out.push('\n');
    }
    out.push('}');
    out
}

// ─── Python trampolines ───────────────────────────────────────────────────────

/// Return the internal C prototype used for the `hsh_py_call` trampoline.
///
/// All Python values cross the bridge as null-terminated C strings; the
/// return value is also a `const char*` (caller must free or treat as
/// static depending on bridge implementation).
pub fn python_trampoline_sig(fn_name: &str, param_count: usize) -> String {
    let params: String = (0..param_count)
        .map(|i| format!("const char* arg{}", i))
        .collect::<Vec<_>>()
        .join(", ");
    let params_str = if params.is_empty() { "void".to_string() } else { params };
    format!("const char* hsh_py_{}({});", fn_name, params_str)
}

/// Build the full C trampoline body for a Python-bridged function.
/// Calls the runtime `hsh_py_call(module, fn, argc, argv)` helper.
pub fn python_trampoline_body(module: &str, fn_name: &str, param_count: usize) -> String {
    let sig = python_trampoline_sig(fn_name, param_count);
    let sig = sig.trim_end_matches(';');
    let argc = param_count;
    let args_arr: String = (0..param_count)
        .map(|i| format!("arg{}", i))
        .collect::<Vec<_>>()
        .join(", ");
    let args_body = if argc == 0 {
        "    const char* argv[] = { NULL };\n".to_string()
    } else {
        format!("    const char* argv[] = {{ {}, NULL }};\n", args_arr)
    };
    format!(
        "{} {{\n{}    return hsh_py_call(\"{}\", \"{}\", {}, argv);\n}}",
        sig, args_body, module, fn_name, argc
    )
}

// ─── Type mappings ───────────────────────────────────────────────────────────

/// Map an H# type expression to its C equivalent.
///
/// Pointer types (`string`, `bytes`, slices, optionals, refs) all become
/// appropriately typed C pointers. Unknown / generic types fall back to
/// `void*` (opaque pointer — safe, but caller must cast).
pub fn type_to_c(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Named(n) => named_to_c(n),
        // Primitive shorthands
        TypeExpr::I8   => "int8_t".into(),
        TypeExpr::I16  => "int16_t".into(),
        TypeExpr::I32  => "int32_t".into(),
        TypeExpr::I64  => "int64_t".into(),
        TypeExpr::I128 => "__int128".into(),
        TypeExpr::U8   => "uint8_t".into(),
        TypeExpr::U16  => "uint16_t".into(),
        TypeExpr::U32  => "uint32_t".into(),
        TypeExpr::U64  => "uint64_t".into(),
        TypeExpr::U128 => "unsigned __int128".into(),
        TypeExpr::F32  => "float".into(),
        TypeExpr::F64  => "double".into(),
        TypeExpr::Bool => "int".into(),          // C has no _Bool in older std
        TypeExpr::String => "const char*".into(),
        TypeExpr::Bytes  => "uint8_t*".into(),
        TypeExpr::Void   => "void".into(),
        // Pointer/wrapper types
        TypeExpr::Ref(_)    => "const void*".into(),
        TypeExpr::RefMut(_) => "void*".into(),
        TypeExpr::Optional(inner) => {
            // Optional<T*> is just a nullable T* in C
            let inner_c = type_to_c(inner);
            if inner_c.ends_with('*') { inner_c } else { format!("{}*", inner_c) }
        }
        TypeExpr::Array(inner) => format!("{}*", type_to_c(inner)),
        TypeExpr::Slice(inner, _) => format!("{}*", type_to_c(inner)),
        TypeExpr::Tuple(_)        => "void*".into(),  // opaque
        TypeExpr::Generic(n, _)   => named_to_c(n),
        TypeExpr::Fn(_, _)        => "void*".into(),  // function pointer (opaque)
    }
}

fn named_to_c(n: &str) -> String {
    match n {
        "int"  | "i64"  | "isize" => "int64_t",
        "uint" | "u64"  | "usize" => "uint64_t",
        "i32"                     => "int32_t",
        "u32"                     => "uint32_t",
        "i16"                     => "int16_t",
        "u16"                     => "uint16_t",
        "i8"                      => "int8_t",
        "u8"                      => "uint8_t",
        "i128"                    => "__int128",
        "u128"                    => "unsigned __int128",
        "f64"  | "float64"        => "double",
        "f32"  | "float32"        => "float",
        "bool"                    => "int",
        "string" | "str"          => "const char*",
        "bytes"  | "byte"         => "uint8_t*",
        "void"                    => "void",
        "char"                    => "char",
        "size_t"                  => "size_t",
        _                         => "void*",
    }.to_string()
}

/// Map an H# type expression to the Rust FFI equivalent.
///
/// Uses `std::ffi` and `std::os::raw` types where appropriate.
pub fn type_to_rust(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Named(n) => named_to_rust(n),
        TypeExpr::I8   => "i8".into(),
        TypeExpr::I16  => "i16".into(),
        TypeExpr::I32  => "i32".into(),
        TypeExpr::I64  => "i64".into(),
        TypeExpr::I128 => "i128".into(),
        TypeExpr::U8   => "u8".into(),
        TypeExpr::U16  => "u16".into(),
        TypeExpr::U32  => "u32".into(),
        TypeExpr::U64  => "u64".into(),
        TypeExpr::U128 => "u128".into(),
        TypeExpr::F32  => "f32".into(),
        TypeExpr::F64  => "f64".into(),
        TypeExpr::Bool => "bool".into(),
        TypeExpr::String => "*const std::ffi::c_char".into(),
        TypeExpr::Bytes  => "*mut u8".into(),
        TypeExpr::Void   => "()".into(),
        TypeExpr::Ref(inner)    => format!("*const {}", type_to_rust(inner)),
        TypeExpr::RefMut(inner) => format!("*mut {}",   type_to_rust(inner)),
        TypeExpr::Optional(inner) => format!("Option<*mut {}>", type_to_rust(inner)),
        TypeExpr::Array(inner)    => format!("*mut {}",  type_to_rust(inner)),
        TypeExpr::Slice(inner, _) => format!("*mut {}",  type_to_rust(inner)),
        TypeExpr::Tuple(_)        => "*mut std::ffi::c_void".into(),
        TypeExpr::Generic(n, _)   => named_to_rust(n),
        TypeExpr::Fn(_, _)        => "*mut std::ffi::c_void".into(),
    }
}

fn named_to_rust(n: &str) -> String {
    match n {
        "int"  | "i64"  | "isize" => "i64",
        "uint" | "u64"  | "usize" => "u64",
        "i32"                     => "i32",
        "u32"                     => "u32",
        "i16"                     => "i16",
        "u16"                     => "u16",
        "i8"                      => "i8",
        "u8"                      => "u8",
        "i128"                    => "i128",
        "u128"                    => "u128",
        "f64"  | "float64"        => "f64",
        "f32"  | "float32"        => "f32",
        "bool"                    => "bool",
        "string" | "str"          => "*const std::ffi::c_char",
        "bytes"  | "byte"         => "*mut u8",
        "void"                    => "()",
        "char"                    => "std::os::raw::c_char",
        "size_t"                  => "usize",
        _                         => "*mut std::ffi::c_void",
    }.to_string()
}

// ─── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn c_decl_simple() {
        let f = ExternFn {
            name: "add".into(),
            params: vec![
                ExternParam { name: "a".into(), ty: TypeExpr::I64 },
                ExternParam { name: "b".into(), ty: TypeExpr::I64 },
            ],
            return_type: Some(TypeExpr::I64),
            variadic: false,
        };
        let decl = c_decl(&f);
        assert_eq!(decl, "int64_t add(int64_t a, int64_t b);");
    }

    #[test]
    fn c_decl_variadic() {
        let f = ExternFn {
            name: "printf".into(),
            params: vec![ExternParam { name: "fmt".into(), ty: TypeExpr::String }],
            return_type: Some(TypeExpr::I32),
            variadic: true,
        };
        let decl = c_decl(&f);
        assert!(decl.contains("..."));
        assert!(decl.starts_with("int32_t printf("));
    }

    #[test]
    fn c_decl_no_params() {
        let f = ExternFn {
            name: "get_count".into(),
            params: vec![],
            return_type: Some(TypeExpr::U64),
            variadic: false,
        };
        assert_eq!(c_decl(&f), "uint64_t get_count(void);");
    }

    #[test]
    fn rust_extern_decl_basic() {
        let f = ExternFn {
            name: "my_fn".into(),
            params: vec![ExternParam { name: "x".into(), ty: TypeExpr::U8 }],
            return_type: Some(TypeExpr::Bool),
            variadic: false,
        };
        let decl = rust_extern_decl(&f);
        assert!(decl.contains("pub fn my_fn"));
        assert!(decl.contains("x: u8"));
        assert!(decl.contains("-> bool"));
    }

    #[test]
    fn python_trampoline_gen() {
        let sig = python_trampoline_sig("compute", 2);
        assert!(sig.contains("hsh_py_compute"));
        assert!(sig.contains("arg0"));
        assert!(sig.contains("arg1"));

        let body = python_trampoline_body("numpy", "dot", 2);
        assert!(body.contains("\"numpy\""));
        assert!(body.contains("\"dot\""));
        assert!(body.contains("hsh_py_call"));
    }

    #[test]
    fn type_to_c_string() {
        assert_eq!(type_to_c(&TypeExpr::String), "const char*");
        assert_eq!(type_to_c(&TypeExpr::Bytes),  "uint8_t*");
        assert_eq!(type_to_c(&TypeExpr::Void),   "void");
    }

    #[test]
    fn type_to_rust_optional_ptr() {
        let ty = TypeExpr::Optional(Box::new(TypeExpr::U8));
        let r = type_to_rust(&ty);
        assert!(r.contains("Option"));
        assert!(r.contains("u8"));
    }

    #[test]
    fn type_to_rust_ref() {
        let ty = TypeExpr::Ref(Box::new(TypeExpr::I32));
        assert_eq!(type_to_rust(&ty), "*const i32");
        let ty2 = TypeExpr::RefMut(Box::new(TypeExpr::I32));
        assert_eq!(type_to_rust(&ty2), "*mut i32");
    }
}
