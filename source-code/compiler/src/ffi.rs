use hsharp_parser::ast::TypeExpr;

#[derive(Debug, Clone)]
pub struct ExternBlock {
    pub lang:      ExternLang,
    pub link_kind: LinkKind,
    pub library:   Option<String>,  // "libssl" etc.
    pub functions: Vec<ExternFn>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExternLang {
    C,
    Rust,
    Cpp,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LinkKind {
    Static,   // extern static [c] is...end  → links .a
    Dynamic,  // extern dynamic [c] is...end → links .so at runtime
}

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

/// Build the C header declaration for an extern function
pub fn c_decl(f: &ExternFn) -> String {
    let ret = match &f.return_type {
        None    => "void".to_string(),
        Some(t) => type_to_c(t),
    };
    let params: Vec<String> = f.params.iter()
        .map(|p| format!("{} {}", type_to_c(&p.ty), p.name))
        .collect();
    let params_str = if f.variadic {
        if params.is_empty() { "...".into() }
        else { format!("{}, ...", params.join(", ")) }
    } else if params.is_empty() {
        "void".into()
    } else {
        params.join(", ")
    };
    format!("{} {}({});", ret, f.name, params_str)
}

/// Build the Rust extern "C" block declaration
pub fn rust_extern_decl(f: &ExternFn) -> String {
    let ret = match &f.return_type {
        None    => String::new(),
        Some(t) => format!(" -> {}", type_to_rust(t)),
    };
    let params: Vec<String> = f.params.iter()
        .map(|p| format!("{}: {}", p.name, type_to_rust(&p.ty)))
        .collect();
    format!("    pub fn {}({}){};\n", f.name, params.join(", "), ret)
}

/// Map H# type to C type string
pub fn type_to_c(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Named(n) => match n.as_str() {
            "int"    | "i64"  => "int64_t",
            "uint"   | "u64"  => "uint64_t",
            "i32"    | "u32"  => "int32_t",
            "i16"    | "u16"  => "int16_t",
            "i8"              => "int8_t",
            "u8"              => "uint8_t",
            "f64"             => "double",
            "f32"             => "float",
            "bool"            => "int",
            "string"          => "const char*",
            "bytes"           => "uint8_t*",
            "void"            => "void",
            _                 => "void*",
        }.to_string(),
        TypeExpr::Void        => "void".into(),
        TypeExpr::Optional(_) | TypeExpr::Ref(_) | TypeExpr::RefMut(_) => "void*".into(),
        _ => "void*".into(),
    }
}

/// Map H# type to Rust FFI type string
pub fn type_to_rust(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Named(n) => match n.as_str() {
            "int"    | "i64"  => "i64",
            "uint"   | "u64"  => "u64",
            "i32"             => "i32",
            "u32"             => "u32",
            "i16"             => "i16",
            "u16"             => "u16",
            "i8"              => "i8",
            "u8"              => "u8",
            "f64"             => "f64",
            "f32"             => "f32",
            "bool"            => "bool",
            "string"          => "*const std::os::raw::c_char",
            "void"            => "()",
            _                 => "*mut std::ffi::c_void",
        }.to_string(),
        TypeExpr::Void => "()".into(),
        _ => "*mut std::ffi::c_void".into(),
    }
}
