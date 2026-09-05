use hsharp_parser::ast::*;

#[derive(Debug, Clone, PartialEq)]
pub enum HType {
    Int, Uint,
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
    F32, F64,
    Bool, Str, Bytes, Void, Any,
    Optional(Box<HType>),
    Array(Box<HType>),
    Tuple(Vec<HType>),
    Named(String),
    Fn(Vec<HType>, Box<HType>),
    Ref(Box<HType>),
    RefMut(Box<HType>),
}

impl HType {
    pub fn from_type_expr(te: &TypeExpr) -> Self {
        match te {
            TypeExpr::Named(n) => match n.as_str() {
                "int"    => HType::Int,
                "uint"   => HType::Uint,
                "i8"     => HType::I8,  "i16"  => HType::I16,
                "i32"    => HType::I32, "i64"  => HType::I64,
                "i128"   => HType::I128,
                "u8"     => HType::U8,  "u16"  => HType::U16,
                "u32"    => HType::U32, "u64"  => HType::U64,
                "u128"   => HType::U128,
                "f32"    => HType::F32, "f64"  => HType::F64,
                "bool"   => HType::Bool,
                "string" => HType::Str,
                "bytes"  => HType::Bytes,
                "any"    => HType::Any,
                _        => HType::Named(n.clone()),
            },
            TypeExpr::Void        => HType::Void,
            TypeExpr::Optional(i) => HType::Optional(Box::new(Self::from_type_expr(i))),
            TypeExpr::Array(i)    => HType::Array(Box::new(Self::from_type_expr(i))),
            TypeExpr::Tuple(ts)   => HType::Tuple(ts.iter().map(Self::from_type_expr).collect()),
            TypeExpr::Ref(i)      => HType::Ref(Box::new(Self::from_type_expr(i))),
            TypeExpr::RefMut(i)   => HType::RefMut(Box::new(Self::from_type_expr(i))),
            TypeExpr::Fn(p, r)    => HType::Fn(p.iter().map(Self::from_type_expr).collect(), Box::new(Self::from_type_expr(r))),
            TypeExpr::Generic(n, _) => HType::Named(n.clone()),
            TypeExpr::Slice(i, _) => HType::Array(Box::new(Self::from_type_expr(i))),
            TypeExpr::I8   => HType::I8,   TypeExpr::I16  => HType::I16,
            TypeExpr::I32  => HType::I32,  TypeExpr::I64  => HType::I64,
            TypeExpr::I128 => HType::I128,
            TypeExpr::U8   => HType::U8,   TypeExpr::U16  => HType::U16,
            TypeExpr::U32  => HType::U32,  TypeExpr::U64  => HType::U64,
            TypeExpr::U128 => HType::U128,
            TypeExpr::F32  => HType::F32,  TypeExpr::F64  => HType::F64,
            TypeExpr::Bool   => HType::Bool,
            TypeExpr::String => HType::Str,
            TypeExpr::Bytes  => HType::Bytes,
        }
    }

    pub fn is_numeric(&self) -> bool {
        matches!(self,
                 HType::Int | HType::Uint |
                 HType::I8 | HType::I16 | HType::I32 | HType::I64 | HType::I128 |
                 HType::U8 | HType::U16 | HType::U32 | HType::U64 | HType::U128 |
                 HType::F32 | HType::F64)
    }

    pub fn compatible_with(&self, other: &HType) -> bool {
        if self == other { return true; }
        if matches!(self, HType::Any) || matches!(other, HType::Any) { return true; }
        if self.is_numeric() && other.is_numeric() { return true; }
        // `nil` infers as `any?` (Optional(Any)) — it's compatible with any
        // declared optional type, e.g. `int?`, `string?`, `MyStruct?`.
        // Likewise Optional(T) is compatible with Optional(U) if T and U are.
        if let (HType::Optional(a), HType::Optional(b)) = (self, other) {
            return a.compatible_with(b);
        }
        // BUG FIX: a bare `T` is compatible with a declared `T?`
        // (implicitly wraps as `Some(value)`) — this is the entire point
        // of `T?` as a return type: `fn f() -> int? is ... return 5 end`
        // is supposed to work exactly like `return Some(5)` would, without
        // the caller having to spell out any wrapping. Before this, only
        // `Optional`-vs-`Optional` was ever considered compatible, so
        // *every* `return <plain value>` into a `T?`-returning function
        // was a hard type error — there wasn't even syntax to spell the
        // wrap explicitly, so this idiom (shown in this project's own
        // test suite: `safe_div`/`chain_div`) could never actually compile.
        // Not symmetric: a declared `T?` is *not* compatible where a bare
        // `T` is required (the caller would need to unwrap first, e.g.
        // via `?`) — only the widening direction (`T` into `T?`) is safe
        // to do implicitly.
        if let HType::Optional(inner) = other {
            return self.compatible_with(inner);
        }
        false
    }

    pub fn display(&self) -> String {
        match self {
            HType::Int    => "int".into(),
            HType::Uint   => "uint".into(),
            HType::I8     => "i8".into(),   HType::I16  => "i16".into(),
            HType::I32    => "i32".into(),  HType::I64  => "i64".into(),
            HType::I128   => "i128".into(),
            HType::U8     => "u8".into(),   HType::U16  => "u16".into(),
            HType::U32    => "u32".into(),  HType::U64  => "u64".into(),
            HType::U128   => "u128".into(),
            HType::F32    => "f32".into(),  HType::F64  => "f64".into(),
            HType::Bool   => "bool".into(),
            HType::Str    => "string".into(),
            HType::Bytes  => "bytes".into(),
            HType::Void   => "void".into(),
            HType::Any    => "any".into(),
            HType::Optional(i) => format!("{}?", i.display()),
            HType::Array(i)    => format!("[{}]", i.display()),
            HType::Tuple(ts)   => format!("({})", ts.iter().map(|t| t.display()).collect::<Vec<_>>().join(", ")),
            HType::Named(n)    => n.clone(),
            HType::Fn(p, r)    => format!("fn({}) -> {}", p.iter().map(|t| t.display()).collect::<Vec<_>>().join(", "), r.display()),
            HType::Ref(i)      => format!("&{}", i.display()),
            HType::RefMut(i)   => format!("&mut {}", i.display()),
        }
    }
}
