#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    /// `string` — `ptr` to a NUL-terminated C string.
    Str,
    /// `bytes` / `[int]` / `[string]` — `ptr` to an `HshArray`.
    Arr,
    /// `int` / `bool` — `i64`.
    Int,
    /// `f64`.
    F64,
    /// `bool` result: the C function returns `int64` (0/1); codegen narrows it to `i1`.
    Bool,
}

pub struct Ext {
    /// Internal call name used by `call_fn_impl` (never user-visible; the
    /// `ext_` prefix keeps it from colliding with user-defined functions).
    pub name: &'static str,
    /// The `__builtin_` suffix this entry serves, e.g. `"hex_encode"`.
    pub dunder: &'static str,
    /// C symbol in `runtime/core.c`.
    pub sym: &'static str,
    pub params: &'static [Kind],
    pub ret: Kind,
}

use Kind::*;

pub static EXT: &[Ext] = &[
    // ── hex ──
    Ext { name: "ext_hex_encode",       dunder: "hex_encode",       sym: "hsh_hex_encode",       params: &[Str],      ret: Str },
    Ext { name: "ext_hex_decode",       dunder: "hex_decode",       sym: "hsh_hex_decode",       params: &[Str],      ret: Str },
    Ext { name: "ext_hex_encode_bytes", dunder: "hex_encode_bytes", sym: "hsh_hex_encode_bytes", params: &[Arr],      ret: Str },
    Ext { name: "ext_hex_xor",          dunder: "hex_xor",          sym: "hsh_hex_xor",          params: &[Str, Str], ret: Str },
    // ── bytes ──
    Ext { name: "ext_bytes_from_ints",  dunder: "bytes_from_ints",  sym: "hsh_bytes_from_ints",  params: &[Arr],      ret: Arr },
    Ext { name: "ext_bytes_to_ints",    dunder: "bytes_to_ints",    sym: "hsh_bytes_to_ints",    params: &[Arr],      ret: Arr },
    Ext { name: "ext_bytes_concat",     dunder: "bytes_concat",     sym: "hsh_bytes_concat",     params: &[Arr, Arr], ret: Arr },
    Ext { name: "ext_bytes_len",        dunder: "bytes_len",        sym: "hsh_bytes_len",        params: &[Arr],      ret: Int },
    Ext { name: "ext_bytes_to_string",  dunder: "bytes_to_string",  sym: "hsh_bytes_to_str_lossy",  params: &[Arr],      ret: Str },
    Ext { name: "ext_base64_decode_bytes", dunder: "base64_decode_bytes", sym: "hsh_base64_decode_bytes", params: &[Str], ret: Arr },
    // ── date (UTC) ──
    Ext { name: "ext_date_year",        dunder: "date_year",        sym: "hsh_date_year",        params: &[Int],      ret: Int },
    Ext { name: "ext_date_month",       dunder: "date_month",       sym: "hsh_date_month",       params: &[Int],      ret: Int },
    Ext { name: "ext_date_day",         dunder: "date_day",         sym: "hsh_date_day",         params: &[Int],      ret: Int },
    Ext { name: "ext_date_weekday",     dunder: "date_weekday",     sym: "hsh_date_weekday",     params: &[Int],      ret: Str },
    Ext { name: "ext_date_add_days",    dunder: "date_add_days",    sym: "hsh_date_add_days",    params: &[Int, Int], ret: Int },
    Ext { name: "ext_date_add_hours",   dunder: "date_add_hours",   sym: "hsh_date_add_hours",   params: &[Int, Int], ret: Int },
    Ext { name: "ext_date_diff_days",   dunder: "date_diff_days",   sym: "hsh_date_diff_days",   params: &[Int, Int], ret: Int },
    // ── env / term / uuid ──
    Ext { name: "ext_env_home",         dunder: "env_home",         sym: "hsh_env_home",         params: &[],         ret: Str },
    Ext { name: "ext_env_remove",       dunder: "env_remove",       sym: "hsh_env_remove",       params: &[Str],      ret: Bool },
    Ext { name: "ext_env_vars",         dunder: "env_vars",         sym: "hsh_env_vars",         params: &[],         ret: Arr },
    Ext { name: "ext_term_width",       dunder: "term_width",       sym: "hsh_term_width",       params: &[],         ret: Int },
    Ext { name: "ext_term_height",      dunder: "term_height",      sym: "hsh_term_height",      params: &[],         ret: Int },
    Ext { name: "ext_term_is_tty",      dunder: "term_is_tty",      sym: "hsh_term_is_tty",      params: &[],         ret: Bool },
    Ext { name: "ext_uuid_is_valid",    dunder: "uuid_is_valid",    sym: "hsh_uuid_is_valid",    params: &[Str],      ret: Bool },
    // ── math ──
    Ext { name: "ext_math_asin",        dunder: "math_asin",        sym: "hsh_math_asin",        params: &[F64],      ret: F64 },
    Ext { name: "ext_math_acos",        dunder: "math_acos",        sym: "hsh_math_acos",        params: &[F64],      ret: F64 },
    Ext { name: "ext_math_atan",        dunder: "math_atan",        sym: "hsh_math_atan",        params: &[F64],      ret: F64 },
    Ext { name: "ext_math_atan2",       dunder: "math_atan2",       sym: "hsh_math_atan2",       params: &[F64, F64], ret: F64 },
    Ext { name: "ext_math_round",       dunder: "math_round",       sym: "hsh_math_round",       params: &[F64],      ret: F64 },
    Ext { name: "ext_math_trunc",       dunder: "math_trunc",       sym: "hsh_math_trunc",       params: &[F64],      ret: F64 },
    Ext { name: "ext_math_log",         dunder: "math_log",         sym: "hsh_math_log",         params: &[F64],      ret: F64 },
    Ext { name: "ext_math_log2",        dunder: "math_log2",        sym: "hsh_math_log2",        params: &[F64],      ret: F64 },
    Ext { name: "ext_math_log10",       dunder: "math_log10",       sym: "hsh_math_log10",       params: &[F64],      ret: F64 },
    Ext { name: "ext_math_exp",         dunder: "math_exp",         sym: "hsh_math_exp",         params: &[F64],      ret: F64 },
];

/// Lookup by the internal `ext_*` call name (used by `call_fn_impl`).
pub fn find(name: &str) -> Option<&'static Ext> {
    if !name.starts_with("ext_") { return None; }
    EXT.iter().find(|e| e.name == name)
}

/// Lookup by `__builtin_<dunder>` suffix (used by `resolve_builtin_dunder_llvm`
/// and by the registry so `supported_on(.., Llvm)` agrees with codegen).
pub fn find_dunder(dunder: &str) -> Option<&'static Ext> {
    EXT.iter().find(|e| e.dunder == dunder)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_are_unique_and_prefixed() {
        for (i, a) in EXT.iter().enumerate() {
            assert!(a.name.starts_with("ext_"), "{}", a.name);
            assert_eq!(a.name, format!("ext_{}", a.dunder));
            assert!(a.sym.starts_with("hsh_"), "{}", a.sym);
            for b in &EXT[i + 1..] {
                assert_ne!(a.name, b.name);
                assert_ne!(a.sym, b.sym);
            }
        }
    }

    #[test]
    fn registry_marks_every_entry_llvm_supported() {
        use crate::builtins_registry::{find, Backend};
        for e in EXT {
            let spec = find(&format!("__builtin_{}", e.dunder))
                .unwrap_or_else(|| panic!("no registry spec for __builtin_{}", e.dunder));
            assert!(spec.backends.contains(&Backend::Llvm), "__builtin_{} not marked Llvm", e.dunder);
        }
    }
}
