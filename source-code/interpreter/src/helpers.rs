use serde_json::Value as Json;
use std::collections::HashMap;
use crate::value::{Value, RuntimeError};


pub fn resolve_stdlib_alias(full_path: &str) -> Option<&'static str> {
    Some(match full_path {
        // crypto — bridge to the differently-named existing builtins
        "crypto::sha256"        => "sha256",
        "crypto::sha512"        => "sha512",
        "crypto::md5"            => "md5",
        "crypto::sha1"           => "sha1",
        "crypto::hmac_sha256"   => "hmac_sha256",
        "crypto::hmac_sha512"   => "hmac_sha512",
        "crypto::random_bytes"  => "random_string",
        "crypto::random_int"    => "random_int",
        "sec::xor"               => "xor_hex",
        "sec::rot13"             => "rot13",
        "sec::scan_port"         => "scan_port",
        // hex
        "hex::encode"            => "hex_encode",
        "hex::decode"            => "hex_decode",
        // regex — std/regex.h#'s H# API takes (text, pattern, ...) i.e.
        // subject-first; bridge to the _ta ("text-argument-first") wrapper
        // builtins, which swap order before delegating to the underlying
        // grep/sed-based (pattern, text) implementations.
        "regex::is_match"        => "re_match_ta",
        "re::is_match"           => "re_match_ta",
        "regex::find"            => "re_find_ta",
        "re::find"                => "re_find_ta",
        "regex::find_all"        => "re_find_all_ta",
        "re::find_all"            => "re_find_all_ta",
        "regex::replace"         => "re_replace_ta",
        "re::replace"             => "re_replace_ta",
        "regex::replace_all"     => "re_replace_all_ta",
        "re::replace_all"         => "re_replace_all_ta",
        "regex::split"            => "re_split_ta",
        "re::split"                => "re_split_ta",
        // fs
        "fs::read"                => "fs_read",
        "fs::write"               => "fs_write",
        "fs::exists"              => "fs_exists",
        "fs::mkdir"               => "fs_mkdir_all",
        "fs::remove"              => "fs_remove",
        "fs::append"              => "fs_append",
        "fs::is_dir"              => "fs_is_dir",
        "fs::is_file"             => "fs_is_file",
        "fs::rmdir"               => "fs_rmdir",
        "fs::rmdir_all"           => "fs_rmdir_all",
        "fs::read_lines"          => "fs_read_lines",
        "fs::size"                => "fs_size",
        "fs::copy"                => "fs_copy",
        "fs::rename"              => "fs_rename",
        "fs::cwd"                 => "fs_cwd",
        "fs::chdir"               => "fs_cwd", // no-op placeholder until chdir lands
        "fs::list_dir"            => "fs_list_dir",
        // path
        "path::join"              => "path_join",
        "path::stem"              => "path_stem",
        "path::extension"         => "path_extension",
        "path::parent"            => "path_parent",
        // env
        "env::temp_dir"           => "env_temp_dir",
        "env::get"                => "env_get",
        "env::args"               => "env_args",
        "env::home"               => "env_home",
        // iter
        "iter::map"                => "iter_map",
        "iter::filter"             => "iter_filter",
        "iter::reduce"             => "iter_reduce",
        "iter::zip"                => "iter_zip",
        "iter::chain"              => "iter_chain",
        "iter::take"                => "iter_take",
        "iter::skip"                => "iter_skip",
        "iter::any"                 => "iter_any",
        "iter::all"                 => "iter_all",
        "iter::sum"                 => "iter_sum",
        "iter::product"             => "iter_product",
        "iter::reverse"             => "iter_reverse",
        "iter::join"                => "iter_join",
        "iter::repeat"              => "iter_repeat",
        "iter::unique"              => "iter_unique",
        // sort
        "sort::sort_ints"           => "sort_ints",
        "sort::sort_strings"        => "sort_strings",
        "sort::binary_search"       => "binary_search",
        "sort::binary_search_left"  => "binary_search_left",
        "sort::min_int"             => "min_int",
        "sort::max_int"             => "max_int",
        "sort::merge_sorted"        => "merge_sorted",
        // async
        "async::spawn"               => "async_spawn",
        "async::timeout"             => "async_timeout",
        // str
        "str::trim"               => "str_trim",
        "str::split"              => "str_split",
        "str::replace"            => "str_replace",
        "str::join"               => "str_join",
        // conv
        "conv::str_to_int"        => "conv_str_to_int",
        "conv::int_to_hex"        => "conv_int_to_hex",
        "conv::to_bytes"          => "conv_to_bytes",
        // db
        "db::open"                => "db_open",
        "db::query"               => "db_query",
        "db::exec"                => "db_exec",
        "db::close"               => "db_close",
        // dns
        "dns::resolve"            => "dns_resolve",
        // uuid
        "uuid::v4"                 => "new_uuid",
        // time
        "t::now_unix"             => "now_unix",
        "t::now_ms"               => "now_ms",
        "t::sleep_ms"             => "sleep_ms",
        "time::now_unix"          => "time_unix",
        "time::now_ms"            => "time_ms",
        // collections — native HashMap/HashSet/Queue/Stack constructors
        "col::HashMap::new"        => "hashmap_new",
        "col::HashSet::new"        => "hashset_new",
        "col::Queue::new"          => "queue_new",
        "col::Stack::new"          => "stack_new",
        // json — set_str/set_int/set_bool all bridge to the same generic
        // json_set builtin (the value's runtime type is preserved either way)
        "json::set_str"            => "json_set",
        "json::set_int"            => "json_set",
        "json::set_bool"           => "json_set",
        // The rest of the json:: API — each maps 1:1 to its json_* builtin.
        // These were missing entirely before (only the three set_* aliases
        // existed), meaning json::parse, json::get_str, json::stringify,
        // etc. all silently fell through call_path's snake_case/
        // builtin_exists fallback to a nonexistent bare-last-segment
        // function name and returned Nil instead of ever reaching their
        // real implementations — every JSON test failed because of this.
        "json::parse"               => "json_parse",
        "json::parse_array"         => "json_parse_array",
        "json::stringify"           => "json_stringify",
        "json::stringify_pretty"    => "json_stringify_pretty",
        "json::empty_object"        => "json_empty_object",
        "json::object"              => "json_object",
        "json::get_str"             => "json_get_str",
        "json::get_int"             => "json_get_int",
        "json::get_float"           => "json_get_float",
        "json::get_bool"            => "json_get_bool",
        "json::get_obj"             => "json_get_obj",
        "json::get_arr"             => "json_get_arr",
        "json::has_key"             => "json_has_key",
        "json::is_null"             => "json_is_null",
        "json::obj_at"              => "json_obj_at",
        "json::int_at"              => "json_int_at",
        "json::str_at"              => "json_as_str",
        "json::as_int"              => "json_as_int",
        "json::as_str"              => "json_as_str",
        "json::query"               => "json_query",
        _ => return None,
    })
}

/// Returns true for snake_case names known to be handled by the builtin
/// match arm inside `call_fn` (the stdlib bridge). Used by `call_path` as a
/// best-effort guess only *after* the explicit alias table has already been
/// checked — this heuristic can produce a name that looks plausible but
/// isn't actually implemented, in which case `call_fn` silently returns
/// `Nil` rather than erroring. Prefer adding new mappings to
/// `resolve_stdlib_alias` over relying on this fallback.
pub fn builtin_exists(snake_name: &str) -> bool {
    const KNOWN: &[&str] = &[
        "math_sin", "math_cos", "math_tan", "math_asin", "math_acos", "math_atan",
        "math_atan2", "math_sqrt", "math_pow", "math_floor", "math_ceil", "math_round",
        "math_trunc", "math_log", "math_log2", "math_log10", "math_exp", "math_abs",
        "math_fabs", "math_ipow", "math_min", "math_max", "math_fmin", "math_fmax",
        "math_clamp", "math_fclamp", "math_gcd", "math_lcm", "math_pi", "math_e", "math_tau",
        "fs_read", "fs_write", "fs_exists", "fs_mkdir_all", "fs_remove", "fs_append",
        "fs_is_dir", "fs_rmdir", "fs_rmdir_all", "fs_read_lines", "fs_size",
        "fs_copy", "fs_rename", "fs_cwd", "fs_list_dir",
        "path_join", "path_stem", "path_extension", "path_parent",
        "env_temp_dir", "env_get", "env_args", "env_home",
        "str_trim", "str_split", "str_replace", "str_contains",
        "db_open", "db_query", "db_exec", "db_close",
        "sqlite_open", "sqlite_query", "sqlite_exec", "sqlite_close",
        "regex_match", "regex_find", "regex_find_all", "regex_replace",
        "re_match", "re_find", "re_find_all", "re_replace",
        "re_match_ta", "re_find_ta", "re_find_all_ta", "re_replace_ta",
        "re_replace_all_ta", "re_split_ta",
        "dns_resolve",
    ];
    KNOWN.contains(&snake_name)
}

/// Convert a parsed `serde_json::Value` into H#'s runtime `Value`.
/// JSON objects become `Value::Struct` (name `"__json"`) so they can be
/// passed around as opaque handles; JSON arrays become `Value::Array`.
pub fn json_to_value(j: &Json) -> Value {
    match j {
        Json::Null            => Value::Nil,
        Json::Bool(b)          => Value::Bool(*b),
        Json::Number(n) => {
            if let Some(i) = n.as_i64() { Value::Int(i) }
            else { Value::Float(n.as_f64().unwrap_or(0.0)) }
        }
        Json::String(s)        => Value::Str(s.clone()),
        Json::Array(items)     => Value::Array(items.iter().map(json_to_value).collect()),
        Json::Object(map) => {
            let mut fields = HashMap::new();
            for (k, v) in map {
                fields.insert(k.clone(), json_to_value(v));
            }
            Value::Struct { name: "__json".to_string(), fields }
        }
    }
}

/// Convert an H# runtime `Value` back into a `serde_json::Value` for
/// stringification.
pub fn value_to_json(v: &Value) -> Json {
    match v {
        Value::Nil          => Json::Null,
        Value::Bool(b)       => Json::Bool(*b),
        Value::Int(n)        => Json::Number((*n).into()),
        Value::Float(f)      => serde_json::Number::from_f64(*f).map(Json::Number).unwrap_or(Json::Null),
        Value::Str(s)        => Json::String(s.clone()),
        Value::Array(items)  => Json::Array(items.iter().map(value_to_json).collect()),
        Value::Struct { fields, .. } => {
            let mut map = serde_json::Map::new();
            for (k, v) in fields {
                map.insert(k.clone(), value_to_json(v));
            }
            Json::Object(map)
        }
        _ => Json::Null,
    }
}

/// Compute the new value of a container after a builtin mutating method
/// call, for receivers that are plain `Value::Array` (not user-defined
/// structs — those go through `try_user_method`'s `self`-mutation path
/// instead). Returns `None` for non-mutating methods, in which case the
/// caller should leave the original binding untouched.
pub fn compute_mutated_container(obj: &Value, method: &str, args: &[Value]) -> Option<Value> {
    match (obj, method) {
        (Value::Array(arr), "push") => {
            let mut new_arr = arr.clone();
            new_arr.push(args.first().cloned().unwrap_or(Value::Nil));
            Some(Value::Array(new_arr))
        }
        (Value::Array(arr), "pop") => {
            let mut new_arr = arr.clone();
            new_arr.pop();
            Some(Value::Array(new_arr))
        }
        (Value::Array(arr), "insert") => {
            let idx = args.first().map(|v| v.to_int()).unwrap_or(0).max(0) as usize;
            let val = args.get(1).cloned().unwrap_or(Value::Nil);
            let mut new_arr = arr.clone();
            let idx = idx.min(new_arr.len());
            new_arr.insert(idx, val);
            Some(Value::Array(new_arr))
        }
        (Value::Array(arr), "remove") => {
            let idx = args.first().map(|v| v.to_int()).unwrap_or(0).max(0) as usize;
            let mut new_arr = arr.clone();
            if idx < new_arr.len() { new_arr.remove(idx); }
            Some(Value::Array(new_arr))
        }
        (Value::Array(arr), "clear") => {
            let _ = arr;
            Some(Value::Array(Vec::new()))
        }
        (Value::Array(arr), "sort") => {
            let mut new_arr = arr.clone();
            new_arr.sort_by(|a, b| {
                a.to_float().partial_cmp(&b.to_float()).unwrap_or(std::cmp::Ordering::Equal)
            });
            Some(Value::Array(new_arr))
        }
        // ── HashMap ──────────────────────────────────────────────────────
        (Value::Struct { name, fields }, "insert") if name == "__hashmap" => {
            let key = args.first().map(|v| v.to_string()).unwrap_or_default();
            let val = args.get(1).cloned().unwrap_or(Value::Nil);
            let mut new_fields = fields.clone();
            new_fields.insert(key, val);
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        (Value::Struct { name, fields }, "remove") if name == "__hashmap" => {
            let key = args.first().map(|v| v.to_string()).unwrap_or_default();
            let mut new_fields = fields.clone();
            new_fields.remove(&key);
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        // ── HashSet ──────────────────────────────────────────────────────
        (Value::Struct { name, fields }, "insert") if name == "__hashset" => {
            let val = args.first().cloned().unwrap_or(Value::Nil);
            let items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            let mut new_items = items;
            if !new_items.iter().any(|v| values_equal(v, &val)) {
                new_items.push(val);
            }
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(new_items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        (Value::Struct { name, fields }, "remove") if name == "__hashset" => {
            let val = args.first().cloned().unwrap_or(Value::Nil);
            let items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            let new_items: Vec<Value> = items.into_iter().filter(|v| !values_equal(v, &val)).collect();
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(new_items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        // ── Queue (FIFO: push appends, pop removes from the front) ────────
        (Value::Struct { name, fields }, "push") if name == "__queue" => {
            let val = args.first().cloned().unwrap_or(Value::Nil);
            let mut items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            items.push(val);
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        (Value::Struct { name, fields }, "pop") if name == "__queue" => {
            let mut items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            if !items.is_empty() { items.remove(0); }
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        // ── Stack (LIFO: push appends, pop removes from the back) ─────────
        (Value::Struct { name, fields }, "push") if name == "__stack" => {
            let val = args.first().cloned().unwrap_or(Value::Nil);
            let mut items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            items.push(val);
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        (Value::Struct { name, fields }, "pop") if name == "__stack" => {
            let mut items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            items.pop();
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        _ => None,
    }
}

pub fn values_equal(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Int(a), Value::Int(b)) => a == b,
        (Value::Float(a), Value::Float(b)) => a == b,
        (Value::Int(a), Value::Float(b)) | (Value::Float(b), Value::Int(a)) => (*a as f64) == *b,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Str(a), Value::Str(b)) => a == b,
        (Value::Bytes(a), Value::Bytes(b)) => a == b,
        (Value::Nil, Value::Nil) => true,
        (Value::Array(a), Value::Array(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| values_equal(x, y))
        }
        (Value::Tuple(a), Value::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| values_equal(x, y))
        }
        (Value::Struct { name: na, fields: fa }, Value::Struct { name: nb, fields: fb }) => {
            na == nb && fa.len() == fb.len()
                && fa.iter().all(|(k, v)| fb.get(k).map(|v2| values_equal(v, v2)).unwrap_or(false))
        }
        _ => false,
    }
}

pub fn compare_values(a: Value, b: Value, f: impl Fn(f64, f64) -> bool) -> Result<Value, RuntimeError> {
    let result = match (a, b) {
        (Value::Int(a), Value::Int(b)) => f(a as f64, b as f64),
        (Value::Float(a), Value::Float(b)) => f(a, b),
        (Value::Int(a), Value::Float(b)) => f(a as f64, b),
        (Value::Float(a), Value::Int(b)) => f(a, b as f64),
        (a, b) => return Err(RuntimeError::TypeError(format!("cannot compare {} and {}", a, b))),
    };
    Ok(Value::Bool(result))
}
