pub fn to_string<T: std::fmt::Display>(v: T) -> String { v.to_string() }
pub fn format_hex(n: u64) -> String { format!("0x{:x}", n) }
