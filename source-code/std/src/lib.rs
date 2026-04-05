//! H# Standard Library
//! Import via: use "std -> module -> sub" from "alias"

pub mod io;
pub mod crypto;
pub mod net;
pub mod fs;
pub mod process;
pub mod encoding;
pub mod regex;
pub mod time;
pub mod collections;
pub mod fmt;
pub mod bytes_util;
// Data formats
pub mod json;
pub mod yaml;
pub mod toml_fmt;
// Security
pub mod sec;
// HTTP
pub mod http;
// OS
pub mod os;
// Math
pub mod math;
// String utils
pub mod strings;
// Path
pub mod path;
// Env
pub mod env;

pub mod prelude {
    pub use crate::io::print::{write, writeln};
    pub use crate::fmt::to_string;
}
