/// H# Standard Library — Rust implementation
/// These modules are compiled into the H# runtime and available
/// via `import "std:..."` in H# source files.

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

/// Re-exports for the prelude (auto-imported into every H# program)
pub mod prelude {
    pub use crate::io::print::println;
    pub use crate::io::print::print;
    pub use crate::fmt::to_string;
}
