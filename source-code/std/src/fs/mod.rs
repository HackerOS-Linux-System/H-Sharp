pub use std::fs::{read_to_string, write, remove_file, create_dir_all, read_dir};
pub fn exists(path: &str) -> bool { std::path::Path::new(path).exists() }
