pub fn read(path: &str) -> Result<String, std::io::Error> { std::fs::read_to_string(path) }
pub fn write(path: &str, content: &str) -> Result<(), std::io::Error> { std::fs::write(path, content) }
pub fn exists(path: &str) -> bool { std::path::Path::new(path).exists() }
