//! H# Path utilities
pub fn join(base:&str,part:&str)->String{std::path::Path::new(base).join(part).display().to_string()}
pub fn parent(p:&str)->String{std::path::Path::new(p).parent().map(|p|p.display().to_string()).unwrap_or_else(||".".to_string())}
pub fn filename(p:&str)->String{std::path::Path::new(p).file_name().map(|n|n.to_string_lossy().to_string()).unwrap_or_default()}
pub fn extension(p:&str)->String{std::path::Path::new(p).extension().map(|e|e.to_string_lossy().to_string()).unwrap_or_default()}
pub fn stem(p:&str)->String{std::path::Path::new(p).file_stem().map(|s|s.to_string_lossy().to_string()).unwrap_or_default()}
pub fn exists(p:&str)->bool{std::path::Path::new(p).exists()}
pub fn is_dir(p:&str)->bool{std::path::Path::new(p).is_dir()}
pub fn is_file(p:&str)->bool{std::path::Path::new(p).is_file()}
