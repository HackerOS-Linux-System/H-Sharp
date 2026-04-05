//! H# OS interface
pub fn platform()->&'static str{
    #[cfg(target_os="linux")]{return "linux";}
    #[cfg(target_os="windows")]{return "windows";}
    #[cfg(target_os="macos")]{return "macos";}
    #[allow(unreachable_code)] "unknown"
}
pub fn hostname()->String{std::fs::read_to_string("/etc/hostname").map(|s|s.trim().to_string()).unwrap_or_else(|_|"localhost".to_string())}
pub fn username()->String{std::env::var("USER").or_else(|_|std::env::var("USERNAME")).unwrap_or_else(|_|"user".to_string())}
pub fn env_var(k:&str)->Option<String>{std::env::var(k).ok()}
pub fn home_dir()->String{std::env::var("HOME").or_else(|_|std::env::var("USERPROFILE")).unwrap_or_else(|_|".".to_string())}
