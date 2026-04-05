//! H# Environment variables
pub fn get(k:&str)->Option<String>{std::env::var(k).ok()}
pub fn get_or(k:&str,def:&str)->String{std::env::var(k).unwrap_or_else(|_|def.to_string())}
pub fn set(k:&str,v:&str){std::env::set_var(k,v);}
pub fn remove(k:&str){std::env::remove_var(k);}
pub fn all()->Vec<(String,String)>{std::env::vars().collect()}
pub fn args()->Vec<String>{std::env::args().collect()}
pub fn cwd()->String{std::env::current_dir().map(|p|p.display().to_string()).unwrap_or_else(|_|".".to_string())}
