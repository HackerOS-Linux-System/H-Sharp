//! H# String utilities
pub fn trim(s:&str)->&str{s.trim()} pub fn to_upper(s:&str)->String{s.to_uppercase()} pub fn to_lower(s:&str)->String{s.to_lowercase()}
pub fn contains(s:&str,p:&str)->bool{s.contains(p)} pub fn starts_with(s:&str,p:&str)->bool{s.starts_with(p)} pub fn ends_with(s:&str,p:&str)->bool{s.ends_with(p)}
pub fn replace(s:&str,from:&str,to:&str)->String{s.replace(from,to)}
pub fn split(s:&str,sep:&str)->Vec<String>{s.split(sep).map(String::from).collect()}
pub fn join(parts:&[String],sep:&str)->String{parts.join(sep)}
pub fn repeat(s:&str,n:usize)->String{s.repeat(n)}
pub fn pad_left(s:&str,w:usize,c:char)->String{if s.len()>=w{s.to_string()}else{format!("{}{}",c.to_string().repeat(w-s.len()),s)}}
pub fn pad_right(s:&str,w:usize,c:char)->String{if s.len()>=w{s.to_string()}else{format!("{}{}",s,c.to_string().repeat(w-s.len()))}}
pub fn char_count(s:&str)->usize{s.chars().count()} pub fn is_empty(s:&str)->bool{s.is_empty()}
