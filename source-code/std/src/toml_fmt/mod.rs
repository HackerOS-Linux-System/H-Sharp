//! H# TOML minimal parser
use std::collections::HashMap;
#[derive(Debug,Clone)]
pub enum TomlValue { Str(String), Int(i64), Float(f64), Bool(bool), Array(Vec<TomlValue>), Table(HashMap<String,TomlValue>) }
pub fn parse(s: &str) -> Result<HashMap<String,TomlValue>,String> {
    let mut map=HashMap::new(); let mut section=String::new();
    for line in s.lines() {
        let line=line.trim(); if line.is_empty()||line.starts_with('#'){continue;}
        if line.starts_with('[')&&line.ends_with(']')&&!line.starts_with("[["){section=line[1..line.len()-1].to_string();continue;}
        if let Some(eq)=line.find('=') {
            let key_raw=line[..eq].trim();
            let key=if section.is_empty(){key_raw.to_string()}else{format!("{}.{}",section,key_raw)};
            let val_str=line[eq+1..].trim();
            map.insert(key,parse_val(val_str));
        }
    }
    Ok(map)
}
fn parse_val(s:&str)->TomlValue{
    if s=="true"{return TomlValue::Bool(true);}if s=="false"{return TomlValue::Bool(false);}
    if s.starts_with('"')&&s.ends_with('"'){return TomlValue::Str(s[1..s.len()-1].to_string());}
    if let Ok(i)=s.parse::<i64>(){return TomlValue::Int(i);}
    if let Ok(f)=s.parse::<f64>(){return TomlValue::Float(f);}
    TomlValue::Str(s.to_string())
}
