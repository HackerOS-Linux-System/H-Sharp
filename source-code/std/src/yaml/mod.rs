//! H# YAML minimal parser
use std::collections::HashMap;
#[derive(Debug,Clone)]
pub enum YamlValue { Null, Bool(bool), Number(f64), Str(String), Seq(Vec<YamlValue>), Map(HashMap<String,YamlValue>) }
pub fn parse(s: &str) -> Result<YamlValue, String> {
    let mut map = HashMap::new();
    for line in s.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') { continue; }
        if let Some(colon) = line.find(": ") {
            let key = line[..colon].trim().to_string();
            let val = line[colon+2..].trim();
            map.insert(key, parse_scalar(val));
        }
    }
    Ok(YamlValue::Map(map))
}
fn parse_scalar(s: &str) -> YamlValue {
    if s=="null"||s=="~" { return YamlValue::Null; }
    if s=="true"  { return YamlValue::Bool(true); }
    if s=="false" { return YamlValue::Bool(false); }
    if let Ok(n)=s.parse::<f64>() { return YamlValue::Number(n); }
    YamlValue::Str(s.trim_matches('"').trim_matches('\'').to_string())
}
pub fn stringify(v: &YamlValue) -> String {
    match v {
        YamlValue::Null      => "null".into(),
        YamlValue::Bool(b)   => b.to_string(),
        YamlValue::Number(n) => n.to_string(),
        YamlValue::Str(s)    => s.clone(),
        YamlValue::Seq(a)    => a.iter().map(|v|format!("- {}",stringify(v))).collect::<Vec<_>>().join("\n"),
        YamlValue::Map(m)    => m.iter().map(|(k,v)|format!("{}: {}",k,stringify(v))).collect::<Vec<_>>().join("\n"),
    }
}
