//! H# JSON parsing and serialization
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum JsonValue {
    Null, Bool(bool), Number(f64), Str(String),
    Array(Vec<JsonValue>), Object(HashMap<String, JsonValue>),
}

impl JsonValue {
    pub fn as_str(&self) -> Option<&str> { if let Self::Str(s)=self {Some(s)} else {None} }
    pub fn as_f64(&self) -> Option<f64>  { if let Self::Number(n)=self {Some(*n)} else {None} }
    pub fn as_bool(&self)->Option<bool>  { if let Self::Bool(b)=self {Some(*b)} else {None} }
    pub fn is_null(&self)->bool          { matches!(self,Self::Null) }
    pub fn to_json(&self) -> String {
        match self {
            Self::Null      => "null".into(),
            Self::Bool(b)   => b.to_string(),
            Self::Number(n) => if n.fract()==0.0 { format!("{}",*n as i64) } else { format!("{}",n) },
            Self::Str(s)    => format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"").replace("\\n","\\n")),
            Self::Array(a)  => format!("[{}]", a.iter().map(|v|v.to_json()).collect::<Vec<_>>().join(",")),
            Self::Object(m) => { let items:Vec<_>=m.iter().map(|(k,v)|format!("\"{}\": {}",k,v.to_json())).collect(); format!("{{{}}}",items.join(",")) }
        }
    }
}

pub fn parse(s: &str) -> Result<JsonValue, String> {
    let mut chars = s.trim().chars().peekable();
    parse_val(&mut chars)
}

fn skip_ws(chars: &mut std::iter::Peekable<impl Iterator<Item=char>>) {
    while chars.peek().map(|c| c.is_ascii_whitespace()).unwrap_or(false) { chars.next(); }
}

fn parse_val(chars: &mut std::iter::Peekable<impl Iterator<Item=char>>) -> Result<JsonValue, String> {
    skip_ws(chars);
    match chars.peek() {
        Some('n') => { "null".chars().for_each(|_|{chars.next();}); Ok(JsonValue::Null) }
        Some('t') => { "true".chars().for_each(|_|{chars.next();}); Ok(JsonValue::Bool(true)) }
        Some('f') => { "false".chars().for_each(|_|{chars.next();}); Ok(JsonValue::Bool(false)) }
        Some('"') => { chars.next(); let mut s=String::new(); loop { match chars.next() { Some('"')=>break, Some('\\')=>{ match chars.next(){ Some('n')=>s.push('\n'), Some('t')=>s.push('\t'), Some(c)=>s.push(c), None=>break } }, Some(c)=>s.push(c), None=>break } } Ok(JsonValue::Str(s)) }
        Some('[') => { chars.next(); let mut a=Vec::new(); skip_ws(chars); if chars.peek()==Some(&']'){chars.next();return Ok(JsonValue::Array(a));} loop { a.push(parse_val(chars)?); skip_ws(chars); match chars.next(){Some(']')=>break,Some(',')=>{},_=>return Err("expected , or ]".into())} } Ok(JsonValue::Array(a)) }
        Some('{') => { chars.next(); let mut m=HashMap::new(); skip_ws(chars); if chars.peek()==Some(&'}'){chars.next();return Ok(JsonValue::Object(m));} loop { skip_ws(chars); chars.next(); let mut k=String::new(); loop{match chars.next(){Some('"')=>break,Some(c)=>k.push(c),None=>break}} skip_ws(chars); chars.next(); let v=parse_val(chars)?; m.insert(k,v); skip_ws(chars); match chars.next(){Some('}')=>break,Some(',')=>{},_=>return Err("expected , or }".into())} } Ok(JsonValue::Object(m)) }
        Some(c) if c.is_ascii_digit()||*c=='-' => { let mut s=String::new(); while chars.peek().map(|c|c.is_ascii_digit()||*c=='.'||*c=='e'||*c=='E'||*c=='+'||*c=='-').unwrap_or(false){s.push(chars.next().unwrap());} s.parse::<f64>().map(JsonValue::Number).map_err(|e|e.to_string()) }
        _ => Err("unexpected token".into()),
    }
}

pub fn stringify(v: &JsonValue) -> String { v.to_json() }
