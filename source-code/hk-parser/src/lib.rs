use std::collections::HashMap;
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq)]
pub enum HkValue {
    String(String),
    Number(f64),
    Bool(bool),
    Array(Vec<HkValue>),
    Map(Vec<(String, HkValue)>),  // Vec preserves insertion order
}

impl HkValue {
    pub fn as_str(&self) -> Option<&str> {
        if let Self::String(s) = self { Some(s) } else { None }
    }
    pub fn as_f64(&self) -> Option<f64> {
        if let Self::Number(n) = self { Some(*n) } else { None }
    }
    pub fn as_bool(&self) -> Option<bool> {
        if let Self::Bool(b) = self { Some(*b) } else { None }
    }
    pub fn as_array(&self) -> Option<&[HkValue]> {
        if let Self::Array(a) = self { Some(a) } else { None }
    }
    pub fn as_map(&self) -> Option<&[(String, HkValue)]> {
        if let Self::Map(m) = self { Some(m) } else { None }
    }
    pub fn get(&self, key: &str) -> Option<&HkValue> {
        if let Self::Map(m) = self {
            m.iter().find(|(k,_)| k == key).map(|(_,v)| v)
        } else { None }
    }
    pub fn to_string_val(&self) -> String {
        match self {
            Self::String(s) => s.clone(),
            Self::Number(n) => n.to_string(),
            Self::Bool(b)   => b.to_string(),
            Self::Array(a)  => format!("[{}]", a.iter().map(|v| v.to_string_val()).collect::<Vec<_>>().join(", ")),
            Self::Map(_)    => "<map>".to_string(),
        }
    }
}

pub type HkConfig = Vec<(String, HkValue)>;

#[derive(Debug)]
pub struct HkError(pub String);

impl std::fmt::Display for HkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "hk parse error: {}", self.0)
    }
}

pub fn parse_hk(input: &str) -> Result<HkConfig, HkError> {
    let lines: Vec<&str> = input.lines().collect();
    let mut config: HkConfig = Vec::new();
    let mut i = 0;

    while i < lines.len() {
        let line = lines[i].trim();
        if line.is_empty() || line.starts_with('!') { i += 1; continue; }

        if line.starts_with('[') {
            let close = line.find(']').ok_or_else(|| HkError(format!("unclosed [ at line {}", i+1)))?;
            let section = line[1..close].trim().to_string();
            if section.is_empty() { return Err(HkError(format!("empty section at line {}", i+1))); }

            let start = i + 1;
            let mut end = start;
            while end < lines.len() {
                let nl = lines[end].trim();
                if !nl.is_empty() && !nl.starts_with('!') && nl.starts_with('[') { break; }
                end += 1;
            }
            let section_val = parse_map(1, &lines[start..end], start)?;
            config.push((section, HkValue::Map(section_val)));
            i = end;
        } else {
            i += 1;
        }
    }
    Ok(config)
}

fn parse_map(level: usize, lines: &[&str], base: usize) -> Result<Vec<(String, HkValue)>, HkError> {
    let prefix = "-".repeat(level) + ">";
    let mut map: Vec<(String, HkValue)> = Vec::new();
    let mut i = 0;

    while i < lines.len() {
        let line = lines[i].trim();
        if line.is_empty() || line.starts_with('!') { i += 1; continue; }

        let dashes = line.chars().take_while(|&c| c == '-').count();
        if dashes == 0 { i += 1; continue; }
        if dashes != level { break; }

        let rest = line[dashes..].trim();
        if !rest.starts_with('>') {
            return Err(HkError(format!("expected '>' at line {}", base + i + 1)));
        }
        let after = rest[1..].trim();
        if after.is_empty() {
            return Err(HkError(format!("empty key at line {}", base + i + 1)));
        }

        if let Some(arrow) = after.find("=>") {
            let key = unquote(after[..arrow].trim());
            let val = parse_value(after[arrow+2..].trim(), base + i)?;
            map.push((key, val));
            i += 1;
        } else {
            // sub-map header
            let key = unquote(after.trim());
            let next_level = level + 1;
            let sub_prefix_count = next_level;
            let mut j = i + 1;
            while j < lines.len() {
                let sl = lines[j].trim();
                if sl.is_empty() || sl.starts_with('!') { j += 1; continue; }
                let dc = sl.chars().take_while(|&c| c == '-').count();
                if dc < next_level { break; }
                j += 1;
            }
            let sub = parse_map(next_level, &lines[i+1..j], base + i + 1)?;
            map.push((key, HkValue::Map(sub)));
            i = j;
        }
    }
    Ok(map)
}

fn unquote(s: &str) -> String {
    let s = s.trim();
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        s[1..s.len()-1].replace("\\\"", "\"")
    } else {
        s.to_string()
    }
}

fn parse_value(s: &str, line: usize) -> Result<HkValue, HkError> {
    let s = s.trim();
    if s.is_empty() { return Err(HkError(format!("empty value at line {}", line+1))); }

    if s.starts_with('[') && s.ends_with(']') {
        let inner = &s[1..s.len()-1];
        let mut items = Vec::new();
        let mut cur = String::new();
        let mut in_q = false;
        let mut esc = false;
        for c in inner.chars() {
            if esc { cur.push(c); esc = false; continue; }
            match c {
                '\\' => esc = true,
                '"' => { in_q = !in_q; cur.push(c); }
                ',' if !in_q => {
                    let t = cur.trim().to_string();
                    if !t.is_empty() { items.push(parse_simple(t.trim(), line)?); }
                    cur.clear();
                }
                _ => cur.push(c),
            }
        }
        let t = cur.trim().to_string();
        if !t.is_empty() { items.push(parse_simple(t.trim(), line)?); }
        return Ok(HkValue::Array(items));
    }
    parse_simple(s, line)
}

fn parse_simple(s: &str, _line: usize) -> Result<HkValue, HkError> {
    let s = s.trim();
    if s.eq_ignore_ascii_case("true")  { return Ok(HkValue::Bool(true)); }
    if s.eq_ignore_ascii_case("false") { return Ok(HkValue::Bool(false)); }
    if let Ok(n) = f64::from_str(s) { return Ok(HkValue::Number(n)); }
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        let inner = &s[1..s.len()-1];
        let mut r = String::new();
        let mut chars = inner.chars();
        while let Some(c) = chars.next() {
            if c == '\\' {
                match chars.next() {
                    Some('n') => r.push('\n'),
                    Some('t') => r.push('\t'),
                    Some('r') => r.push('\r'),
                    Some('"') => r.push('"'),
                    Some('\\') => r.push('\\'),
                    Some(c) => r.push(c),
                    None => {}
                }
            } else { r.push(c); }
        }
        return Ok(HkValue::String(r));
    }
    Ok(HkValue::String(s.to_string()))
}

pub fn load_hk_file(path: &str) -> Result<HkConfig, HkError> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| HkError(format!("cannot read {}: {}", path, e)))?;
    parse_hk(&content)
}

/// Get a value from config by section.key path
pub fn get(config: &HkConfig, section: &str, key: &str) -> Option<String> {
    config.iter()
        .find(|(s,_)| s == section)
        .and_then(|(_,v)| v.get(key))
        .map(|v| v.to_string_val())
}

/// Get nested: section.subsection.key
pub fn get_nested(config: &HkConfig, section: &str, sub: &str, key: &str) -> Option<String> {
    config.iter()
        .find(|(s,_)| s == section)
        .and_then(|(_,v)| v.get(sub))
        .and_then(|v| v.get(key))
        .map(|v| v.to_string_val())
}
