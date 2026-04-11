use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum HclValue {
    Str(String),
    Bool(bool),
    Number(f64),
    List(Vec<HclValue>),
    Block(HashMap<String, HclValue>),
    Null,
}

impl HclValue {
    pub fn as_str(&self) -> Option<&str> {
        if let Self::Str(s) = self { Some(s) } else { None }
    }
    pub fn as_bool(&self) -> Option<bool> {
        if let Self::Bool(b) = self { Some(*b) } else { None }
    }
    pub fn as_list(&self) -> Option<&[HclValue]> {
        if let Self::List(v) = self { Some(v) } else { None }
    }
    pub fn get(&self, key: &str) -> Option<&HclValue> {
        if let Self::Block(m) = self { m.get(key) } else { None }
    }
}

/// Parse a vira.hcl file into a flat key→value map.
pub fn parse(src: &str) -> anyhow::Result<HashMap<String, HclValue>> {
    let mut map = HashMap::new();
    let mut lines = src.lines().peekable();

    while let Some(raw) = lines.next() {
        let line = strip_comment(raw).trim().to_string();
        if line.is_empty() { continue; }

        // Block: key "label" { or key {
        if line.ends_with('{') {
            let header = line.trim_end_matches('{').trim();
            let (key, _label) = parse_block_header(header);
            let block = parse_block_body(&mut lines);
            map.insert(key, HclValue::Block(block));
            continue;
        }

        // Assignment: key = value
        if let Some((k, v)) = parse_assignment(&line) {
            map.insert(k, v);
        }
    }
    Ok(map)
}

fn strip_comment(s: &str) -> &str {
    // HCL comments: # and //
    if let Some(idx) = s.find(" #").or_else(|| s.find(" //")) {
        &s[..idx]
    } else { s }
}

fn parse_block_header(s: &str) -> (String, Option<String>) {
    let parts: Vec<&str> = s.splitn(2, '"').collect();
    let key = parts[0].trim().to_string();
    let label = if parts.len() > 1 {
        Some(parts[1].trim_end_matches('"').to_string())
    } else { None };
    (key, label)
}

fn parse_block_body<'a>(lines: &mut std::iter::Peekable<impl Iterator<Item = &'a str>>) -> HashMap<String, HclValue> {
    let mut map = HashMap::new();
    while let Some(raw) = lines.next() {
        let line = strip_comment(raw).trim().to_string();
        if line == "}" || line.is_empty() { break; }
        if let Some((k, v)) = parse_assignment(&line) {
            map.insert(k, v);
        }
    }
    map
}

fn parse_assignment(line: &str) -> Option<(String, HclValue)> {
    let eq = line.find('=')?;
    let key = line[..eq].trim().to_string();
    let val_str = line[eq+1..].trim();
    let val = parse_value(val_str);
    Some((key, val))
}

fn parse_value(s: &str) -> HclValue {
    let s = s.trim();
    // String
    if s.starts_with('"') && s.ends_with('"') {
        return HclValue::Str(s[1..s.len()-1].to_string());
    }
    // Bool
    if s == "true"  { return HclValue::Bool(true); }
    if s == "false" { return HclValue::Bool(false); }
    // Null
    if s == "null"  { return HclValue::Null; }
    // List
    if s.starts_with('[') && s.ends_with(']') {
        let inner = &s[1..s.len()-1];
        let items: Vec<HclValue> = inner.split(',')
            .map(|item| parse_value(item.trim()))
            .collect();
        return HclValue::List(items);
    }
    // Number
    if let Ok(n) = s.parse::<f64>() { return HclValue::Number(n); }
    // Fallback: string without quotes
    HclValue::Str(s.to_string())
}

/// Serialize a vira.hcl block to string
pub fn serialize_project(name: &str, version: &str, deps: &[(String, String)]) -> String {
    let mut out = String::new();
    out.push_str(&format!("project \"{}\" {{\n", name));
    out.push_str(&format!("  version = \"{}\"\n", version));
    out.push_str("}\n\n");
    if !deps.is_empty() {
        out.push_str("dependencies {\n");
        for (pkg, ver) in deps {
            out.push_str(&format!("  {} = \"{}\"\n", pkg, ver));
        }
        out.push_str("}\n");
    }
    out
}
