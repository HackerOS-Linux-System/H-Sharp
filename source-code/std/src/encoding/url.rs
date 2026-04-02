pub fn encode(s: &str) -> String {
    s.bytes().flat_map(|b| {
        if b.is_ascii_alphanumeric() || b".-_~".contains(&b) {
            vec![b as char]
        } else {
            format!("%{:02X}", b).chars().collect()
        }
    }).collect()
}
