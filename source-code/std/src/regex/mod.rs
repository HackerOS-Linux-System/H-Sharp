pub fn is_match(pattern: &str, text: &str) -> bool {
    // Simple literal match for now
    text.contains(pattern)
}
