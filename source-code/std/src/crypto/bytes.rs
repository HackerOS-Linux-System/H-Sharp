pub fn xor(data: &[u8], key: &[u8]) -> Vec<u8> {
    data.iter().enumerate()
        .map(|(i, &b)| b ^ key[i % key.len()])
        .collect()
}
pub fn rot13(data: &str) -> String {
    data.chars().map(|c| match c {
        'a'..='m' | 'A'..='M' => (c as u8 + 13) as char,
        'n'..='z' | 'N'..='Z' => (c as u8 - 13) as char,
        _ => c,
    }).collect()
}
