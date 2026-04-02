pub fn to_hex(data: &[u8]) -> String {
    data.iter().map(|b| format!("{:02x}", b)).collect()
}
pub fn from_hex(s: &str) -> Result<Vec<u8>, String> {
    crate::crypto::hex::decode(s)
}
