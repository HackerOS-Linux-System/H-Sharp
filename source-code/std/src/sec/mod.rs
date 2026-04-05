//! H# Security / cybersec utilities
pub fn xor(data:&[u8],key:&[u8])->Vec<u8>{data.iter().enumerate().map(|(i,&b)|b^key[i%key.len()]).collect()}
pub fn rot13(s:&str)->String{s.chars().map(|c|match c{'a'..='m'|'A'..='M'=>(c as u8+13)as char,'n'..='z'|'N'..='Z'=>(c as u8-13)as char,_=>c}).collect()}
pub fn caesar(s:&str,shift:u8)->String{s.chars().map(|c|match c{'a'..='z'=>(((c as u8-b'a'+shift)%26)+b'a')as char,'A'..='Z'=>(((c as u8-b'A'+shift)%26)+b'A')as char,_=>c}).collect()}
pub fn fnv1a64(data:&[u8])->u64{let mut h:u64=0xcbf29ce484222325;for &b in data{h^=b as u64;h=h.wrapping_mul(0x100000001b3);}h}
pub fn to_hex(data:&[u8])->String{data.iter().map(|b|format!("{:02x}",b)).collect()}
pub fn from_hex(s:&str)->Result<Vec<u8>,String>{if s.len()%2!=0{return Err("odd length".into());}(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).map_err(|e|e.to_string())).collect()}
pub fn is_ipv4(s:&str)->bool{s.split('.').count()==4&&s.split('.').all(|o|o.parse::<u8>().is_ok())}
pub fn scan_port(host:&str,port:u16,timeout_ms:u64)->bool{use std::net::TcpStream;TcpStream::connect_timeout(&format!("{}:{}",host,port).parse().unwrap_or_else(|_|"0.0.0.0:0".parse().unwrap()),std::time::Duration::from_millis(timeout_ms)).is_ok()}
pub fn checksum32(data:&[u8])->u32{let mut crc:u32=0xFFFFFFFF;for &b in data{crc^=b as u32;for _ in 0..8{if crc&1!=0{crc=(crc>>1)^0xEDB88320;}else{crc>>=1;}}}!crc}
