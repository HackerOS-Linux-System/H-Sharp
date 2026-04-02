use std::net::TcpStream;
pub fn connect(host: &str, port: u16) -> Result<TcpStream, std::io::Error> {
    TcpStream::connect(format!("{}:{}", host, port))
}
pub fn scan_port(host: &str, port: u16) -> bool {
    TcpStream::connect(format!("{}:{}", host, port)).is_ok()
}
