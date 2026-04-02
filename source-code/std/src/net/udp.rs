use std::net::UdpSocket;
pub fn bind(addr: &str) -> Result<UdpSocket, std::io::Error> { UdpSocket::bind(addr) }
