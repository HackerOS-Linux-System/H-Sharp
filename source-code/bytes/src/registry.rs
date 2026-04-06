/// bytes registry — uses same vira-io/repository as vira

use serde::{Deserialize, Serialize};
use std::io::{Read, Write};

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct Registry { pub packages: Vec<PackageEntry> }

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageEntry {
    pub name: String, pub latest: String,
    pub git: Option<String>, pub description: Option<String>,
}

impl Registry {
    pub fn fetch() -> Self {
        if let Ok(body) = http_get("raw.githubusercontent.com",
            "/vira-io/repository/main/repo-list.json") {
            return serde_json::from_str(&body).unwrap_or_default();
        }
        Self::default()
    }
    pub fn find(&self, name: &str) -> Option<&PackageEntry> {
        self.packages.iter().find(|p| p.name == name)
    }
}

fn http_get(host: &str, path: &str) -> anyhow::Result<String> {
    let addr = format!("{}:80", host).parse::<std::net::SocketAddr>()?;
    let mut s = std::net::TcpStream::connect_timeout(&addr, std::time::Duration::from_secs(5))?;
    write!(s, "GET {} HTTP/1.0\r\nHost: {}\r\nUser-Agent: bytes/0.1\r\nConnection: close\r\n\r\n", path, host)?;
    s.set_read_timeout(Some(std::time::Duration::from_secs(10))).ok();
    let mut r = String::new(); s.read_to_string(&mut r)?;
    Ok(r.split_once("\r\n\r\n").map(|(_, b)| b).unwrap_or(&r).to_string())
}
