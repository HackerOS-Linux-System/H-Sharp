use serde::{Deserialize, Serialize};
use std::collections::HashMap;

const LOCKFILE: &str = "bytes.lock";

#[derive(Debug, Deserialize, Serialize, Default)]
pub struct LockFile {
    pub version: u32,
    pub packages: HashMap<String, LockedPackage>,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct LockedPackage {
    pub version: String,
    pub checksum: Option<String>,
    pub url: Option<String>,
}

impl LockFile {
    pub fn read() -> Self {
        std::fs::read_to_string(LOCKFILE)
            .ok()
            .and_then(|s| serde_json::from_str(&s).ok())
            .unwrap_or(LockFile { version: 1, packages: HashMap::new() })
    }

    pub fn write(&self) {
        let s = serde_json::to_string_pretty(self).unwrap();
        std::fs::write(LOCKFILE, s).ok();
    }

    pub fn lock(&mut self, name: &str, version: &str, url: Option<String>, checksum: Option<String>) {
        self.packages.insert(name.to_string(), LockedPackage {
            version: version.to_string(),
            checksum,
            url,
        });
    }

    pub fn unlock(&mut self, name: &str) {
        self.packages.remove(name);
    }
}
