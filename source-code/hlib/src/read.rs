use std::collections::BTreeMap;
use std::io::Read;
use std::path::Path;

use sha2::{Digest, Sha256};

use crate::error::{HlibError, Result};
use crate::manifest::Manifest;
use crate::sign;

const CHECKSUMS_ENTRY: &str = "CHECKSUMS.sha256";
const SIGNATURE_ENTRY: &str = "SIGNATURE.ed25519";
const MANIFEST_ENTRY: &str = "manifest.json";

fn sha256_hex(data: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hex::encode(hasher.finalize())
}

/// An opened `.hlib` archive, fully decompressed and indexed in memory.
/// `.hlib` archives are meant to be small (a library, not a monolith),
/// so reading the whole thing up front keeps the API simple — no
/// streaming reader needed.
pub struct HlibArchive {
    pub manifest: Manifest,
    entries: BTreeMap<String, Vec<u8>>,
}

impl HlibArchive {
    /// Opens and decompresses `path`, parses `manifest.json`, and
    /// returns the archive. Does **not** verify checksums or signature —
    /// call `verify_checksums()` / `verify_signature()` explicitly,
    /// since a caller that only wants to peek at metadata (`hlib
    /// inspect`) shouldn't pay for a full hash pass, and a caller that's
    /// about to `dlopen` untrusted code definitely should.
    pub fn open(path: &Path) -> Result<Self> {
        let compressed = std::fs::read(path).map_err(|e| HlibError::Io {
            path: path.to_path_buf(),
            source: e,
        })?;

        let tar_bytes = zstd::stream::decode_all(compressed.as_slice())
            .map_err(|_| HlibError::NotAnArchive(path.to_path_buf()))?;

        let mut entries = BTreeMap::new();
        let mut archive = tar::Archive::new(tar_bytes.as_slice());
        for file in archive
            .entries()
            .map_err(|_| HlibError::NotAnArchive(path.to_path_buf()))?
        {
            let mut file = file.map_err(|_| HlibError::NotAnArchive(path.to_path_buf()))?;
            let entry_path = file
                .path()
                .map_err(|_| HlibError::NotAnArchive(path.to_path_buf()))?
                .to_string_lossy()
                .to_string();
            let mut buf = Vec::new();
            file.read_to_end(&mut buf).map_err(|e| HlibError::Io {
                path: path.to_path_buf(),
                source: e,
            })?;
            entries.insert(entry_path, buf);
        }

        let manifest_bytes = entries
            .get(MANIFEST_ENTRY)
            .ok_or_else(|| HlibError::MissingEntry(MANIFEST_ENTRY.to_string()))?;
        let manifest: Manifest = serde_json::from_slice(manifest_bytes)?;
        manifest.check_supported()?;

        Ok(Self { manifest, entries })
    }

    /// Raw bytes of one archive entry by its path (e.g. the `path` field
    /// of one of `manifest.artifacts`).
    pub fn entry_bytes(&self, path: &str) -> Option<&[u8]> {
        self.entries.get(path).map(|v| v.as_slice())
    }

    pub fn entry_paths(&self) -> impl Iterator<Item = &String> {
        self.entries.keys()
    }

    /// Recomputes SHA-256 for every entry listed in `CHECKSUMS.sha256`
    /// and compares it against what's actually in the archive. This is
    /// the archive's own internal integrity check — it does **not**
    /// prove authenticity (anyone can regenerate `CHECKSUMS.sha256` to
    /// match tampered content); that's what `verify_signature` is for.
    pub fn verify_checksums(&self) -> Result<()> {
        let checksums_bytes = self
            .entries
            .get(CHECKSUMS_ENTRY)
            .ok_or_else(|| HlibError::MissingEntry(CHECKSUMS_ENTRY.to_string()))?;
        let checksums_text = String::from_utf8_lossy(checksums_bytes);

        for line in checksums_text.lines() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            let mut parts = line.splitn(2, "  ");
            let expected = parts
                .next()
                .ok_or_else(|| HlibError::MalformedChecksumLine(line.to_string()))?;
            let entry_path = parts
                .next()
                .ok_or_else(|| HlibError::MalformedChecksumLine(line.to_string()))?;

            let data = self
                .entries
                .get(entry_path)
                .ok_or_else(|| HlibError::MissingEntry(entry_path.to_string()))?;
            let actual = sha256_hex(data);
            if actual != expected {
                return Err(HlibError::ChecksumMismatch {
                    path: entry_path.to_string(),
                    expected: expected.to_string(),
                    actual,
                });
            }
        }
        Ok(())
    }

    /// Verifies `SIGNATURE.ed25519` against `expected_public_key_hex`
    /// (lowercase hex, 32 bytes) covering `CHECKSUMS.sha256`'s exact
    /// bytes. Returns `Err(HlibError::Unsigned)` if the archive carries
    /// no signature at all, and `Err(HlibError::BadSignature)` if it's
    /// present but doesn't verify — callers should treat both as "do not
    /// trust", they're kept distinct only so the error message is
    /// accurate.
    ///
    /// This intentionally takes the expected public key as an explicit
    /// argument rather than trusting `manifest.signature.public_key` —
    /// anyone can re-sign a tampered archive with their *own* keypair
    /// and the embedded public key would still "verify" against itself.
    /// Real trust comes from the caller comparing this key against a
    /// key it already trusts (a lockfile pin, a project's declared
    /// publisher key, etc.), same as `bit.lock`/`virus` pin package
    /// hashes today.
    pub fn verify_signature(&self, expected_public_key_hex: &str) -> Result<()> {
        let sig_bytes = self.entries.get(SIGNATURE_ENTRY).ok_or(HlibError::Unsigned)?;
        let checksums_bytes = self
            .entries
            .get(CHECKSUMS_ENTRY)
            .ok_or_else(|| HlibError::MissingEntry(CHECKSUMS_ENTRY.to_string()))?;

        let verifying_key = sign::verifying_key_from_hex(expected_public_key_hex)?;
        let ok = sign::verify(&verifying_key, checksums_bytes, sig_bytes)?;
        if ok {
            Ok(())
        } else {
            Err(HlibError::BadSignature)
        }
    }

    /// Extracts every archive entry to `dir`, preserving the internal
    /// path layout (`native/<target>/...`, `ast/...`, `headers/...`,
    /// …). Convenience for consumers that want real files on disk (to
    /// `dlopen`, or to feed a `.so` to a system linker) rather than
    /// working from in-memory byte slices.
    pub fn extract_to_dir(&self, dir: &Path) -> Result<()> {
        for (path, data) in &self.entries {
            let dest = dir.join(path);
            if let Some(parent) = dest.parent() {
                std::fs::create_dir_all(parent).map_err(|e| HlibError::Io {
                    path: parent.to_path_buf(),
                    source: e,
                })?;
            }
            std::fs::write(&dest, data).map_err(|e| HlibError::Io {
                path: dest.clone(),
                source: e,
            })?;
        }
        Ok(())
    }
}
