use std::path::PathBuf;

/// Every way building, reading or verifying a `.hlib` archive can fail.
#[derive(thiserror::Error, Debug)]
pub enum HlibError {
    #[error("i/o error at {path}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },

    #[error("i/o error: {0}")]
    IoPlain(#[from] std::io::Error),

    #[error("manifest (de)serialization failed: {0}")]
    Json(#[from] serde_json::Error),

    #[error("`{0}` is not a valid .hlib archive (not a zstd-compressed tar / bad header)")]
    NotAnArchive(PathBuf),

    #[error("archive is missing required entry `{0}`")]
    MissingEntry(String),

    #[error("archive entry `{path}` failed checksum verification (expected {expected}, got {actual})")]
    ChecksumMismatch {
        path: String,
        expected: String,
        actual: String,
    },

    #[error("CHECKSUMS.sha256 line is malformed: `{0}`")]
    MalformedChecksumLine(String),

    #[error("archive is not signed (no SIGNATURE.ed25519 entry) — cannot verify")]
    Unsigned,

    #[error("ed25519 signature verification failed for this archive")]
    BadSignature,

    #[error("invalid ed25519 key material: {0}")]
    BadKey(String),

    #[error("hlib spec version {found} is newer than the highest version this reader understands ({supported})")]
    UnsupportedSpecVersion { found: u32, supported: u32 },

    #[error("hlib was written for H# edition \"{found}\", which this toolchain doesn't support (supported: {supported}) — upgrade H#, or rebuild the library with a supported edition")]
    UnsupportedEdition { found: String, supported: String },

    #[error("unknown artifact kind `{0}`")]
    UnknownArtifactKind(String),

    #[error("unknown target language `{0}` (expected one of: hsharp, hackerlang, hackerscript)")]
    UnknownLanguage(String),

    #[error("duplicate archive entry path `{0}`")]
    DuplicatePath(String),
}

pub type Result<T> = std::result::Result<T, HlibError>;
