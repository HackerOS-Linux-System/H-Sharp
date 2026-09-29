use serde::{Deserialize, Serialize};

use crate::error::{HlibError, Result};

/// Current version of the on-disk `.hlib` layout / `manifest.json` schema
/// this crate reads and writes. Bumped whenever the archive layout (not
/// just the language-specific payload inside it) changes in a
/// backwards-incompatible way.
pub const HLIB_SPEC_VERSION: u32 = 1;

/// Which HackerOS language toolchain produced (and can natively consume)
/// this `.hlib`. A single `.hlib` always has exactly one *producer*
/// language, but is meant to be readable by all three — that's the
/// entire point of the format — so the header/AST/bytecode split exists
/// precisely to let a consumer written in a different language than the
/// producer still link against it (see `ArtifactKind`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Language {
    Hsharp,
    Hackerlang,
    Hackerscript,
}

impl Language {
    pub fn as_str(&self) -> &'static str {
        match self {
            Language::Hsharp => "hsharp",
            Language::Hackerlang => "hackerlang",
            Language::Hackerscript => "hackerscript",
        }
    }

    pub fn from_str(s: &str) -> Result<Self> {
        match s.to_ascii_lowercase().as_str() {
            "hsharp" | "h#" | "h-sharp" => Ok(Language::Hsharp),
            "hackerlang" | "hl" | "hacker-lang" => Ok(Language::Hackerlang),
            "hackerscript" | "hcs" | "hacker-script" => Ok(Language::Hackerscript),
            other => Err(HlibError::UnknownLanguage(other.to_string())),
        }
    }
}

/// What kind of payload a single archive entry listed in
/// `manifest.json`'s `artifacts` array is. A `.hlib` need not contain
/// every kind — a pure-source generic-only library might ship only
/// `Ast` + `Header`; a library with no generics/macros to re-expand
/// might ship only `SharedObject` + `Header`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ArtifactKind {
    /// A native `.so`/`.dylib`/`.dll` built from the producer language's
    /// compiler (H#'s LLVM backend, HackerScript's generated+cargo-built
    /// `cdylib`). Loaded with `dlopen`/`libloading` by any consumer.
    SharedObject,
    /// Hacker Lang bytecode (`.hlbc`), interpreted/JIT-ed directly by
    /// `hl_jit` — Hacker Lang programs never need a `.so` for pure
    /// Hacker Lang code, only for FFI.
    Bytecode,
    /// Serialized AST of every exported generic function/struct/trait
    /// impl and every macro definition, in the producer's own AST shape
    /// (tagged by `language` in the manifest) — needed because generics
    /// and macros are expanded/monomorphized by the *consumer's*
    /// compiler at the call site, so it needs the real AST, not just a
    /// compiled symbol. JSON-encoded so any of the three toolchains can
    /// at least parse the envelope even if only the producer's own
    /// front-end can fully re-interpret the embedded node shapes.
    Ast,
    /// Language-agnostic interface description (see `Header` below) —
    /// what every other language's compiler/interpreter reads to link
    /// against `SharedObject`/`Bytecode` artifacts without needing the
    /// original source at all.
    Header,
    /// Arbitrary extra file (docs, license, icon, …) carried through
    /// unmodified. Not interpreted by the loader.
    Extra,
}

/// One entry in `manifest.json`'s `artifacts` list — one file inside the
/// archive, plus enough metadata to decide whether/how to load it
/// without having to open it first.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Artifact {
    /// Path of this entry inside the tar, e.g.
    /// `native/x86_64-unknown-linux-gnu/libfoo.so`.
    pub path: String,
    pub kind: ArtifactKind,
    /// Target triple this artifact was built for. `None` for
    /// target-independent artifacts (bytecode, AST, headers).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target: Option<String>,
    /// Lowercase hex SHA-256 of this entry's raw bytes. Redundant with
    /// `CHECKSUMS.sha256` inside the archive (kept here too so a reader
    /// can sanity-check a single artifact without re-hashing the whole
    /// archive).
    pub sha256: String,
    /// Size in bytes, purely informational (for `hlib inspect`-style
    /// listings and progress bars during extraction).
    pub size: u64,
}

/// One exported symbol, described language-agnostically enough that a
/// *different* language's compiler can generate its own native `extern`
/// binding declaration from it without ever seeing the producer's
/// source.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExportedSymbol {
    pub name: String,
    pub kind: ExportedSymbolKind,
    /// Human-readable signature exactly as the producer language would
    /// print it (`fn add(a: i64, b: i64) -> i64`, `fun add(a: Int, b: Int) -> Int`, …) —
    /// informational only, not parsed by consumers.
    pub signature: String,
    /// Parameter types, already lowered to the small set of ABI-stable
    /// primitive/pointer types every HackerOS language agrees on (see
    /// `AbiType`). Empty for non-callable exports (plain constants,
    /// struct/enum type exports with no associated function).
    #[serde(default)]
    pub params: Vec<AbiType>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub returns: Option<AbiType>,
    /// True if this export carries unresolved type parameters and can
    /// only be used via the `Ast` artifact (monomorphized by the
    /// consumer), not by linking straight against the `SharedObject`.
    #[serde(default)]
    pub generic: bool,
    /// True if this export is a macro (source-level only — never present
    /// in `SharedObject`, always expanded from the `Ast` artifact).
    #[serde(default)]
    pub is_macro: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExportedSymbolKind {
    Function,
    Struct,
    Enum,
    Trait,
    Const,
    TypeAlias,
}

/// The small, deliberately boring set of ABI-stable types every HackerOS
/// language toolchain agrees maps to the same C-compatible bit pattern —
/// this is what lets a `SharedObject` compiled by one language's backend
/// be called correctly from another's FFI layer purely by reading
/// `manifest.json`, with no shared header file. Anything richer
/// (generics, language-specific struct layouts, closures) has to go
/// through the `Ast` artifact instead and be recompiled per-consumer.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "type")]
pub enum AbiType {
    I8, I16, I32, I64,
    U8, U16, U32, U64,
    F32, F64,
    Bool,
    /// A raw byte pointer (`*const u8`/`*mut u8`) — used for owned/borrowed
    /// UTF-8 strings and raw buffers, always paired with a length param
    /// per each language's own convention (documented per-symbol in
    /// `signature`, since HackerOS languages don't yet agree on a single
    /// fat-pointer ABI).
    Ptr,
    /// Opaque pointer to a producer-language-defined struct the consumer
    /// cannot construct directly (`native/target/*` layout is unspecified
    /// across languages) — pass-through handle only.
    Opaque { struct_name: String },
    Void,
}

/// One declared dependency on another `.hlib`. Purely informational for
/// v1 — no transitive resolver is shipped here; each language's own
/// package manager (`bit`, `virus`, Hacker Lang's env system) is
/// expected to fetch these before the compiler tries to link.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Dependency {
    pub name: String,
    pub version_req: String,
}

/// Signature block. `None` (the field is simply absent from
/// `manifest.json`) means the archive is unsigned — `hlib_core` never
/// invents or requires a signature, since plenty of purely local/dev
/// builds have no reason to carry one.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SignatureInfo {
    pub algorithm: String, // always "ed25519" in v1
    /// Lowercase hex of the 32-byte Ed25519 public key that produced
    /// `SIGNATURE.ed25519`. Consumers compare this (or its fingerprint)
    /// against a trust store; `hlib_core` itself only checks the math.
    pub public_key: String,
    /// Name of the archive entry the signature was computed over —
    /// always `CHECKSUMS.sha256` in v1, kept as a named field instead of
    /// a hardcoded assumption so a future spec bump could sign something
    /// else without breaking this struct's shape.
    pub signed_entry: String,
}

/// The full contents of `manifest.json` — the one file every `.hlib`
/// reader looks at first.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Manifest {
    pub hlib_spec_version: u32,
    pub name: String,
    pub version: String,
    pub language: Language,
    /// Version string of the compiler/toolchain that produced this
    /// archive (e.g. H#'s `0.9.0`) — informational, for diagnostics.
    #[serde(default)]
    pub language_version: String,
    /// ABI generation of the `SharedObject` artifacts in this archive.
    /// Consumers refuse to link against a `SharedObject` whose
    /// `abi_version` they don't recognize, even if `hlib_spec_version`
    /// (the *container* format) matches — the container and the native
    /// calling convention are versioned independently.
    #[serde(default = "default_abi_version")]
    pub abi_version: u32,
    #[serde(default)]
    pub description: String,
    #[serde(default)]
    pub authors: Vec<String>,
    /// RFC 3339 UTC timestamp of when `build()` produced the archive.
    pub created_at: String,
    #[serde(default)]
    pub dependencies: Vec<Dependency>,
    pub artifacts: Vec<Artifact>,
    #[serde(default)]
    pub exports: Vec<ExportedSymbol>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub signature: Option<SignatureInfo>,
}

fn default_abi_version() -> u32 {
    1
}

impl Manifest {
    /// Reject archives built against a spec version newer than this
    /// build of `hlib_core` understands. Older manifests are always
    /// accepted (fields added since default via `#[serde(default)]`).
    pub fn check_supported(&self) -> Result<()> {
        if self.hlib_spec_version > HLIB_SPEC_VERSION {
            return Err(HlibError::UnsupportedSpecVersion {
                found: self.hlib_spec_version,
                supported: HLIB_SPEC_VERSION,
            });
        }
        Ok(())
    }

    pub fn artifacts_of_kind(&self, kind: ArtifactKind) -> impl Iterator<Item = &Artifact> {
        self.artifacts.iter().filter(move |a| a.kind == kind)
    }

    /// Convenience: the `SharedObject` artifact matching `target`
    /// exactly, if this archive ships native code for that triple.
    pub fn shared_object_for(&self, target: &str) -> Option<&Artifact> {
        self.artifacts
            .iter()
            .find(|a| a.kind == ArtifactKind::SharedObject && a.target.as_deref() == Some(target))
    }
}
