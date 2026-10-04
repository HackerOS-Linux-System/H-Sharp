use std::fmt;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Mutex;

use crate::ast::{ImportKind, Module};
use crate::span::Span;

/// Version of the toolchain that is parsing the file (`0.9.0`), as printed in
/// edition diagnostics.
pub const TOOLCHAIN_VERSION: &str = env!("CARGO_PKG_VERSION");

// ─── Edition registry ────────────────────────────────────────────────────────

/// A known H# edition. Ordered chronologically (`E2026 < E2027 < …`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Edition {
    /// The 2026 edition — the syntax documented in this repository's README
    /// and used by everything under `std/`, `examples/` and `tests/`.
    E2026,
}

/// Lifecycle state of an edition inside *this* toolchain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EditionStatus {
    /// Fully supported.
    Stable,
    /// Still accepted, but files should migrate (a warning is appropriate).
    Deprecated,
}

impl Edition {
    /// Newest edition this toolchain understands.
    pub const LATEST: Edition = Edition::E2026;
    /// Oldest edition this toolchain still accepts.
    pub const OLDEST: Edition = Edition::E2026;
    /// Every edition this toolchain accepts, oldest first.
    pub const ALL: &'static [Edition] = &[Edition::E2026];

    /// The edition's year (`2026`).
    pub fn year(self) -> u32 {
        match self {
            Edition::E2026 => 2026,
        }
    }

    /// The edition's canonical spelling inside `using "…"` (`"2026"`).
    pub fn as_str(self) -> &'static str {
        match self {
            Edition::E2026 => "2026",
        }
    }

    /// Lifecycle state of this edition in the running toolchain.
    pub fn status(self) -> EditionStatus {
        match self {
            Edition::E2026 => EditionStatus::Stable,
        }
    }

    /// One-line human description (used by `h# editions`).
    pub fn summary(self) -> &'static str {
        match self {
            Edition::E2026 => "baseline syntax: `is … end` blocks, `use \"std -> x\"`, `@: mode`, hlib/bit/workspace imports",
        }
    }

    /// Parse the payload of a `using "…"` declaration.
    ///
    /// Accepts exactly the canonical spelling (`"2026"`) — surrounding
    /// whitespace is ignored, nothing else is. Newer-than-known years and
    /// malformed strings are told apart so callers can show the right hint.
    pub fn parse(s: &str) -> Result<Edition, EditionError> {
        let t = s.trim();
        let year: u32 = match t.parse() {
            Ok(y) if t.len() == 4 => y,
            _ => return Err(EditionError::Malformed(s.to_string())),
        };
        for e in Edition::ALL {
            if e.year() == year {
                return Ok(*e);
            }
        }
        if year > Edition::LATEST.year() {
            Err(EditionError::TooNew { year })
        } else {
            Err(EditionError::Retired { year })
        }
    }

    /// Does this edition include `feature`?
    pub fn supports(self, feature: EditionFeature) -> bool {
        self >= feature.since()
    }

    /// `"2026"`-style list of every supported edition, for messages.
    pub fn supported_list() -> String {
        Edition::ALL.iter().map(|e| e.as_str()).collect::<Vec<_>>().join(", ")
    }
}

impl fmt::Display for Edition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl Default for Edition {
    fn default() -> Self {
        default_edition()
    }
}

// ─── Errors ──────────────────────────────────────────────────────────────────

/// Why a `using "…"` payload could not be turned into an [`Edition`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EditionError {
    /// Not a four-digit year (`"twenty"`, `"26"`, `""`).
    Malformed(String),
    /// A well-formed year newer than [`Edition::LATEST`] — the file was
    /// written for a newer H# than this one.
    TooNew { year: u32 },
    /// A well-formed year older than [`Edition::OLDEST`] (or a gap between
    /// shipped editions) — no longer accepted by this toolchain.
    Retired { year: u32 },
}

impl EditionError {
    /// Short message suitable for a diagnostic headline.
    pub fn message(&self) -> String {
        match self {
            EditionError::Malformed(s) => format!(
                "invalid edition `{}` in `using` declaration (expected a four-digit year, e.g. \"{}\")",
                s,
                Edition::LATEST
            ),
            EditionError::TooNew { year } => format!(
                "edition \"{}\" is newer than this H# toolchain (v{}) understands",
                year, TOOLCHAIN_VERSION
            ),
            EditionError::Retired { year } => format!(
                "edition \"{}\" is no longer supported by this H# toolchain (v{})",
                year, TOOLCHAIN_VERSION
            ),
        }
    }

    /// Follow-up hints, one per line.
    pub fn hints(&self) -> Vec<String> {
        let mut h = Vec::new();
        match self {
            EditionError::Malformed(_) => {
                h.push(format!("write it as `using \"{}\"`", Edition::LATEST));
            }
            EditionError::TooNew { year } => {
                h.push(format!(
                    "upgrade H# (`hsharp --version` shows v{}), or change the file to `using \"{}\"`",
                    TOOLCHAIN_VERSION,
                    Edition::LATEST
                ));
                h.push(format!("this file was written for edition {}", year));
            }
            EditionError::Retired { .. } => {
                h.push(format!("migrate the file to `using \"{}\"`", Edition::LATEST));
            }
        }
        h.push(format!("supported editions: {}", Edition::supported_list()));
        h
    }
}

impl fmt::Display for EditionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message())
    }
}

impl std::error::Error for EditionError {}

// ─── Default edition (files without `using`) ─────────────────────────────────

/// `0` = "not overridden, use LATEST".
static DEFAULT_YEAR: AtomicU32 = AtomicU32::new(0);

/// Edition assumed for a file with no `using` declaration.
pub fn default_edition() -> Edition {
    let y = DEFAULT_YEAR.load(Ordering::Relaxed);
    Edition::ALL
        .iter()
        .copied()
        .find(|e| e.year() == y)
        .unwrap_or(Edition::LATEST)
}

/// Override the edition assumed for files without `using` (the CLI's
/// `--edition` flag and the `HSHARP_EDITION` environment variable end up here).
pub fn set_default_edition(e: Edition) {
    DEFAULT_YEAR.store(e.year(), Ordering::Relaxed);
}

/// Reset to "newest known edition" (mainly for tests).
pub fn reset_default_edition() {
    DEFAULT_YEAR.store(0, Ordering::Relaxed);
}

/// Initialise the default edition from `HSHARP_EDITION`, if set and valid.
/// Returns the parse error for an invalid value so the CLI can report it.
pub fn init_default_from_env() -> Result<(), EditionError> {
    match std::env::var("HSHARP_EDITION") {
        Ok(v) if !v.trim().is_empty() => {
            set_default_edition(Edition::parse(&v)?);
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Edition the bundled `std/` and `core/` sources are written in. They ship
/// with the toolchain and carry no `using` line, so they are always read as
/// this edition — *not* as the user's default — which is what lets a project
/// pick any edition without touching how the standard library is parsed.
pub const STD_EDITION: Edition = Edition::E2026;

/// The edition `module` is actually compiled under: its own `using`, or the
/// default for undeclared files. An unparsable declaration cannot reach here
/// via [`crate::parse`] (it is a parse error), so it falls back to the default.
pub fn effective_edition(module: &Module) -> Edition {
    effective_edition_with(module, None)
}

/// Like [`effective_edition`], but an undeclared file falls back to
/// `file_default` (e.g. the `[edition]` of the library's own `Bit.hk`)
/// before the process-wide [`default_edition`].
pub fn effective_edition_with(module: &Module, file_default: Option<Edition>) -> Edition {
    module
        .edition
        .as_deref()
        .and_then(|s| Edition::parse(s).ok())
        .or(file_default)
        .unwrap_or_else(default_edition)
}

// ─── Feature gates ───────────────────────────────────────────────────────────

/// A language/module-system feature that is tied to a minimum edition.
///
/// Every feature below exists since 2026; the table is the place new
/// editions record what *they* introduce (and what older editions lack).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EditionFeature {
    /// File-level `@: safety|arc|arena|pointers|default` directive.
    FileMemMode,
    /// `use "std -> …"` / `use "core -> …"` standard-library imports.
    StdImport,
    /// `use "bit -> …"` (and `dynamic use`) package-manager imports.
    BitImport,
    /// `use "hlib -> …"` `.hlib` archive imports.
    HlibImport,
    /// `use "workspace -> …"` workspace-member imports.
    WorkspaceImport,
}

impl EditionFeature {
    /// First edition that includes the feature.
    pub fn since(self) -> Edition {
        match self {
            EditionFeature::FileMemMode
            | EditionFeature::StdImport
            | EditionFeature::BitImport
            | EditionFeature::HlibImport
            | EditionFeature::WorkspaceImport => Edition::E2026,
        }
    }

    /// Human name for diagnostics.
    pub fn name(self) -> &'static str {
        match self {
            EditionFeature::FileMemMode => "file-level `@: mode` directive",
            EditionFeature::StdImport => "`use \"std -> …\"` imports",
            EditionFeature::BitImport => "`use \"bit -> …\"` imports",
            EditionFeature::HlibImport => "`use \"hlib -> …\"` imports",
            EditionFeature::WorkspaceImport => "`use \"workspace -> …\"` imports",
        }
    }
}

/// A feature used by a module that its declared edition does not include.
#[derive(Debug, Clone, PartialEq)]
pub struct FeatureViolation {
    pub feature: EditionFeature,
    pub edition: Edition,
    pub span: Span,
}

impl FeatureViolation {
    pub fn message(&self) -> String {
        format!(
            "{} requires edition \"{}\" or newer, but this file uses \"{}\"",
            self.feature.name(),
            self.feature.since(),
            self.edition
        )
    }
}

/// Features `module` uses that `edition` does not include.
pub fn check_features(module: &Module, edition: Edition) -> Vec<FeatureViolation> {
    let mut out = Vec::new();
    let mut need = |feature: EditionFeature, span: &Span| {
        if !edition.supports(feature) {
            out.push(FeatureViolation { feature, edition, span: span.clone() });
        }
    };
    let decl_span = module.edition_span.clone().unwrap_or_else(Span::dummy);
    if module.file_mem_mode.is_some() {
        need(EditionFeature::FileMemMode, &decl_span);
    }
    for (kind, _alias, span) in &module.imports {
        match kind {
            ImportKind::Std { .. } | ImportKind::Core { .. } => need(EditionFeature::StdImport, span),
            ImportKind::BitRepo { .. } => need(EditionFeature::BitImport, span),
            ImportKind::Hlib { .. } => need(EditionFeature::HlibImport, span),
            ImportKind::Workspace { .. } => need(EditionFeature::WorkspaceImport, span),
            _ => {}
        }
    }
    out
}

/// Is `message` one of the diagnostics produced by edition handling (unknown/
/// malformed `using`, misplaced or duplicate `using`, feature newer than the
/// declared edition)? The module resolver uses this to make such errors in an
/// imported `mod` file **fatal**, whereas other parse errors in a `mod` file
/// keep their long-standing warn-and-continue behaviour.
pub fn is_edition_diagnostic(message: &str) -> bool {
    message.contains("edition \"")
        || message.contains("`using`")
        || message.contains("invalid edition")
        || message.contains("requires edition")
}

// ─── Per-file lowering hook ──────────────────────────────────────────────────

/// Rewrite `module` — written against `from` — into the canonical AST of
/// this toolchain. Called once per parsed file, right after parsing, so a
/// project can freely mix files of different editions: by the time modules
/// are merged, they all speak the same AST.
///
/// Identity today (only [`Edition::E2026`] exists). New editions add a
/// `match from { … }` arm here.
pub fn lower_module(_module: &mut Module, from: Edition) {
    match from {
        Edition::E2026 => {}
    }
}

// ─── Mixed-edition policy ────────────────────────────────────────────────────

/// How an imported file's edition relates to the importer's.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Relation {
    Same,
    /// The dependency is written against an *older* edition.
    DependencyOlder,
    /// The dependency is written against a *newer* edition.
    DependencyNewer,
}

/// Compare an importer's edition to a dependency's. All combinations are
/// **allowed** — this only classifies them (for notes/reports), because each
/// file is lowered under its own edition (see [`lower_module`]).
pub fn relate(importer: Edition, dependency: Edition) -> Relation {
    use std::cmp::Ordering::*;
    match dependency.cmp(&importer) {
        Equal => Relation::Same,
        Less => Relation::DependencyOlder,
        Greater => Relation::DependencyNewer,
    }
}

// ─── Parse ledger (what editions took part in this build) ────────────────────

/// One parsed file and the edition it was compiled under.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EditionRecord {
    pub file: String,
    pub edition: Edition,
    /// `true` if the file said `using "…"` itself, `false` if it fell back
    /// to the default edition.
    pub declared: bool,
}

static RECORDING: Mutex<Option<Vec<EditionRecord>>> = Mutex::new(None);

/// Start recording every file passed through [`crate::parse`] (CLI builds
/// turn this on; long-lived processes like the LSP leave it off so nothing
/// accumulates).
pub fn start_recording() {
    if let Ok(mut g) = RECORDING.lock() {
        *g = Some(Vec::new());
    }
}

/// Stop recording and return everything seen since [`start_recording`],
/// de-duplicated by file path, in first-seen order.
pub fn take_records() -> Vec<EditionRecord> {
    let Ok(mut g) = RECORDING.lock() else { return Vec::new() };
    let mut seen = std::collections::HashSet::new();
    g.take()
        .unwrap_or_default()
        .into_iter()
        .filter(|r| seen.insert(r.file.clone()))
        .collect()
}

pub(crate) fn record(file: &str, edition: Edition, declared: bool) {
    if let Ok(mut g) = RECORDING.lock() {
        if let Some(v) = g.as_mut() {
            v.push(EditionRecord { file: file.to_string(), edition, declared });
        }
    }
}

/// One-paragraph summary of an edition mix, or `None` when every file used
/// the same edition (nothing worth saying).
pub fn describe_mix(records: &[EditionRecord]) -> Option<String> {
    let mut editions: Vec<Edition> = records.iter().map(|r| r.edition).collect();
    editions.sort();
    editions.dedup();
    if editions.len() < 2 {
        return None;
    }
    let mut s = String::from("note: this build mixes H# editions (each file is compiled under its own):\n");
    for e in &editions {
        let n = records.iter().filter(|r| r.edition == *e).count();
        s.push_str(&format!("  edition {}: {} file(s)\n", e, n));
    }
    Some(s)
}

// ─── Tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;

    #[test]
    fn parses_known_edition() {
        assert_eq!(Edition::parse("2026"), Ok(Edition::E2026));
        assert_eq!(Edition::parse(" 2026 "), Ok(Edition::E2026));
        assert_eq!(Edition::E2026.as_str(), "2026");
        assert_eq!(Edition::E2026.year(), 2026);
    }

    #[test]
    fn classifies_bad_editions() {
        assert!(matches!(Edition::parse("2099"), Err(EditionError::TooNew { year: 2099 })));
        assert!(matches!(Edition::parse("2015"), Err(EditionError::Retired { year: 2015 })));
        assert!(matches!(Edition::parse("26"), Err(EditionError::Malformed(_))));
        assert!(matches!(Edition::parse("latest"), Err(EditionError::Malformed(_))));
        assert!(matches!(Edition::parse(""), Err(EditionError::Malformed(_))));
    }

    #[test]
    fn error_messages_are_actionable() {
        let e = Edition::parse("2099").unwrap_err();
        assert!(e.message().contains("newer"));
        assert!(e.hints().iter().any(|h| h.contains("supported editions: 2026")));
        let e = Edition::parse("abc").unwrap_err();
        assert!(e.message().contains("four-digit"));
    }

    #[test]
    fn registry_is_consistent() {
        assert_eq!(Edition::ALL.first().copied(), Some(Edition::OLDEST));
        assert_eq!(Edition::ALL.last().copied(), Some(Edition::LATEST));
        for e in Edition::ALL {
            assert_eq!(Edition::parse(e.as_str()), Ok(*e));
            assert_eq!(e.status(), EditionStatus::Stable);
        }
        // sorted, no duplicates
        let mut v = Edition::ALL.to_vec();
        v.sort();
        v.dedup();
        assert_eq!(v, Edition::ALL.to_vec());
    }

    #[test]
    fn relate_is_symmetric_classification() {
        assert_eq!(relate(Edition::E2026, Edition::E2026), Relation::Same);
    }

    #[test]
    fn declared_edition_is_recorded_on_module() {
        let r = parse("using \"2026\"\nfn main() is\n    write(\"hi\")\nend\n", "t.h#");
        assert!(!r.has_errors(), "{}", r.render_errors());
        assert_eq!(r.module.edition.as_deref(), Some("2026"));
        assert!(r.module.edition_span.is_some());
        assert_eq!(effective_edition(&r.module), Edition::E2026);
    }

    #[test]
    fn missing_using_falls_back_to_default() {
        let r = parse("fn main() is\n    write(\"hi\")\nend\n", "t.h#");
        assert!(!r.has_errors(), "{}", r.render_errors());
        assert_eq!(r.module.edition, None);
        assert_eq!(effective_edition(&r.module), default_edition());
    }

    #[test]
    fn unknown_edition_is_a_parse_error() {
        let r = parse("using \"2099\"\nfn main() is\nend\n", "t.h#");
        assert!(r.has_errors());
        let msg = r.render_errors();
        assert!(msg.contains("2099"), "{}", msg);
        assert!(msg.contains("newer"), "{}", msg);
    }

    #[test]
    fn malformed_edition_is_a_parse_error() {
        let r = parse("using \"soon\"\nfn main() is\nend\n", "t.h#");
        assert!(r.has_errors());
        assert!(r.render_errors().contains("four-digit"));
    }

    #[test]
    fn using_without_string_is_a_parse_error() {
        let r = parse("using\nfn main() is\nend\n", "t.h#");
        assert!(r.has_errors());
    }

    #[test]
    fn integer_form_is_accepted() {
        let r = parse("using 2026\nfn main() is\nend\n", "t.h#");
        assert!(!r.has_errors(), "{}", r.render_errors());
        assert_eq!(r.module.edition.as_deref(), Some("2026"));
    }

    #[test]
    fn duplicate_using_is_an_error() {
        let r = parse("using \"2026\"\nusing \"2026\"\nfn main() is\nend\n", "t.h#");
        assert!(r.has_errors());
        assert!(r.render_errors().contains("more than once"));
    }

    #[test]
    fn using_after_items_is_an_error() {
        let r = parse("fn main() is\nend\nusing \"2026\"\n", "t.h#");
        assert!(r.has_errors());
        assert!(r.render_errors().contains("before"));
    }

    #[test]
    fn using_may_follow_file_mem_mode_and_precede_imports() {
        let src = "@: safety\nusing \"2026\"\nuse \"std -> math\"\nfn main() is\nend\n";
        let r = parse(src, "t.h#");
        assert!(!r.has_errors(), "{}", r.render_errors());
        assert_eq!(r.module.edition.as_deref(), Some("2026"));
        assert!(r.module.file_mem_mode.is_some());
        assert_eq!(r.module.imports.len(), 1);
    }

    #[test]
    fn features_are_all_available_in_2026() {
        let src = "@: arc\nusing \"2026\"\nuse \"std -> math\"\nuse \"bit -> mylib\"\nuse \"hlib -> other\"\nfn main() is\nend\n";
        let r = parse(src, "t.h#");
        assert!(!r.has_errors(), "{}", r.render_errors());
        assert!(check_features(&r.module, Edition::E2026).is_empty());
        for f in [
            EditionFeature::FileMemMode,
            EditionFeature::StdImport,
            EditionFeature::BitImport,
            EditionFeature::HlibImport,
            EditionFeature::WorkspaceImport,
        ] {
            assert!(Edition::E2026.supports(f));
            assert_eq!(f.since(), Edition::E2026);
        }
    }

    #[test]
    fn default_override_roundtrip() {
        // Only one edition exists, so just prove the set/reset plumbing is sound.
        set_default_edition(Edition::E2026);
        assert_eq!(default_edition(), Edition::E2026);
        reset_default_edition();
        assert_eq!(default_edition(), Edition::LATEST);
    }

    #[test]
    fn mix_description_only_for_real_mixes() {
        let one = vec![
            EditionRecord { file: "a.h#".into(), edition: Edition::E2026, declared: true },
            EditionRecord { file: "b.h#".into(), edition: Edition::E2026, declared: false },
        ];
        assert!(describe_mix(&one).is_none());
        assert!(describe_mix(&[]).is_none());
    }

    #[test]
    fn per_file_default_applies_only_to_undeclared_files() {
        let declared = parse("using \"2026\"\nfn a() is\nend\n", "d.h#");
        let bare = crate::parse_with_default("fn a() is\nend\n", "b.h#", Some(Edition::E2026));
        assert!(!bare.has_errors(), "{}", bare.render_errors());
        assert_eq!(effective_edition_with(&declared.module, Some(Edition::E2026)), Edition::E2026);
        assert_eq!(effective_edition_with(&bare.module, Some(Edition::E2026)), Edition::E2026);
        assert_eq!(STD_EDITION, Edition::E2026);
    }

    #[test]
    fn edition_diagnostics_are_recognised() {
        for src in ["using \"2099\"\n", "using \"x\"\n", "using\n", "fn a() is\nend\nusing \"2026\"\n"] {
            let r = parse(src, "t.h#");
            assert!(r.has_errors(), "{src}");
            assert!(r.errors.iter().any(|e| is_edition_diagnostic(&e.message)), "{src}: {}", r.render_errors());
        }
        assert!(!is_edition_diagnostic("unexpected token `end`"));
    }

    #[test]
    fn lowering_is_identity_for_2026() {
        let r = parse("using \"2026\"\nfn main() is\n    write(\"x\")\nend\n", "t.h#");
        let mut m = r.module.clone();
        lower_module(&mut m, Edition::E2026);
        assert_eq!(m.items, r.module.items);
    }

    #[test]
    fn ledger_records_each_parsed_file_with_its_edition() {
        start_recording();
        let _ = parse("using \"2026\"\nfn a() is\nend\n", "ledger_a.h#");
        let _ = parse("fn b() is\nend\n", "ledger_b.h#");
        let _ = parse("fn b() is\nend\n", "ledger_b.h#"); // same file twice -> once
        let recs = take_records();
        let a = recs.iter().find(|r| r.file == "ledger_a.h#").expect("a recorded");
        let b = recs.iter().find(|r| r.file == "ledger_b.h#").expect("b recorded");
        assert!(a.declared && a.edition == Edition::E2026);
        assert!(!b.declared);
        assert_eq!(recs.iter().filter(|r| r.file == "ledger_b.h#").count(), 1);
        // recording is off again after take_records()
        let _ = parse("fn c() is\nend\n", "ledger_c.h#");
        assert!(take_records().is_empty());
    }
}
