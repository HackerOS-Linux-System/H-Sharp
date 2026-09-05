use serde::Serialize;

#[derive(Serialize)]
pub(crate) struct Diagnostic {
    pub(crate) message: String,
}

#[derive(Serialize)]
pub(crate) struct RunResult {
    /// Whether the program parsed *and* ran to completion without a
    /// top-level runtime error or panic. `false` doesn't necessarily mean
    /// nothing printed — a program can `write(...)` several lines and
    /// *then* hit an error; `stdout` still has everything printed before
    /// that point, exactly like a real terminal session would.
    pub(crate) ok: bool,
    /// Everything the program printed via `write`/`print`/`println`, in
    /// order, concatenated. Empty string if nothing was printed (or if
    /// parsing failed before any code could run).
    pub(crate) stdout: String,
    /// Parse errors, if any — each already rendered as a human-readable,
    /// source-quoting message (via `hsharp_parser`'s own error renderer),
    /// so the playground UI can just display these as-is.
    pub(crate) parse_errors: Vec<Diagnostic>,
    /// Type errors, if any — populated (and `ok` forced `false`, execution
    /// skipped entirely) whenever parsing succeeded but `hsharp-typecheck`
    /// found at least one `Severity::Error` diagnostic. Warnings (e.g. an
    /// unused variable) are reported here too but don't block execution —
    /// only errors do, matching `hsharp compile`'s own behavior.
    pub(crate) type_errors: Vec<Diagnostic>,
    /// The runtime error or panic message, if execution started but
    /// didn't finish cleanly. `None` when `ok` is `true`, or when parsing
    /// failed before execution could start (see `parse_errors` instead).
    pub(crate) runtime_error: Option<String>,
}
