mod diagnostics;
mod htype;
mod checker;
mod helpers;
mod bytes_resolve;

pub use diagnostics::{Severity, Diagnostic, TypeError, print_diagnostics};
pub use htype::HType;
pub use checker::TypeChecker;
