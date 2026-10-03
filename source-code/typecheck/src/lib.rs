mod diagnostics;
mod htype;
mod checker;
mod helpers;
mod bit_resolve;

pub use diagnostics::{Severity, Diagnostic, TypeError, print_diagnostics};
pub use htype::HType;
pub use checker::TypeChecker;

// Regression: `return self` inside an `impl` method (fluent builders) used to
// fail with "return type mismatch: expected `T`, found `Self`" because `self`
// was typed as the placeholder `Self` instead of the impl's type.
#[cfg(test)]
mod self_in_impl_tests {
    use super::*;

    fn mismatches(src: &str) -> Vec<String> {
        let parsed = hsharp_parser::parse(src, "test.h#");
        assert!(!parsed.has_errors(), "parse errors: {}", parsed.render_errors());
        let mut tc = TypeChecker::new();
        tc.check_module(&parsed.module)
            .into_iter()
            .filter(|d| d.message.contains("return type mismatch"))
            .map(|d| d.message)
            .collect()
    }

    #[test]
    fn builder_returning_self_typechecks() {
        let src = "struct D is\n    pub code: string\nend\n\nimpl D is\n    fn with_code(self, c: string) -> D is\n        self.code = c\n        return self\n    end\nend\n";
        assert!(mismatches(src).is_empty());
    }

    #[test]
    fn returning_wrong_struct_is_still_an_error() {
        let src = "struct A is\n    pub n: int\nend\nstruct B is\n    pub n: int\nend\n\nimpl A is\n    fn bad(self) -> B is\n        return self\n    end\nend\n";
        assert_eq!(mismatches(src).len(), 1);
    }
}
