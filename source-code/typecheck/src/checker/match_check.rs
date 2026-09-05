use hsharp_parser::ast::*;
use hsharp_parser::span::Span;
use super::TypeChecker;
use crate::htype::HType;
use crate::helpers::{collect_bool_pattern, collect_enum_pattern_variants};

impl TypeChecker {

    /// §3: match exhaustiveness.
    ///
    /// - For `bool` subjects: arms must cover both `true` and `false`
    ///   (literally, or via a catch-all `Pattern::Wildcard`/`Pattern::Ident`).
    /// - For enum subjects (subject type is `HType::Named(enum_name)` where
    ///   `enum_name` is a known enum): arms must cover every
    ///   `EnumVariant::name`, again allowing a catch-all to satisfy any
    ///   remaining variants.
    /// - For any other subject type (int, string, struct, Any, ...): no
    ///   exhaustiveness check is performed — H# doesn't (yet) have a closed
    ///   set of values for these, so a catch-all is effectively mandatory
    ///   but we don't enforce it (would be a separate, noisier lint).
    ///
    /// A missing arm currently means "falls through and does nothing" at
    /// runtime — exactly the kind of silent bug exhaustiveness checking
    /// exists to catch.
    pub(super) fn check_match_exhaustive(&mut self, subject_ty: &HType, arms: &[MatchArm], match_span: &Span) {
        let has_catchall = arms.iter().any(|arm| {
            arm.guard.is_none() && matches!(arm.pattern, Pattern::Wildcard(_) | Pattern::Ident(_, _))
        });
        if has_catchall { return; }

        match subject_ty {
            HType::Bool => {
                let mut has_true  = false;
                let mut has_false = false;
                for arm in arms {
                    if arm.guard.is_some() { continue; } // guarded arms don't count toward exhaustiveness
                    collect_bool_pattern(&arm.pattern, &mut has_true, &mut has_false);
                }
                if !(has_true && has_false) {
                    let mut missing = Vec::new();
                    if !has_true  { missing.push("true"); }
                    if !has_false { missing.push("false"); }
                    self.err_hint(
                        match_span.clone(),
                                  format!("match on `bool` is not exhaustive: missing {}", missing.join(" and ")),
                                      "add the missing arm(s), or a `_ => ...` catch-all".to_string(),
                    );
                }
            }
            HType::Named(enum_name) => {
                let Some(variants) = self.enums.get(enum_name).cloned() else { return };
                let mut covered: std::collections::HashSet<String> = Default::default();
                for arm in arms {
                    if arm.guard.is_some() { continue; }
                    collect_enum_pattern_variants(&arm.pattern, &mut covered);
                }
                let missing: Vec<&str> = variants.iter()
                .filter(|v| !covered.contains(*v))
                .map(|v| v.as_str())
                .collect();
                if !missing.is_empty() {
                    self.err_hint(
                        match_span.clone(),
                                  format!("match on `{}` is not exhaustive: missing variant(s) {}", enum_name, missing.join(", ")),
                                      "add the missing arm(s), or a `_ => ...` catch-all".to_string(),
                    );
                }
            }
            // int/string/struct/Any/etc: not (yet) exhaustiveness-checked.
            _ => {}
        }
    }
}
