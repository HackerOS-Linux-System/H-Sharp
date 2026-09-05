use hsharp_parser::ast::*;
use hsharp_parser::span::Span;
use crate::htype::HType;


/// §3: is `from as to` a valid cast?
///
/// Allowed:
///   - numeric <-> numeric (any int/float width combination — narrowing
///     casts are allowed, matching C/Rust `as` semantics: the programmer
///     is opting into possible truncation)
///   - numeric <-> bool (0/1 <-> false/true, like C)
///   - anything <-> `any` (the escape hatch / dynamic type)
///   - `T as T` (no-op cast, sometimes used for clarity)
///
/// NOT allowed:
///   - string <-> numeric (must go through `to_int()`/`to_string()`, which
///     can fail/format — not a bit-reinterpretation cast)
///   - struct <-> anything (no `#[repr(C)]` layout guarantees yet — see
///     roadmap §5 on extern/struct layout)
pub(crate) fn cast_allowed(from: &HType, to: &HType) -> bool {
    if from == to { return true; }
    if matches!(from, HType::Any) || matches!(to, HType::Any) { return true; }

    let from_num_or_bool = from.is_numeric() || matches!(from, HType::Bool);
    let to_num_or_bool   = to.is_numeric()   || matches!(to, HType::Bool);
    if from_num_or_bool && to_num_or_bool { return true; }

    // Pointer-ish casts (ref <-> ref) are allowed — `unsafe` blocks rely on
    // re-interpreting pointers; the typechecker doesn't try to prove memory
    // safety inside `unsafe`.
    if matches!(from, HType::Ref(_) | HType::RefMut(_)) && matches!(to, HType::Ref(_) | HType::RefMut(_)) {
        return true;
    }

    false
}

/// Walk a pattern, recording whether it matches `true` and/or `false`
/// (for bool exhaustiveness). `Pattern::Or` recurses into each alternative.
pub(crate) fn collect_bool_pattern(pat: &Pattern, has_true: &mut bool, has_false: &mut bool) {
    match pat {
        Pattern::Literal(Literal::Bool(true), _)  => *has_true  = true,
        Pattern::Literal(Literal::Bool(false), _) => *has_false = true,
        Pattern::Or(pats, _) => for p in pats { collect_bool_pattern(p, has_true, has_false); },
        Pattern::Wildcard(_) | Pattern::Ident(_, _) => { *has_true = true; *has_false = true; }
        _ => {}
    }
}

/// Walk a pattern, recording which enum variant names it covers (for enum
/// exhaustiveness). `Pattern::Enum { variant, .. }` and a bare
/// `Pattern::Ident(name, _)` that happens to match a variant's name both
/// count (the latter covers the common style of writing unit variants as
/// plain identifiers without `Enum { .. }` wrapping).
pub(crate) fn collect_enum_pattern_variants(pat: &Pattern, covered: &mut std::collections::HashSet<String>) {
    match pat {
        Pattern::Enum { variant, .. } => { covered.insert(variant.clone()); }
        Pattern::Ident(name, _)       => { covered.insert(name.clone()); }
        Pattern::Or(pats, _)          => for p in pats { collect_enum_pattern_variants(p, covered); },
        _ => {}
    }
}

/// §3: return-path reachability.
///
/// Returns `true` if every execution path through `stmts` ends in a
/// `Stmt::Return` (directly, or via an `if`/`elsif`/`else` where every
/// branch — including a mandatory `else` — itself always-returns, or a
/// `match` where every arm always-returns).
///
/// A `while`/`for` loop is NOT considered to always-return even if its body
/// does, because the loop might execute zero times (or the typechecker
/// can't easily prove it executes at least once) — matching how Rust treats
/// loops for this analysis (a `loop { ... }` with no `break` is the
/// exception Rust special-cases; H# doesn't have bare infinite `loop` as a
/// distinct construct here, so we keep this simple and conservative).
pub(crate) fn block_always_returns(stmts: &[Stmt]) -> bool {
    let Some(last) = stmts.last() else { return false };
    stmt_always_returns(last)
}

pub(crate) fn stmt_always_returns(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Return(_, _) => true,
        // BUG FIX: a match arm written in the terse single-expression
        // form (`Pattern => return n`, no `is ... end`) parses its body
        // as `Stmt::Expr(Expr::Return(...))`, *not* `Stmt::Return(...)`
        // — `parse_match` treats `return n` there as an ordinary
        // expression (H# allows `return` as an expression, not just a
        // statement) wrapped in a one-element `Stmt::Expr` body, per
        // `parse_match`'s "Single expression arm" branch. Without this
        // arm, a function whose only body is a `match` where every arm
        // uses this terse `=> return ...` form (the natural, idiomatic
        // way to write it) was flagged as "does not return on all
        // paths" even though it provably does.
        Stmt::Expr(Expr::Return(_, _), _) => true,
        Stmt::Expr(Expr::If { then_body, elsif_branches, else_body, .. }, _) => {
            let Some(else_body) = else_body else { return false }; // no else => can fall through
            block_always_returns(then_body)
            && elsif_branches.iter().all(|(_, body)| block_always_returns(body))
            && block_always_returns(else_body)
        }
        Stmt::Expr(Expr::Match { arms, .. }, _) => {
            !arms.is_empty() && arms.iter().all(|arm| block_always_returns(&arm.body))
        }
        // `unsafe is ... end` blocks: reachability follows the inner body.
        Stmt::Expr(Expr::Unsafe(body, _, _), _) => block_always_returns(body),
        _ => false,
    }
}

/// Best-effort span for a statement (used to point reachability errors at
/// "the end of the function" when there's at least one statement to anchor
/// to).
pub(crate) fn stmt_span(stmt: &Stmt) -> Span {
    match stmt {
        Stmt::Let { span, .. } | Stmt::Return(_, span) | Stmt::Break(_, span) |
        Stmt::Continue(span) => span.clone(),
        Stmt::Expr(e, _) => e.span().clone(),
        Stmt::Import(_, _, span) => span.clone(),
        Stmt::Item(item) => item_span(item),
    }
}

pub(crate) fn item_span(item: &Item) -> Span {
    match item {
        Item::FnDef(f)     => f.span.clone(),
        Item::StructDef(s) => s.span.clone(),
        Item::EnumDef(e)   => e.span.clone(),
        Item::TraitDef(t)  => t.span.clone(),
        Item::ImplBlock(i) => i.span.clone(),
        Item::TypeAlias { span, .. } => span.clone(),
        Item::ConstDef { span, .. } => span.clone(),
        Item::Extern(e)    => e.span.clone(),
        Item::ModDecl { span, .. } => span.clone(),
    }
}
