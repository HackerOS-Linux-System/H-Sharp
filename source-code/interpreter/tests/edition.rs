use hsharp_interpreter::{Interpreter, Value};
use hsharp_parser::edition::{self, Edition};

fn run_fn(src: &str, name: &str) -> Value {
    let parsed = hsharp_parser::parse(src, "edition_test.h#");
    assert!(!parsed.has_errors(), "{}", parsed.render_errors());
    let mut interp = Interpreter::new();
    interp.run_module_register_only(&parsed.module).expect("register");
    interp.call_test_fn(name).expect("call")
}

#[test]
fn declared_2026_program_runs() {
    let v = run_fn("using \"2026\"\nfn answer() -> int is\n    return 41 + 1\nend\n", "answer");
    assert!(matches!(v, Value::Int(42)), "{:?}", v);
}

#[test]
fn undeclared_program_runs_under_default_edition() {
    let v = run_fn("fn answer() -> int is\n    return 7\nend\n", "answer");
    assert!(matches!(v, Value::Int(7)), "{:?}", v);
}

#[test]
fn unknown_edition_never_reaches_the_interpreter() {
    let parsed = hsharp_parser::parse("using \"2099\"\nfn main() is\nend\n", "t.h#");
    assert!(parsed.has_errors());
    assert!(parsed.render_errors().contains("newer"));
}

#[test]
fn per_file_default_edition_is_used_for_imported_files() {
    let parsed = hsharp_parser::parse_with_default(
        "fn answer() -> int is\n    return 1\nend\n",
        "lib.h#",
        Some(Edition::E2026),
    );
    assert!(!parsed.has_errors(), "{}", parsed.render_errors());
    assert_eq!(edition::effective_edition_with(&parsed.module, Some(Edition::E2026)), Edition::E2026);
}
