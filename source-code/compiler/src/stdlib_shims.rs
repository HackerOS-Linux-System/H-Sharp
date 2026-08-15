use hsharp_parser::ast::*;
use hsharp_parser::span::Span;

const PROC_RESULT: &str = "ProcResult";
const RUN_CMD: &str = "proc_run_cmd";
const RUN_CMD_LIVE: &str = "proc_run_cmd_live";
const STR_SPLIT: &str = "str_split";
const STR_COUNT: &str = "str_count";
const ITER_JOIN: &str = "iter_join";
const JSON_EMPTY_OBJECT: &str = "json_empty_object";
const JSON_PARSE: &str = "json_parse";
const JSON_STRINGIFY_PRETTY: &str = "json_stringify_pretty";
const JSON_TYPE_ALIAS: &str = "json";

pub fn inject_stdlib_shims(module: &mut Module) {
    let has_struct = module.items.iter().any(|i| matches!(i, Item::StructDef(s) if s.name == PROC_RESULT));
    let has_fn     = module.items.iter().any(|i| matches!(i, Item::FnDef(f) if f.name == RUN_CMD || f.name == RUN_CMD_LIVE));
    // Don't inject over a name the user (or a future real std/proc.h#)
    // already defines — same "only if missing" guard `const_lowering`
    // doesn't need (it always rewrites) but this does, since unlike a
    // `const`, there's a real chance of a legitimate user struct/fn
    // already using these names.
    if !has_struct && !has_fn {
        module.items.push(proc_result_struct());
        module.items.push(run_cmd_fn(RUN_CMD));
        module.items.push(run_cmd_fn(RUN_CMD_LIVE));
    }

    let has_split = module.items.iter().any(|i| matches!(i, Item::FnDef(f) if f.name == STR_SPLIT));
    if !has_split {
        module.items.push(str_split_fn());
    }

    inject_fn_if_missing(module, STR_COUNT, str_count_fn);
    inject_fn_if_missing(module, ITER_JOIN, iter_join_fn);
    inject_fn_if_missing(module, JSON_EMPTY_OBJECT, json_empty_object_fn);
    inject_fn_if_missing(module, JSON_PARSE, json_parse_fn);
    inject_fn_if_missing(module, JSON_STRINGIFY_PRETTY, json_stringify_pretty_fn);

    // `json` as a type: getit writes `fn load_cache() -> json is ... end`.
    // There's no real parsed-JSON-value type anywhere in this runtime
    // (see hsh_json_get's "not a full JSON parser" doc comment in
    // core.c) — every json:: function here operates on plain flat JSON
    // *text*, so `json` is simply an alias for `string`. This makes
    // `-> json` type-check as exactly what it already behaviorally is,
    // rather than an unresolved named type that typecheck's lenient
    // fallback (see typecheck/src/lib.rs) would otherwise silently wave
    // through with no real checking at all.
    let has_json_type = module.items.iter().any(|i| matches!(i, Item::TypeAlias { name, .. } if name == JSON_TYPE_ALIAS));
    if !has_json_type {
        module.items.push(Item::TypeAlias {
            name: JSON_TYPE_ALIAS.to_string(),
            ty: TypeExpr::String,
            pub_: true,
            span: Span::dummy(),
        });
    }
}

fn inject_fn_if_missing(module: &mut Module, name: &str, build: fn() -> Item) {
    let exists = module.items.iter().any(|i| matches!(i, Item::FnDef(f) if f.name == name));
    if !exists {
        module.items.push(build());
    }
}

fn proc_result_struct() -> Item {
    let span = Span::dummy();
    Item::StructDef(StructDef {
        attrs: vec![],
        type_params: vec![],
        name: PROC_RESULT.to_string(),
        fields: vec![
            StructField { name: "stdout".into(),    ty: TypeExpr::String, pub_: true, span: span.clone() },
            StructField { name: "stderr".into(),    ty: TypeExpr::String, pub_: true, span: span.clone() },
            StructField { name: "exit_code".into(), ty: TypeExpr::I64,    pub_: true, span: span.clone() },
        ],
        pub_: true,
        span,
    })
}

/// Builds:
/// ```h#
/// pub fn proc_run_cmd(cmd: string, timeout_secs: int) -> ProcResult is
///     let __code = run_cmd_exec(cmd, timeout_secs)
///     return ProcResult { stdout: run_cmd_last_stdout(), stderr: run_cmd_last_stderr(), exit_code: __code }
/// end
/// ```
/// (`proc_run_cmd_live` is byte-for-byte the same body — see the module
/// doc comment on `runtime/core.c`'s `hsh_run_cmd_exec` for why "_live"
/// doesn't yet stream output differently.)
fn run_cmd_fn(name: &str) -> Item {
    let span = Span::dummy();
    let call = |fn_name: &str, args: Vec<Expr>| -> Expr {
        Expr::Call(Box::new(Expr::Ident(fn_name.to_string(), span.clone())), args, span.clone())
    };
    let ident = |n: &str| Expr::Ident(n.to_string(), span.clone());

    let exec_call = call("run_cmd_exec", vec![ident("cmd"), ident("timeout_secs")]);
    let let_code = Stmt::Let {
        name: "__code".to_string(),
        ty: Some(TypeExpr::I64),
        mutable: false,
        value: Some(exec_call),
        span: span.clone(),
    };
    let struct_lit = Expr::StructLit(
        PROC_RESULT.to_string(),
        vec![
            ("stdout".to_string(),    call("run_cmd_last_stdout", vec![])),
            ("stderr".to_string(),    call("run_cmd_last_stderr", vec![])),
            ("exit_code".to_string(), ident("__code")),
        ],
        span.clone(),
    );
    let ret = Stmt::Return(Some(struct_lit), span.clone());

    Item::FnDef(FnDef {
        attrs: vec![],
        type_params: vec![],
        name: name.to_string(),
        params: vec![
            Param { name: "cmd".into(), ty: TypeExpr::String, mutable: false, span: span.clone() },
            Param { name: "timeout_secs".into(), ty: TypeExpr::I64, mutable: false, span: span.clone() },
        ],
        return_type: Some(TypeExpr::Named(PROC_RESULT.to_string())),
        body: vec![let_code, ret],
        pub_: true,
        is_unsafe: false,
        is_async: false,
        mem_mode: MemoryMode::default(),
        span,
    })
}

/// Builds:
/// ```h#
/// pub fn str_split(s: string, sep: string) -> [string] is
///     let __n = str_split_count(s, sep)
///     let __result = []
///     let __i = 0
///     while __i < __n is
///         __result.push(str_split_part(s, sep, __i))
///         __i = __i + 1
///     end
///     return __result
/// end
/// ```
/// Deliberately built entirely from ordinary array operations
/// (`[]` literal, `.push()`, `while`) — the exact same codegen path
/// every other array-building H# program already goes through — rather
/// than a new C runtime function that hands back a raw `HshArray*`,
/// which would mean matching that struct's boxing/tagging layout by
/// hand without LLVM available here to verify it. See
/// `runtime/core.c`'s doc comment on `hsh_str_split_count` for the two
/// small scalar-return C functions this loop calls.
fn str_split_fn() -> Item {
    let span = Span::dummy();
    let call = |fn_name: &str, args: Vec<Expr>| -> Expr {
        Expr::Call(Box::new(Expr::Ident(fn_name.to_string(), span.clone())), args, span.clone())
    };
    let ident = |n: &str| Expr::Ident(n.to_string(), span.clone());
    let int_lit = |v: i64| Expr::Literal(Literal::Int(v), span.clone());

    let let_n = Stmt::Let {
        name: "__n".to_string(), ty: Some(TypeExpr::I64), mutable: false,
        value: Some(call("str_split_count", vec![ident("s"), ident("sep")])),
        span: span.clone(),
    };
    let let_result = Stmt::Let {
        name: "__result".to_string(), ty: Some(TypeExpr::Array(Box::new(TypeExpr::String))), mutable: true,
        value: Some(Expr::ArrayLit(vec![], span.clone())),
        span: span.clone(),
    };
    let let_i = Stmt::Let {
        name: "__i".to_string(), ty: Some(TypeExpr::I64), mutable: true,
        value: Some(int_lit(0)),
        span: span.clone(),
    };
    let push_call = Expr::MethodCall(
        Box::new(ident("__result")),
        "push".to_string(),
        vec![call("str_split_part", vec![ident("s"), ident("sep"), ident("__i")])],
        span.clone(),
    );
    let incr = Expr::Assign(
        Box::new(ident("__i")),
        Box::new(Expr::BinOp(Box::new(ident("__i")), BinOp::Add, Box::new(int_lit(1)), span.clone())),
        span.clone(),
    );
    let while_loop = Stmt::Expr(
        Expr::While {
            condition: Box::new(Expr::BinOp(Box::new(ident("__i")), BinOp::Lt, Box::new(ident("__n")), span.clone())),
            body: vec![Stmt::Expr(push_call, span.clone()), Stmt::Expr(incr, span.clone())],
            span: span.clone(),
        },
        span.clone(),
    );
    let ret = Stmt::Return(Some(ident("__result")), span.clone());

    Item::FnDef(FnDef {
        attrs: vec![],
        type_params: vec![],
        name: STR_SPLIT.to_string(),
        params: vec![
            Param { name: "s".into(), ty: TypeExpr::String, mutable: false, span: span.clone() },
            Param { name: "sep".into(), ty: TypeExpr::String, mutable: false, span: span.clone() },
        ],
        return_type: Some(TypeExpr::Array(Box::new(TypeExpr::String))),
        body: vec![let_n, let_result, let_i, while_loop, ret],
        pub_: true,
        is_unsafe: false,
        is_async: false,
        mem_mode: MemoryMode::default(),
        span,
    })
}

/// `str::count(s, sub)` — number of (non-overlapping) occurrences of
/// `sub` in `s`. Reuses `str_split_count` rather than new C: splitting
/// "a/b/c" on "/" gives 3 parts, i.e. 2 occurrences — occurrences is
/// always `parts - 1`. Zero new runtime surface.
fn str_count_fn() -> Item {
    let span = Span::dummy();
    let call = |fn_name: &str, args: Vec<Expr>| -> Expr {
        Expr::Call(Box::new(Expr::Ident(fn_name.to_string(), span.clone())), args, span.clone())
    };
    let ident = |n: &str| Expr::Ident(n.to_string(), span.clone());
    let int_lit = |v: i64| Expr::Literal(Literal::Int(v), span.clone());

    let body_expr = Expr::BinOp(
        Box::new(call("str_split_count", vec![ident("s"), ident("sub")])),
        BinOp::Sub,
        Box::new(int_lit(1)),
        span.clone(),
    );
    Item::FnDef(FnDef {
        attrs: vec![], type_params: vec![], name: STR_COUNT.to_string(),
        params: vec![
            Param { name: "s".into(), ty: TypeExpr::String, mutable: false, span: span.clone() },
            Param { name: "sub".into(), ty: TypeExpr::String, mutable: false, span: span.clone() },
        ],
        return_type: Some(TypeExpr::I64),
        body: vec![Stmt::Return(Some(body_expr), span.clone())],
        pub_: true, is_unsafe: false, is_async: false, mem_mode: MemoryMode::default(), span,
    })
}

/// `iter::join(arr, sep)` — built entirely from ordinary, already-working
/// array/string operations (`.len()`, indexing, `+` concatenation),
/// exactly like `str_split` above avoids new array-construction C code.
fn iter_join_fn() -> Item {
    let span = Span::dummy();
    let ident = |n: &str| Expr::Ident(n.to_string(), span.clone());
    let int_lit = |v: i64| Expr::Literal(Literal::Int(v), span.clone());
    let str_lit = |s: &str| Expr::Literal(Literal::String(s.to_string()), span.clone());
    let concat = |a: Expr, b: Expr| Expr::BinOp(Box::new(a), BinOp::Add, Box::new(b), span.clone());

    let let_n = Stmt::Let {
        name: "__n".into(), ty: Some(TypeExpr::I64), mutable: false,
        value: Some(Expr::MethodCall(Box::new(ident("arr")), "len".to_string(), vec![], span.clone())),
        span: span.clone(),
    };
    let let_result = Stmt::Let {
        name: "__result".into(), ty: Some(TypeExpr::String), mutable: true,
        value: Some(str_lit("")), span: span.clone(),
    };
    let let_i = Stmt::Let {
        name: "__i".into(), ty: Some(TypeExpr::I64), mutable: true,
        value: Some(int_lit(0)), span: span.clone(),
    };
    let append_sep = Stmt::Expr(
        Expr::If {
            condition: Box::new(Expr::BinOp(Box::new(ident("__i")), BinOp::Gt, Box::new(int_lit(0)), span.clone())),
            then_body: vec![Stmt::Expr(Expr::Assign(
                Box::new(ident("__result")),
                Box::new(concat(ident("__result"), ident("sep"))),
                span.clone(),
            ), span.clone())],
            elsif_branches: vec![],
            else_body: None,
            span: span.clone(),
        },
        span.clone(),
    );
    let append_item = Stmt::Expr(Expr::Assign(
        Box::new(ident("__result")),
        Box::new(concat(ident("__result"), Expr::IndexAccess(Box::new(ident("arr")), Box::new(ident("__i")), span.clone()))),
        span.clone(),
    ), span.clone());
    let incr = Stmt::Expr(Expr::Assign(
        Box::new(ident("__i")),
        Box::new(Expr::BinOp(Box::new(ident("__i")), BinOp::Add, Box::new(int_lit(1)), span.clone())),
        span.clone(),
    ), span.clone());
    let while_loop = Stmt::Expr(Expr::While {
        condition: Box::new(Expr::BinOp(Box::new(ident("__i")), BinOp::Lt, Box::new(ident("__n")), span.clone())),
        body: vec![append_sep, append_item, incr],
        span: span.clone(),
    }, span.clone());
    let ret = Stmt::Return(Some(ident("__result")), span.clone());

    Item::FnDef(FnDef {
        attrs: vec![], type_params: vec![], name: ITER_JOIN.to_string(),
        params: vec![
            Param { name: "arr".into(), ty: TypeExpr::Array(Box::new(TypeExpr::String)), mutable: false, span: span.clone() },
            Param { name: "sep".into(), ty: TypeExpr::String, mutable: false, span: span.clone() },
        ],
        return_type: Some(TypeExpr::String),
        body: vec![let_n, let_result, let_i, while_loop, ret],
        pub_: true, is_unsafe: false, is_async: false, mem_mode: MemoryMode::default(), span,
    })
}

/// `json::empty_object()` / `json::parse(s)` / `json::stringify_pretty(s)`
/// — see the `json` type-alias doc comment in `inject_stdlib_shims`
/// above for why these treat "a JSON value" as plain flat-object text
/// rather than a real parsed structure. `parse` is therefore an
/// identity function (nothing to parse into), `empty_object` is the
/// literal `"{}"`, and `stringify_pretty` reformats via the
/// already-existing `replace()` builtin — three string substitutions,
/// zero new runtime code.
fn json_empty_object_fn() -> Item {
    let span = Span::dummy();
    Item::FnDef(FnDef {
        attrs: vec![], type_params: vec![], name: JSON_EMPTY_OBJECT.to_string(),
        params: vec![],
        return_type: Some(TypeExpr::String),
        body: vec![Stmt::Return(Some(Expr::Literal(Literal::String("{}".to_string()), span.clone())), span.clone())],
        pub_: true, is_unsafe: false, is_async: false, mem_mode: MemoryMode::default(), span,
    })
}

fn json_parse_fn() -> Item {
    let span = Span::dummy();
    Item::FnDef(FnDef {
        attrs: vec![], type_params: vec![], name: JSON_PARSE.to_string(),
        params: vec![Param { name: "s".into(), ty: TypeExpr::String, mutable: false, span: span.clone() }],
        return_type: Some(TypeExpr::String),
        body: vec![Stmt::Return(Some(Expr::Ident("s".to_string(), span.clone())), span.clone())],
        pub_: true, is_unsafe: false, is_async: false, mem_mode: MemoryMode::default(), span,
    })
}

fn json_stringify_pretty_fn() -> Item {
    let span = Span::dummy();
    let call = |fn_name: &str, args: Vec<Expr>| -> Expr {
        Expr::Call(Box::new(Expr::Ident(fn_name.to_string(), span.clone())), args, span.clone())
    };
    let ident = |n: &str| Expr::Ident(n.to_string(), span.clone());
    let str_lit = |s: &str| Expr::Literal(Literal::String(s.to_string()), span.clone());
    let replace = |target: Expr, from: &str, to: &str| call("replace", vec![target, str_lit(from), str_lit(to)]);

    let let_1 = Stmt::Let { name: "__s1".into(), ty: Some(TypeExpr::String), mutable: false,
        value: Some(replace(ident("s"), "{", "{\n  ")), span: span.clone() };
    let let_2 = Stmt::Let { name: "__s2".into(), ty: Some(TypeExpr::String), mutable: false,
        value: Some(replace(ident("__s1"), ",", ",\n  ")), span: span.clone() };
    let let_3 = Stmt::Let { name: "__s3".into(), ty: Some(TypeExpr::String), mutable: false,
        value: Some(replace(ident("__s2"), "}", "\n}")), span: span.clone() };
    let ret = Stmt::Return(Some(ident("__s3")), span.clone());

    Item::FnDef(FnDef {
        attrs: vec![], type_params: vec![], name: JSON_STRINGIFY_PRETTY.to_string(),
        params: vec![Param { name: "s".into(), ty: TypeExpr::String, mutable: false, span: span.clone() }],
        return_type: Some(TypeExpr::String),
        body: vec![let_1, let_2, let_3, ret],
        pub_: true, is_unsafe: false, is_async: false, mem_mode: MemoryMode::default(), span,
    })
}
