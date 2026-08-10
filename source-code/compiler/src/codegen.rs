use std::collections::HashMap;
use std::path::Path;
use inkwell::{
    AddressSpace,
    OptimizationLevel,
    context::Context,
    builder::Builder,
    module::Module,
    values::{BasicValueEnum, FunctionValue, PointerValue},
    types::{BasicTypeEnum, BasicType},
    targets::{
        CodeModel, FileType, InitializationConfig, RelocMode,
        Target, TargetMachine,
    },
};
use hsharp_parser::ast::{Module as HshModule, *};
use hsharp_parser::span::Span;
use crate::{CompileOptions, OutputKind};
use crate::llvm_types::htype_to_llvm;
use crate::builtins::LlvmBuiltins;
use crate::llvm_optimize::{optimize_module, mark_nounwind};
use crate::ffi_linker;
use crate::regions;

#[derive(Debug, thiserror::Error)]
pub enum CodegenError {
    #[error("LLVM: {0}")]          Llvm(String),
    // Previously these two carried only the bare name — "codegen: undefined
    // var: nazwa" with no file/line/column at all, which is close to
    // useless in a real multi-file project (the actual failing use of
    // `nazwa` might be nowhere near any file the person is currently
    // looking at — e.g. a stray unescaped `{name}` deep inside a string
    // literal three files away, silently parsed as string interpolation
    // referencing an undeclared variable `name`). Every raise site below
    // now threads through the real `Span` of the identifier/call that
    // failed to resolve, the same way the typechecker's `Diagnostic`s
    // already do.
    #[error("undefined var: {name} ({span})")] UndefinedVar { name: String, span: Span },
    #[error("undefined fn: {name} ({span})")]  UndefinedFn { name: String, span: Span },
    #[error("io: {0}")]            Io(#[from] std::io::Error),
    #[error("link: {0}")]          Link(String),
    /// `@safety`'s move-after-use check escalated from a warning to a
    /// real compile error — see `check_moves_basic`'s doc comment for why
    /// `@safety` (and only `@safety`; `@default` still just warns) treats
    /// this as fatal.
    #[error("@safety violation in `{fn_name}`:\n{}", .violations.join("\n"))]
    SafetyViolation { fn_name: String, violations: Vec<String> },
}
type R<T> = Result<T, CodegenError>;

pub struct LlvmCodegen {
    context: Context,
    opts:    CompileOptions,
    /// §5: link flags collected from `extern [c/cpp/rust, "library"]` blocks
    /// in the module being compiled. Populated at the start of
    /// `compile_full` (which takes `&self`, hence `RefCell`).
    link_flags: std::cell::RefCell<ffi_linker::LinkFlags>,
    /// Whether the module uses regex:: (needs runtime/regex.c + -lpcre2-8).
    /// RefCell so compile_full (&self) can set it without unsafe.
    uses_regex: std::cell::Cell<bool>,
    /// Whether the module uses db:: (needs runtime/sqlite.c + -lsqlite3).
    uses_db: std::cell::Cell<bool>,
}

impl LlvmCodegen {
    pub fn new(opts: &CompileOptions) -> R<Self> {
        Target::initialize_x86(&InitializationConfig::default());
        Ok(Self {
            context: Context::create(),
           opts: opts.clone(),
           link_flags: std::cell::RefCell::new(ffi_linker::LinkFlags::default()),
           uses_regex: std::cell::Cell::new(false),
           uses_db:    std::cell::Cell::new(false),
        })
    }

    pub fn declare_functions(&mut self, _m: &HshModule) -> R<()> { Ok(()) }
    pub fn compile_module(&mut self, _m: &HshModule) -> R<()>    { Ok(()) }
    pub fn get_ir(&self)        -> String { String::new() }
    pub fn emit(&self, _output: &str, _optimize: bool) -> R<()> { Ok(()) }
    pub fn emit_object_file(&self, _out: &str) -> R<()>         { Ok(()) }

    /// Scan for `regex::` / `db::` usage in expressions and statements.
    /// Called once at compile_full start so emit_binary_with_machine
    /// can decide which optional runtime modules to compile/link.
    fn scan_module_features(m: &HshModule) -> (bool, bool) {
        let mut has_regex = false;
        let mut has_db    = false;
        for item in &m.items {
            scan_item_features(item, &mut has_regex, &mut has_db);
            if has_regex && has_db { break; }
        }
        (has_regex, has_db)
    }

    /// Full compilation: AST -> LLVM IR -> optimised binary.
    pub fn compile_full(&self, m: &HshModule) -> R<()> {
        let (uses_regex, uses_db) = Self::scan_module_features(m);
        self.uses_regex.set(uses_regex);
        self.uses_db.set(uses_db);

        let (module, machine) = self.build_module(m)?;
        self.emit_binary_with_machine(&module, &machine)
    }

    /// Build + optimize the LLVM IR for `m` without emitting a binary, and
    /// return it as text. Used by `h# --emit-ir`.
    pub fn compile_to_ir(&self, m: &HshModule) -> R<String> {
        let (module, _machine) = self.build_module(m)?;
        Ok(module.print_to_string().to_string())
    }

    /// Shared by `compile_full` and `compile_to_ir`: build the LLVM module
    /// (declare + compile all functions, including extern C/C++/Rust/Python
    /// handling) and run the optimization pipeline. Returns the optimized
    /// module plus the target machine used to optimize it (also needed by
    /// `emit_binary_with_machine` for object-file emission).
    fn build_module(&self, m: &HshModule) -> R<(Module<'_>, TargetMachine)> {
        let ctx     = &self.context;
        let module  = ctx.create_module("hsharp_module");
        let builder = ctx.create_builder();
        let builtins = LlvmBuiltins::declare(ctx, &module);

        let mut func_vals:   HashMap<String, FunctionValue>  = HashMap::new();
        let mut str_globals: HashMap<String, PointerValue>   = HashMap::new();

        // ── §5 FFI: extern blocks (C / C++ / Rust / Python) ───────────────
        //
        // `ffi_linker::collect_link_flags` walks every `Item::Extern` and
        // produces the `-l...`/whole-archive flags needed at link time
        // (see ffi_linker.rs for the C/C++/Rust rules). We mirror that same
        // walk here to also DECLARE each extern function in the LLVM
        // module so calls to it resolve at link time.
        *self.link_flags.borrow_mut() = ffi_linker::collect_link_flags(m);

        for item in &m.items {
            if let Item::Extern(ext) = item {
                match ext.lang {
                    ExternLang::C | ExternLang::Cpp | ExternLang::Rust => {
                        // C/C++/Rust externs: declare with Linkage::External.
                        // The actual symbol comes from libc, -l{library}
                        // (C/C++), or a Rust staticlib linked
                        // whole-archive (see ffi_linker.rs) so #[no_mangle]
                        // symbols aren't garbage-collected by the linker
                        // before our call sites reference them.
                        //
                        // C++ caveat (documented in ffi_linker.rs and the
                        // roadmap): this only resolves correctly if the
                        // C++ library exports these symbols with
                        // `extern "C"` linkage (no Itanium mangling). H#
                        // does not implement a C++ name mangler.
                        for fn_decl in &ext.functions {
                            let sig = self.build_extern_fn_type(ctx, fn_decl);
                            let fv = if let Some(existing) = module.get_function(&fn_decl.name) {
                                existing
                            } else {
                                module.add_function(&fn_decl.name, sig, Some(inkwell::module::Linkage::External))
                            };
                            // Register so `call_fn`'s fallback
                            // (`self.func_vals.get(name)`) resolves calls
                            // to this extern symbol exactly like a
                            // user-defined H# function.
                            func_vals.insert(fn_decl.name.clone(), fv);
                        }
                    }
                    ExternLang::Python => {
                        // Phase 1.5: generate a REAL callable trampoline
                        // function for each declared `fn` in this block.
                        // The trampoline marshals H# args into a Python
                        // expression string, evaluates it via
                        // `hsh_py_eval` (subprocess `python3 -c`, no
                        // shell), and marshals the result back to the
                        // declared H# return type.
                        //
                        // `ext.library` is the Python module name, e.g.
                        // `extern [python, "numpy"] is fn mean(data: string) -> f64 ... end`
                        // generates:
                        //   f64 mean(string data) {
                        //     code = "import numpy\nprint(numpy.mean(" + repr(data) + "))"
                        //     out  = trim(py_eval(code))
                        //     return atof(out)
                        //   }
                        let module_name = ext.library.clone().unwrap_or_else(|| "__main__".to_string());
                        for fn_decl in &ext.functions {
                            let sig = self.build_extern_fn_type(ctx, fn_decl);
                            let fv = module.add_function(&fn_decl.name, sig, None);
                            mark_nounwind(fv);
                            self.compile_python_trampoline(
                                ctx, &module, &builder, &builtins, &module_name, fn_decl, fv,
                            )?;
                            func_vals.insert(fn_decl.name.clone(), fv);
                        }
                    }
                }
            }
        }

        // Collect struct definitions (name -> ordered fields) so struct
        // literal / field-access codegen can resolve field indices.
        let mut structs: HashMap<String, Vec<StructField>> = HashMap::new();
        for item in &m.items {
            if let Item::StructDef(sd) = item {
                structs.insert(sd.name.clone(), sd.fields.clone());
            }
        }

        // Pass 1: declare signatures for H#-defined functions/methods
        let fns = self.collect_fns(m);
        for f in &fns {
            let sig = self.build_fn_type(ctx, f);
            let fv  = module.add_function(&f.name, sig, None);
            mark_nounwind(fv); // H# has no unwinding (panic = abort/exit) — see llvm_optimize.rs
            func_vals.insert(f.name.clone(), fv);
        }

        // Pass 2: compile bodies
        for f in &fns {
            let fv = func_vals[&f.name];
            self.compile_fn(ctx, &module, &builder, &builtins, f, fv,
                            &func_vals, &mut str_globals, &structs)?;
        }

        // Target machine — tuned for the HOST CPU (native -march=native
        // equivalent) so generated binaries use AVX2/BMI2/etc when
        // available, matching the performance goal of this pass.
        Target::initialize_native(&InitializationConfig::default())
        .map_err(CodegenError::Llvm)?;
        let triple  = TargetMachine::get_default_triple();
        let target  = Target::from_triple(&triple)
        .map_err(|e| CodegenError::Llvm(e.to_string()))?;
        let opt_lvl = if self.opts.optimize { OptimizationLevel::Aggressive }
        else                   { OptimizationLevel::Default };

        let cpu_name     = TargetMachine::get_host_cpu_name();
        let cpu_features = TargetMachine::get_host_cpu_features();
        let cpu_str  = cpu_name.to_str().unwrap_or("x86-64");
        let feat_str = cpu_features.to_str().unwrap_or("+avx2,+bmi,+bmi2,+sse4.1,+sse4.2,+popcnt");

        let machine = target.create_target_machine(
            &triple, cpu_str, feat_str,
            opt_lvl, RelocMode::PIC, CodeModel::Small,
        ).ok_or_else(|| CodegenError::Llvm("cannot create target machine".into()))?;

        if let Err(e) = module.verify() {
            return Err(CodegenError::Llvm(format!(
                "LLVM module verification failed before optimization — this indicates a bug in the H# codegen itself (invalid IR was generated), not a problem with your source code. Please report this along with the command you ran.\n{}",
                e.to_string()
            )));
        }

        // ── SEGFAULT FIX (kept) ───────────────────────────────────────────
        // Only ONE optimization call per module. Previously:
        // optimize_module(O3) + minimize_size() caused a double-pipeline
        // segfault in LLVM's pass manager on --release. Single call only;
        // O3 already includes DCE + inlining + vectorization + size opts.
        let opt_num = if self.opts.optimize { 3 } else { 0 };
        optimize_module(&module, &machine, opt_num);
        // minimize_size intentionally removed — do NOT re-add it after O3.
        // ───────────────────────────────────────────────────────────────────

        Ok((module, machine))
    }

    fn is_move_sensitive_type(ty: &TypeExpr) -> bool {
        match ty {
            TypeExpr::Array(_) => true,
            TypeExpr::Named(n) => n == "string",
            _ => false,
        }
    }

    /// `@safety` basic v2: warn (never error — this deliberately can't
    /// block compilation) about a string/array-typed local being read
    /// after a plain `let y = x` moved it into another name. Unlike basic
    /// v1 (which only looked at a flat run of statements and reset the
    /// moved-set to empty whenever it hit an `if`/`while`/`match`/`for`/
    /// `do`/`unsafe`/closure body — silently skipping all of them), this
    /// recurses into every nested body and threads the moved-set through:
    ///   - `if`/`match`: each branch is checked starting from the same
    ///     incoming moved-set; a variable only becomes *definitely* moved
    ///     afterwards if it's moved on **every** branch (an `if` with no
    ///     `else`, or a branch that doesn't touch it, means it's still
    ///     usable afterward — that's the "no-op path" case).
    ///   - `while`/`for`: the body may run zero or more times, so nothing
    ///     new is guaranteed moved *after* the loop — but the body is now
    ///     actually checked (previously skipped entirely), and is checked
    ///     twice: once silently just to see what it moves, then again
    ///     with that fed back in as if it were already moved on entry, so
    ///     a variable moved near the end of one iteration and read again
    ///     near the top of the next is now caught too.
    ///   - `do`/`unsafe`: always execute exactly once, so whatever they
    ///     move folds straight into the surrounding flow, same as a
    ///     flat sequence of statements.
    ///   - closures: checked in isolation (they may run later, any number
    ///     of times) and don't feed anything back into the surrounding
    ///     flow.
    /// Still a heuristic, not a full dataflow fixed point: it has no real
    /// scoping (a `let` inside one `if` branch is — same as the rest of
    /// this codegen's `self.vars` — still nominally "known" afterward
    /// rather than going out of scope), and it doesn't understand
    /// `&`/`&mut` borrows beyond "taking a reference to an already-moved
    /// variable is still flagged as a use". Good enough to catch real
    /// cross-branch and cross-iteration move bugs that v1 missed
    /// entirely; not a soundness guarantee.
    fn check_moves_basic(body: &[Stmt], fn_name: &str) -> Vec<String> {
        let violations = std::cell::RefCell::new(Vec::new());
        Self::check_moves_block(body, HashMap::new(), fn_name, false, &violations);
        violations.into_inner()
    }

    /// Checks `body` given the set of variables already known-moved on
    /// entry (`moved_in`), warning (unless `silent`) about any read of an
    /// already-moved variable, and returns the set of variables that are
    /// *definitely* moved by the time control falls off the end of `body`
    /// — i.e. moved on every reachable straight-line path through it —
    /// which is what callers thread into whatever comes textually next.
    fn check_moves_block(
        body: &[Stmt],
        moved_in: HashMap<String, Span>,
        fn_name: &str,
        silent: bool,
        violations: &std::cell::RefCell<Vec<String>>,
    ) -> HashMap<String, Span> {
        let mut moved = moved_in;
        for s in body {
            match s {
                Stmt::Let { name, ty, value: Some(e), span, .. } => {
                    Self::check_moves_expr(e, &mut moved, fn_name, silent, violations);
                    let sensitive = ty.as_ref().map(Self::is_move_sensitive_type).unwrap_or(false);
                    if sensitive {
                        if let Expr::Ident(src, _) = e {
                            moved.insert(src.clone(), span.clone());
                        } else if let Some(key) = Self::field_move_key(e) {
                            // `let x = s.name` moves the *field*, not the
                            // whole struct `s` — `s.other_field` stays
                            // fine to read afterward, only `s.name`
                            // itself (and any later `x`, via the Ident
                            // case above) is flagged. Previously struct
                            // fields weren't tracked at all: moving a
                            // field out via a plain `let` was invisible
                            // to this check, so `s.name` used again after
                            // being moved out silently passed with no
                            // warning at all — a real gap in `@safety`'s
                            // coverage relative to a genuine ownership
                            // checker.
                            moved.insert(key, span.clone());
                        }
                    }
                    moved.remove(name);
                }
                Stmt::Let { .. } | Stmt::Continue(_) | Stmt::Import(..) => {}
                Stmt::Item(Item::FnDef(nested)) => {
                    // A nested/local fn is its own straight-line world —
                    // doesn't inherit or feed back into the enclosing one.
                    Self::check_moves_basic(&nested.body, &nested.name);
                }
                Stmt::Item(_) => {}
                Stmt::Expr(e, _) => Self::check_moves_expr(e, &mut moved, fn_name, silent, violations),
                Stmt::Return(Some(e), _) | Stmt::Break(Some(e), _) => {
                    Self::check_moves_expr(e, &mut moved, fn_name, silent, violations);
                }
                Stmt::Return(None, _) | Stmt::Break(None, _) => {}
            }
        }
        moved
    }

    /// A variable counts as "definitely moved" after a set of mutually
    /// exclusive branches only if every branch's own moved-set contains
    /// it — i.e. the intersection of the branch outputs' key sets.
    fn intersect_moved(outs: Vec<HashMap<String, Span>>) -> HashMap<String, Span> {
        let mut iter = outs.into_iter();
        let Some(mut acc) = iter.next() else { return HashMap::new() };
        for other in iter {
            acc.retain(|k, _| other.contains_key(k));
        }
        acc
    }

    /// Checks a single expression for moved-variable reads, recursing
    /// into sub-expressions, and — for the control-flow-shaped variants
    /// (`If`/`Match`/`While`/`For`/`Do`/`Unsafe`/`Closure`, all of which
    /// v1 completely ignored) — into their nested bodies too, updating
    /// `*moved` per the branch/loop merge rules documented on
    /// `check_moves_basic`. This handles both `Stmt::Expr(e, _)` (a
    /// control-flow construct used as a statement) and the same
    /// constructs appearing as a plain sub-expression (e.g. inside
    /// `let x = if cond { a } else { b }`), since both route through here.
    fn check_moves_expr(e: &Expr, moved: &mut HashMap<String, Span>, fn_name: &str, silent: bool, violations: &std::cell::RefCell<Vec<String>>) {
        match e {
            Expr::Ident(name, span) => {
                if silent { return; }
                if let Some(move_span) = moved.get(name) {
                    let msg = format!(
                        "{}: `{}` used here after being moved (moved at {}) in `{}`",
                        span, name, move_span, fn_name
                    );
                    eprintln!("warning: {} — move-after-use check (@default/@safety)", msg);
                    violations.borrow_mut().push(msg);
                }
            }
            Expr::BinOp(l, _, r, _) | Expr::Assign(l, r, _) | Expr::CompoundAssign(l, _, r, _) => {
                Self::check_moves_expr(l, moved, fn_name, silent, violations);
                Self::check_moves_expr(r, moved, fn_name, silent, violations);
            }
            Expr::UnOp(_, inner, _) | Expr::Cast(inner, _, _) |
            Expr::Try(inner, _) | Expr::Await(inner, _) => Self::check_moves_expr(inner, moved, fn_name, silent, violations),
            Expr::FieldAccess(obj, field, span) => {
                if !silent {
                    if let Some(key) = Self::field_move_key(e) {
                        if let Some(move_span) = moved.get(&key) {
                            let msg = format!(
                                "{}: `{}` used here after being moved (moved at {}) in `{}`",
                                span, key, move_span, fn_name
                            );
                            eprintln!("warning: {} — move-after-use check (@default/@safety)", msg);
                            violations.borrow_mut().push(msg);
                        }
                    }
                    let _ = field; // field name itself never needs its own move-check
                }
                Self::check_moves_expr(obj, moved, fn_name, silent, violations);
            }
            Expr::IndexAccess(a, b, _) => {
                Self::check_moves_expr(a, moved, fn_name, silent, violations);
                Self::check_moves_expr(b, moved, fn_name, silent, violations);
            }
            Expr::Call(callee, args, _) => {
                Self::check_moves_expr(callee, moved, fn_name, silent, violations);
                for a in args { Self::check_moves_expr(a, moved, fn_name, silent, violations); }
            }
            Expr::MethodCall(recv, _, args, _) => {
                Self::check_moves_expr(recv, moved, fn_name, silent, violations);
                for a in args { Self::check_moves_expr(a, moved, fn_name, silent, violations); }
            }
            Expr::ArrayLit(items, _) | Expr::TupleLit(items, _) => {
                for i in items { Self::check_moves_expr(i, moved, fn_name, silent, violations); }
            }
            Expr::StructLit(_, fields, _) => {
                for (_, v) in fields { Self::check_moves_expr(v, moved, fn_name, silent, violations); }
            }
            Expr::Return(Some(inner), _) => Self::check_moves_expr(inner, moved, fn_name, silent, violations),

            Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
                Self::check_moves_expr(condition, moved, fn_name, silent, violations);
                let then_out = Self::check_moves_block(then_body, moved.clone(), fn_name, silent, violations);
                let mut branch_outs = vec![then_out];
                for (cond, b) in elsif_branches {
                    Self::check_moves_expr(cond, moved, fn_name, silent, violations);
                    branch_outs.push(Self::check_moves_block(b, moved.clone(), fn_name, silent, violations));
                }
                *moved = if let Some(else_body) = else_body {
                    branch_outs.push(Self::check_moves_block(else_body, moved.clone(), fn_name, silent, violations));
                    Self::intersect_moved(branch_outs)
                } else {
                    // No `else` ⇒ an implicit no-op path exists, which
                    // moves nothing beyond what was already moved.
                    moved.clone()
                };
            }
            Expr::Match { subject, arms, .. } => {
                Self::check_moves_expr(subject, moved, fn_name, silent, violations);
                if !arms.is_empty() {
                    let mut arm_outs = Vec::with_capacity(arms.len());
                    for arm in arms {
                        if let Some(g) = &arm.guard { Self::check_moves_expr(g, moved, fn_name, silent, violations); }
                        arm_outs.push(Self::check_moves_block(&arm.body, moved.clone(), fn_name, silent, violations));
                    }
                    *moved = Self::intersect_moved(arm_outs);
                }
            }
            Expr::While { condition, body, .. } => {
                Self::check_moves_expr(condition, moved, fn_name, silent, violations);
                // Pass 1 (silent): just discover what the body itself moves.
                let collected = Self::check_moves_block(body, moved.clone(), fn_name, true, violations);
                // Pass 2 (real): re-check with those folded in as if
                // already moved on entry, catching "moved near the end of
                // one iteration, read again near the top of the next" —
                // impossible to see in v1, which never looked inside loop
                // bodies at all.
                let mut seed = moved.clone();
                seed.extend(collected);
                Self::check_moves_block(body, seed, fn_name, silent, violations);
                // Loop may run zero times — nothing new guaranteed after it.
            }
            Expr::For { iterable, body, .. } => {
                Self::check_moves_expr(iterable, moved, fn_name, silent, violations);
                let collected = Self::check_moves_block(body, moved.clone(), fn_name, true, violations);
                let mut seed = moved.clone();
                seed.extend(collected);
                Self::check_moves_block(body, seed, fn_name, silent, violations);
            }
            Expr::Do { body, .. } => {
                // Always runs exactly once — folds straight into the flow.
                *moved = Self::check_moves_block(body, moved.clone(), fn_name, silent, violations);
            }
            Expr::Unsafe(body, _, _) => {
                *moved = Self::check_moves_block(body, moved.clone(), fn_name, silent, violations);
            }
            Expr::Closure { body, .. } => {
                // May run later, any number of times — check in isolation,
                // don't feed its effects back into the surrounding flow.
                Self::check_moves_block(body, moved.clone(), fn_name, silent, violations);
            }
            _ => {}
        }
    }


    /// First real caller of `regions.rs`'s `RegionStack` (previously a
    /// complete, sensible set of data structures — `RegionKind`,
    /// `RegionTy`, move-tracking via `mark_moved` — that nothing in the
    /// compiler ever actually constructed or drove). This is a
    /// diagnostic-only pass: it mirrors `f`'s block structure with real
    /// `RegionStack` push/pop calls so heap-typed locals (`RegionTy::
    /// StringVal`/`BytesVal`/`Struct`/`Array`) still live when an
    /// `@safety` function returns get reported as "would need freeing in
    /// a full ownership model" — the same values `@arena` already frees
    /// for real via `hsh_arena_free`. Only run for `@safety` (not
    /// `@default`, which is the overwhelming majority of any real
    /// program's functions) since every non-trivial function has heap
    /// locals that are, today, only reclaimed at process exit — blasting
    /// a note for all of them everywhere would just be noise for people
    /// who haven't opted into caring; `@safety` is an explicit signal
    /// that this program wants that scrutiny. It deliberately does *not*
    /// insert actual `hsh_string_free`/`hsh_array_free`/struct-drop calls
    /// here: doing that safely requires knowing a value was never
    /// aliased elsewhere (returned, stored in a struct/array, passed to
    /// another function that keeps it, etc.), which this codegen doesn't
    /// track anywhere yet — inserting frees without that would risk
    /// double-frees or use-after-free, strictly worse than today's "never
    /// freed until process exit" leak. Turning this from a note into real
    /// codegen — for `@safety` first, then `@default` — is exactly the
    /// future work `regions.rs` was scaffolded for.
    fn region_drop_audit(f: &FnDef) {
        let mut regions = regions::RegionStack::new();
        regions.push_frame();
        Self::region_audit_block(&f.body, &mut regions);
        let (_, leftover) = regions.pop();
        for v in leftover {
            eprintln!(
                "note: {}: `{}` ({:?}) is still live when `{}` returns — a full ownership implementation would free it here (this is exactly what `@arena`'s `hsh_arena_free` already does for its whole call, end-to-end); `@default`/`@safety` don't insert a drop yet, so today it's only reclaimed when the process exits",
                f.span, v.name, v.ty, f.name
            );
        }
    }

    fn region_audit_block(body: &[Stmt], regions: &mut regions::RegionStack) {
        for s in body {
            match s {
                Stmt::Let { name, ty, value, .. } => {
                    if let Some(Expr::Ident(src, _)) = value {
                        regions.mark_moved(src);
                    }
                    let rty = ty.as_ref().map(|t| Self::type_expr_to_region_ty(t))
                        .unwrap_or(regions::RegionTy::Scalar);
                    regions.declare(name, rty);
                }
                Stmt::Expr(Expr::If { then_body, elsif_branches, else_body, .. }, _) => {
                    regions.push_scope();
                    Self::region_audit_block(then_body, regions);
                    let _ = regions.pop();
                    for (_, b) in elsif_branches {
                        regions.push_scope();
                        Self::region_audit_block(b, regions);
                        let _ = regions.pop();
                    }
                    if let Some(eb) = else_body {
                        regions.push_scope();
                        Self::region_audit_block(eb, regions);
                        let _ = regions.pop();
                    }
                }
                Stmt::Expr(Expr::While { body, .. }, _) | Stmt::Expr(Expr::For { body, .. }, _) => {
                    regions.push_scope();
                    Self::region_audit_block(body, regions);
                    let _ = regions.pop();
                }
                Stmt::Expr(Expr::Do { body, .. }, _) | Stmt::Expr(Expr::Unsafe(body, _, _), _) => {
                    // Always runs exactly once — same region as the caller.
                    Self::region_audit_block(body, regions);
                }
                Stmt::Return(Some(Expr::Ident(name, _)), _) | Stmt::Break(Some(Expr::Ident(name, _)), _) => {
                    // Returning/breaking with a bare `x` hands ownership to
                    // the caller — don't flag it as "still live" garbage.
                    regions.mark_moved(name);
                }
                _ => {}
            }
        }
    }

    fn type_expr_to_region_ty(t: &TypeExpr) -> regions::RegionTy {
        match t {
            TypeExpr::Array(_) => regions::RegionTy::Array(Box::new(regions::RegionTy::Scalar)),
            TypeExpr::Named(n) => regions::RegionTy::from_type_name(n),
            _ => regions::RegionTy::Scalar,
        }
    }

    /// Best-effort byte size for a struct field's type, used only by
    /// `ptr_field_offset` to compute an offset without a real
    /// `TargetData` query. Mirrors `llvm_types.rs::htype_to_llvm`'s
    /// actual representation choices exactly (same match arms) rather
    /// than reasoning about sizes independently, so this can't silently
    /// drift out of sync with what codegen actually emits: strings/
    /// bytes/arrays/structs/tuples/generics/refs/optionals/fn-values are
    /// all a single pointer- or i64-sized slot in this codegen (H#'s
    /// strings and arrays are heap-boxed, not inlined), so 8 bytes
    /// covers all of them; only the fixed-width integer/float/bool
    /// types need their own size. Assumes natural alignment (align ==
    /// size) with no packing control, which is what this codegen's
    /// struct layout actually follows today.
    fn field_natural_size(ty: &TypeExpr) -> u64 {
        match ty {
            TypeExpr::Named(n) => match n.as_str() {
                "i8" | "u8" | "bool"  => 1,
                "i16" | "u16"         => 2,
                "i32" | "u32" | "f32" => 4,
                _                     => 8, // int/i64/uint/u64/f64/string/bytes/opaque
            },
            TypeExpr::I8 | TypeExpr::U8 | TypeExpr::Bool => 1,
            TypeExpr::I16 | TypeExpr::U16                 => 2,
            TypeExpr::I32 | TypeExpr::U32 | TypeExpr::F32 => 4,
            _ => 8, // I64/U64/I128/U128/F64/String/Bytes/Ref/Array/Tuple/Generic/Fn/Optional
        }
    }

    /// Builds the compound key used to track a moved struct *field*
    /// (as opposed to a whole variable) — `Some("s.name")` for
    /// `s.name` where `s` is a plain local, `None` for anything deeper
    /// (`a.b.c`) or where the object isn't a bare identifier. One level
    /// is enough for the common `let x = s.field` case this exists to
    /// catch; deeper chains fall back to being untracked (leak, not a
    /// false positive) rather than trying to generalize the key scheme
    /// further.
    fn field_move_key(e: &Expr) -> Option<String> {
        if let Expr::FieldAccess(obj, field, _) = e {
            if let Expr::Ident(obj_name, _) = obj.as_ref() {
                return Some(format!("{}.{}", obj_name, field));
            }
        }
        None
    }

    fn collect_fns(&self, m: &HshModule) -> Vec<FnDef> {
        let mut fns = Vec::new();
        for item in &m.items {
            match item {
                Item::FnDef(f) => {
                    let mut f = f.clone();
                    let hoisted = crate::modules::hoist_nested_fns(&mut f.body, &f.name);
                    fns.push(f);
                    fns.extend(hoisted);
                }
                Item::ImplBlock(imp) => {
                    for method in &imp.methods {
                        let mangled_name = format!("{}_{}", imp.type_name, method.name);
                        let mut body = method.body.clone();
                        let hoisted = crate::modules::hoist_nested_fns(&mut body, &mangled_name);
                        fns.push(FnDef {
                            attrs: vec![], type_params: vec![],
                            name:        mangled_name,
                                 params:      method.params.clone(),
                                 return_type: method.return_type.clone(),
                                 body,
                                 pub_:        method.pub_,
                                 is_async:    false,
                                 is_unsafe:   method.is_unsafe,
                                 mem_mode:    method.mem_mode,
                                 span:        method.span.clone(),
                        });
                        fns.extend(hoisted);
                    }
                }
                _ => {}
            }
        }
        fns
    }

    fn build_fn_type<'ctx>(&self, ctx: &'ctx Context, f: &FnDef)
    -> inkwell::types::FunctionType<'ctx>
    {
        use inkwell::types::BasicMetadataTypeEnum;
        let mut param_types: Vec<BasicMetadataTypeEnum> = Vec::new();
        for p in &f.params {
            if p.name == "self" { continue; }
            if let Some(t) = htype_to_llvm(ctx, &p.ty) {
                param_types.push(t.into());
            }
        }
        if f.name == "main" {
            // Compile H# main() as C main(int argc, char** argv) so that
            // argc/argv are accessible at link time via _hsh_argc/_hsh_argv.
            let ptr = ctx.ptr_type(inkwell::AddressSpace::default());
            return ctx.i32_type().fn_type(&[ctx.i32_type().into(), ptr.into()], false);
        }
        match &f.return_type {
            None      => ctx.void_type().fn_type(&param_types, false),
            Some(ret) => match htype_to_llvm(ctx, ret) {
                None    => ctx.void_type().fn_type(&param_types, false),
                Some(t) => t.fn_type(&param_types, false),
            }
        }
    }

    /// §5: build an LLVM function type for an `extern [c/cpp/rust/python,
    /// "lib"] fn name(...)` declaration. Unlike `build_fn_type` (for
    /// H#-defined functions), this:
    ///   - never special-cases `main`
    ///   - honors `ExternFnDecl.variadic` (e.g. C's `printf`-style functions)
    ///   - treats a missing return type as `void` (C convention), not `i64`
    fn build_extern_fn_type<'ctx>(&self, ctx: &'ctx Context, f: &ExternFnDecl)
    -> inkwell::types::FunctionType<'ctx>
    {
        use inkwell::types::BasicMetadataTypeEnum;
        let mut param_types: Vec<BasicMetadataTypeEnum> = Vec::new();
        for p in &f.params {
            if let Some(t) = htype_to_llvm(ctx, &p.ty) {
                param_types.push(t.into());
            }
        }
        match &f.return_type {
            None      => ctx.void_type().fn_type(&param_types, f.variadic),
            Some(ret) => match htype_to_llvm(ctx, ret) {
                None    => ctx.void_type().fn_type(&param_types, f.variadic),
                Some(t) => t.fn_type(&param_types, f.variadic),
            }
        }
    }

    fn compile_fn<'ctx>(
        &self,
        ctx:         &'ctx Context,
        module:      &Module<'ctx>,
        builder:     &Builder<'ctx>,
        builtins:    &LlvmBuiltins<'ctx>,
        f:           &FnDef,
        fv:          FunctionValue<'ctx>,
        func_vals:   &HashMap<String, FunctionValue<'ctx>>,
        str_globals: &mut HashMap<String, PointerValue<'ctx>>,
        structs:     &HashMap<String, Vec<StructField>>,
    ) -> R<()> {
        let entry = ctx.append_basic_block(fv, "entry");
        builder.position_at_end(entry);

        let mut vars: HashMap<String, (PointerValue<'ctx>, BasicTypeEnum<'ctx>)> = HashMap::new();
        let mut var_types: HashMap<String, String> = HashMap::new();
        let mut array_elem_types: HashMap<String, String> = HashMap::new();
        let mut array_elem_llvm_ty: HashMap<String, BasicTypeEnum<'ctx>> = HashMap::new();
        let mut array_elem_type_expr: HashMap<String, TypeExpr> = HashMap::new();
        let mut pidx = 0u32;
        for p in &f.params {
            if p.name == "self" { continue; }
            if let TypeExpr::Named(n) = &p.ty {
                if structs.contains_key(n) {
                    var_types.insert(p.name.clone(), n.clone());
                }
            }
            if let TypeExpr::Array(elem) = &p.ty {
                if let TypeExpr::Named(n) = elem.as_ref() {
                    if structs.contains_key(n) {
                        array_elem_types.insert(p.name.clone(), n.clone());
                    }
                }
                if let Some(elem_llvm) = htype_to_llvm(ctx, elem) {
                    array_elem_llvm_ty.insert(p.name.clone(), elem_llvm);
                }
                array_elem_type_expr.insert(p.name.clone(), elem.as_ref().clone());
            }
            if let Some(llvm_ty) = htype_to_llvm(ctx, &p.ty) {
                let param_val = fv.get_nth_param(pidx).unwrap();
                let ptr       = builder.build_alloca(llvm_ty, &p.name).unwrap();
                builder.build_store(ptr, param_val).unwrap();
                vars.insert(p.name.clone(), (ptr, llvm_ty));
                pidx += 1;

                // Performance: H# string/bytes params are guaranteed
                // non-null by the runtime's `if (!s) return "";` contract
                // (see runtime.rs). Telling LLVM this lets it elide
                // defensive null checks around every use of the param.
                if matches!(llvm_ty, BasicTypeEnum::PointerType(_)) {
                    crate::llvm_optimize::mark_param_nonnull(fv, pidx - 1);
                }
            }
        }

        let mut cx = FnCx {
            ctx, module, builder, builtins, func_vals, str_globals,
            vars, fn_name: f.name.clone(), ret_type: f.return_type.clone(),
            structs, var_types, array_elem_types, array_elem_llvm_ty, array_elem_type_expr, mem_mode: f.mem_mode,
            arc_owned: std::cell::RefCell::new(Vec::new()),
            branch_depth: std::cell::Cell::new(0),
            loop_stack: Vec::new(),
        };

        match f.mem_mode {
            MemoryMode::Safety => {
                // BUG FIX / real expansion: `@safety` used to be purely
                // advisory — the move-after-use check ran and printed
                // warnings, but nothing about marking a function `@safety`
                // actually *enforced* anything; a violation and a clean
                // function compiled identically. That's backwards for an
                // annotation whose entire point is opting into stricter
                // checking. `@default` keeps the old warn-only behavior
                // (a function that never asked for scrutiny shouldn't
                // suddenly fail to build), but `@safety` now means what it
                // says: a real move-after-use is a compile *error* here,
                // not a note easily lost in build output.
                eprintln!(
                    "note: {}: `@safety` on `{}` runs a control-flow-aware straight-line move-after-use check (recurses into if/while/match/for/do/unsafe) and treats any violation as a hard compile error — not just a warning like `@default` gets. Still a heuristic (no real scoping, no borrow understanding beyond \"a reference to an already-moved variable is a use\"), not a full ownership/borrow checker or a soundness guarantee",
                    f.span, f.name
                );
                let violations = Self::check_moves_basic(&f.body, &f.name);
                if !violations.is_empty() {
                    return Err(CodegenError::SafetyViolation { fn_name: f.name.clone(), violations });
                }
                Self::region_drop_audit(f);
            }
            MemoryMode::Arc => {
                eprintln!(
                    "note: {}: `@arc` on `{}` — basic v2: `arc_alloc`/`arc_retain`/`arc_release`/`arc_count` are available (real atomic refcounting), and plain `let x = arc_alloc(n)` / `let y = x` bindings at the function's top level (not inside if/while/for/match/do/unsafe) are now retained/released for you automatically, including on reassignment (`x = ...` releases whatever `x` held before, not just at return). Locals only bound inside a branch, or an arc pointer returned inside a struct/array instead of as a bare `x`, still need manual `arc_retain`/`arc_release`",
                    f.span, f.name
                );
            }
            MemoryMode::Pointers => {
                eprintln!(
                    "note: {}: `@pointers` on `{}` — basic v2: typed `ptr_read_*`/`ptr_write_*` builtins are available for i8/i16/i32/i64/f32/f64/ptr, plus `ptr_add`/`ptr_is_null` (all unchecked by design, trusts the caller). The typechecker now also enforces that these and the `@arc` builtins are only reachable from a `@pointers`/`@arc` function or an `unsafe ... end` block — see typechecker.rs — so the annotation is a real, checked boundary rather than a doc-only hint",
                    f.span, f.name
                );
            }
            MemoryMode::Arena => {
                // Bump-allocate everything this call creates into a fresh
                // arena, freed on every exit path (see
                // `build_return_coerced`'s epilogue). 1 MiB is a starting
                // default — `hsh_arena_alloc` degrades to a plain malloc
                // if a call ever needs more than that, so this is a
                // performance knob, not a correctness one.
                const DEFAULT_ARENA_CAP: u64 = 1024 * 1024;
                let cap = cx.ctx.i64_type().const_int(DEFAULT_ARENA_CAP, false);
                let arena = cx.call_coerced(cx.builtins.hsh_arena_new, &[cap.into()], "fn_arena");
                let arena_val = cx.unwrap_call(arena);
                cx.call_coerced(cx.builtins.hsh_arena_push_current, &[arena_val], "");
            }
            // `@default` now runs the same straight-line move-after-use
            // check `@safety` does — see `check_moves_basic`'s doc
            // comment for exactly what it catches. Previously this was
            // opt-in only (you had to write `@safety` to get any
            // memory-safety diagnostics at all); every other H# function
            // — which is to say, the overwhelming majority of any real
            // program, since nobody annotates every single `fn` — got
            // zero scrutiny. This is deliberately *not* Rust's borrow
            // checker: it never blocks compilation (always `warning:`,
            // never `error:` — see the note below), it's one flat AST
            // walk per function rather than a whole-program alias/
            // lifetime analysis, and it doesn't touch codegen at all, so
            // it costs a tiny, constant amount of extra compile time
            // rather than the proportionally-much-larger cost Rust pays
            // for soundness. `@safety` still exists as an explicit,
            // opt-in signal that *also* runs `region_drop_audit` (the
            // "would need freeing here in a full ownership model" note)
            // — `@default` deliberately doesn't, to avoid spamming notes
            // about every heap local in code that never asked for that
            // level of scrutiny.
            MemoryMode::Default => {
                Self::check_moves_basic(&f.body, &f.name);
            }
        }

        // ── async fn: wrap body in a pthread-based task launcher ─────────────
        // An `async fn foo(...)` compiles as:
        //   1. A normal `__hsh_async_foo(...)` that does the real work.
        //   2. A thin wrapper `foo(...)` that calls `hsh_task_spawn(__hsh_async_foo, args)`
        //      and returns an opaque *i64 task handle. `await` on that handle calls
        //      `hsh_task_wait(handle)` which joins the pthread.
        // For now we mark the fn with a special prefix so the linker can find both.
        // The spawn/wait ABI is implemented in the runtime C layer (hsh_async_rt.c).
        if f.is_async {
            // The function body compiles normally inside the `__hsh_async_` prefixed fn.
            // The public `foo` wrapper is generated separately in `emit_async_wrapper`.
            // Here we just ensure the entry block is built.
        }

        // ── Inject argc/argv storage at the top of main() ─────────────────────
        // We emit:
        //   extern int _hsh_argc; extern char** _hsh_argv;
        //   _hsh_argc = argc; _hsh_argv = argv;
        // so that hsh_env_args() in core.c can retrieve them later.
        if f.name == "main" {
            let ptr_ty  = ctx.ptr_type(inkwell::AddressSpace::default());
            let i32_ty  = ctx.i32_type();

            // Declare globals (or get if already declared)
            let g_argc = module.get_global("_hsh_argc")
                .unwrap_or_else(|| module.add_global(i32_ty,  None, "_hsh_argc"));
            let g_argv = module.get_global("_hsh_argv")
                .unwrap_or_else(|| module.add_global(ptr_ty,  None, "_hsh_argv"));
            g_argc.set_linkage(inkwell::module::Linkage::External);
            g_argv.set_linkage(inkwell::module::Linkage::External);

            // Store argc (param 0) and argv (param 1)
            let argc_val = fv.get_nth_param(0).unwrap();
            let argv_val = fv.get_nth_param(1).unwrap();
            builder.build_store(g_argc.as_pointer_value(), argc_val).unwrap();
            builder.build_store(g_argv.as_pointer_value(), argv_val).unwrap();
        }

        let terminated = cx.stmts(&f.body)?;

        if !terminated {
            cx.build_return_coerced(None)?;
        }
        Ok(())
    }

    /// Emit a thin async wrapper function `name(...)` that launches the
    /// real async body `__hsh_async_name(...)` on a pthread and returns
    /// an opaque `*i8` task handle.  `await` on that handle calls
    /// `hsh_task_wait(handle)` which joins the thread.
    ///
    /// Called once per `async fn` after the body function is compiled.
    fn emit_async_wrapper<'ctx>(
        &self,
        ctx:       &'ctx Context,
        module:    &Module<'ctx>,
        builder:   &Builder<'ctx>,
        f:         &FnDef,
        body_fn:   FunctionValue<'ctx>,
    ) -> R<FunctionValue<'ctx>> {
        // Wrapper has the same signature as the body function
        let fn_ty  = body_fn.get_type();
        let wrapper = module.add_function(&f.name, fn_ty, None);
        let entry   = ctx.append_basic_block(wrapper, "entry");
        builder.position_at_end(entry);

        // Look up hsh_task_spawn(fn_ptr: *i8, args: *i8) -> *i8
        let i8ptr    = ctx.ptr_type(inkwell::AddressSpace::default());
        let spawn_ty = i8ptr.fn_type(&[i8ptr.into(), i8ptr.into()], false);
        let spawn_fn = module.get_function("hsh_task_spawn")
            .unwrap_or_else(|| module.add_function("hsh_task_spawn", spawn_ty, None));

        // Cast body_fn pointer to *i8 (opaque pointer — bit_cast is a no-op
        // under LLVM's opaque-pointer model but keeps the IR builder happy
        // across inkwell versions that still require an explicit cast).
        let fn_ptr_i8 = builder.build_bit_cast(
            body_fn.as_global_value().as_pointer_value(),
            i8ptr,
            "fn_ptr"
        ).unwrap();

        // Pack args into a heap struct via hsh_task_pack_args (runtime helper)
        // For now pass nullptr (args encoding is done by the runtime layer)
        let null_args = i8ptr.const_null();

        let handle = builder.build_call(
            spawn_fn,
            &[fn_ptr_i8.into(), null_args.into()],
            "task_handle"
        ).unwrap();

        let handle_val = unwrap_call(ctx, handle);
        builder.build_return(Some(&handle_val)).unwrap();
        Ok(wrapper)
    }

    fn zero_val<'ctx>(&self, ctx: &'ctx Context, ty: BasicTypeEnum<'ctx>) -> BasicValueEnum<'ctx> {
        match ty {
            BasicTypeEnum::IntType(t)     => t.const_zero().into(),
            BasicTypeEnum::FloatType(t)   => t.const_zero().into(),
            BasicTypeEnum::PointerType(t) => t.const_null().into(),
            _                             => ctx.i64_type().const_zero().into(),
        }
    }

    /// §5 phase 1.5: generate a callable trampoline body for one
    /// `extern [python, "module"] fn name(params...) -> ret` declaration.
    ///
    /// Generated logic (all via direct IR builder calls — no AST/FnCx
    /// needed, the body shape is fixed):
    ///
    ///   1. Build a Python source string:
    ///        "import {module}\nprint({module}.{name}(<args>))"
    ///      where each H# argument is marshaled to a Python literal:
    ///        - string params -> `hsh_py_repr(arg)`  (proper 'quoted' literal)
    ///        - numeric/bool params -> `hsh_int_to_string(arg)` (valid Python int literal)
    ///   2. Call `hsh_py_eval(code)` -> captured stdout (includes trailing "\n" from `print`)
    ///   3. `hsh_trim(...)` to strip the trailing newline
    ///   4. Marshal the result back to the declared return type:
    ///        - `string` (or no return type) -> the trimmed string as-is
    ///        - numeric types -> `hsh_atoll(trimmed)`
    ///        - `f32`/`f64` -> `hsh_atof(trimmed)`
    ///        - `bool` -> `hsh_atoll(trimmed) != 0`
    ///
    /// Limitations (documented for users): only scalar string/int/float/
    /// bool params and returns are supported. Arrays/structs/`any` are
    /// NOT marshaled (phase 2 — full libpython embedding — is needed for
    /// that; see roadmap).
    fn compile_python_trampoline<'ctx>(
        &self,
        ctx:      &'ctx Context,
        module:   &Module<'ctx>,
        builder:  &Builder<'ctx>,
        builtins: &LlvmBuiltins<'ctx>,
        py_module: &str,
        f:        &ExternFnDecl,
        fv:       FunctionValue<'ctx>,
    ) -> R<()> {
        let _ = module;
        let entry = ctx.append_basic_block(fv, "entry");
        builder.position_at_end(entry);

        // code = "import {py_module}\nprint({py_module}.{name}("
        let prefix = format!("import {m}\nprint({m}.{fname}(", m = py_module, fname = f.name);
        let mut code: BasicValueEnum = builder.build_global_string_ptr(&prefix, ".pycode").unwrap()
        .as_pointer_value().into();

        let mut pidx = 0u32;
        for (i, p) in f.params.iter().enumerate() {
            let arg = fv.get_nth_param(pidx).ok_or_else(|| CodegenError::Llvm(format!("missing param {} for extern python fn {}", p.name, f.name)))?;
            pidx += 1;

            let marshaled: BasicValueEnum = if is_string_type(&p.ty) {
                let r = builder.build_call(builtins.hsh_py_repr, &[arg.into()], "pyrepr").unwrap();
                unwrap_call(ctx, r)
            } else {
                // numeric/bool: hsh_int_to_string produces a valid Python
                // int literal (e.g. "42", "-7"). Bools are passed as i8
                // 0/1 — also valid Python ints.
                let as_i64 = match arg {
                    BasicValueEnum::IntValue(iv) =>
                    builder.build_int_cast(iv, ctx.i64_type(), "to_i64").unwrap().into(),
                    BasicValueEnum::FloatValue(fval) =>
                    builder.build_float_to_signed_int(fval, ctx.i64_type(), "f2i").unwrap().into(),
                    other => other,
                };
                let r = builder.build_call(builtins.hsh_int_to_string, &[as_i64.into()], "argstr").unwrap();
                unwrap_call(ctx, r)
            };

            code = unwrap_call(ctx, builder.build_call(builtins.hsh_strcat, &[code.into(), marshaled.into()], "cat_arg").unwrap());

            if i + 1 < f.params.len() {
                let comma = builder.build_global_string_ptr(",", ".pycomma").unwrap().as_pointer_value();
                code = unwrap_call(ctx, builder.build_call(builtins.hsh_strcat, &[code.into(), comma.into()], "cat_comma").unwrap());
            }
        }

        let suffix = builder.build_global_string_ptr("))", ".pysuffix").unwrap().as_pointer_value();
        code = unwrap_call(ctx, builder.build_call(builtins.hsh_strcat, &[code.into(), suffix.into()], "cat_suffix").unwrap());

        // result = trim(py_eval(code))
        let raw     = unwrap_call(ctx, builder.build_call(builtins.hsh_py_eval, &[code.into()], "pyresult").unwrap());
        let trimmed = unwrap_call(ctx, builder.build_call(builtins.hsh_trim, &[raw.into()], "pytrim").unwrap());

        // Marshal back to the declared return type.
        let ret_val: Option<BasicValueEnum> = match &f.return_type {
            None => None,
            Some(ty) if is_string_type(ty) => Some(trimmed),
            Some(ty) if is_float_type(ty) => {
                let r = builder.build_call(builtins.hsh_atof, &[trimmed.into()], "pyfloat").unwrap();
                Some(unwrap_call(ctx, r))
            }
            Some(ty) if is_bool_type(ty) => {
                let r = builder.build_call(builtins.hsh_atoll, &[trimmed.into()], "pyint").unwrap();
                let iv = unwrap_call(ctx, r).into_int_value();
                let zero = iv.get_type().const_zero();
                let b = builder.build_int_compare(inkwell::IntPredicate::NE, iv, zero, "pybool").unwrap();
                Some(builder.build_int_z_extend(b, ctx.i8_type(), "pybool8").unwrap().into())
            }
            Some(_numeric) => {
                let r = builder.build_call(builtins.hsh_atoll, &[trimmed.into()], "pyint").unwrap();
                Some(unwrap_call(ctx, r))
            }
        };

        match ret_val {
            Some(v) => { builder.build_return(Some(&v)).unwrap(); }
            None    => { builder.build_return(None).unwrap(); }
        }
        Ok(())
    }

    /// Detect whether we're linking on Termux (Android's bionic libc via a
    /// Termux userland), which needs a meaningfully different link recipe
    /// than a normal glibc/musl Linux desktop:
    ///  - `-lm`/`-lpthread`/`-ldl` don't exist as separate libraries at
    ///    all on bionic — math/pthread/dl are folded straight into libc,
    ///    so passing these flags just makes `ld.lld` fail with
    ///    "unable to find library" (`-lc` itself can fail the same way
    ///    once the linker's default library search has already gone
    ///    sideways from an earlier unresolved `-l`).
    ///  - `-no-pie` isn't just unsupported, it's actively wrong — Android
    ///    has required PIE executables since API 21, so asking for a
    ///    non-PIE binary can push the linker down a different, broken
    ///    path (matches the `argument unused` warning immediately
    ///    followed by every `-l` failing).
    /// Detected at runtime (not via `#[cfg(target_os = ...)]`) because a
    /// `hsharp` binary built *on* Termux typically still reports as a
    /// normal `linux` Rust target — Termux doesn't get its own
    /// `target_os`. `TERMUX_VERSION` is set by Termux itself in every
    /// session; `PREFIX` pointing at the Termux sysroot is a second,
    /// independent signal in case that ever changes.
    fn is_termux() -> bool {
        std::env::var_os("TERMUX_VERSION").is_some()
            || std::env::var("PREFIX")
                .map(|p| p.contains("com.termux"))
                .unwrap_or(false)
    }

    fn emit_binary_with_machine(&self, module: &Module, machine: &TargetMachine) -> R<()> {
        // ── Locate the runtime directory ─────────────────────────────────────
        // The runtime/ directory lives next to the compiler binary:
        //   <exe_dir>/runtime/core.c
        //   <exe_dir>/runtime/regex.c   (optional — only if program uses regex::)
        //   <exe_dir>/runtime/sqlite.c  (optional — only if program uses db::)
        //
        // Fallback: try the source tree at compile time (dev builds).
        let rt_dir = std::env::current_exe()
            .ok()
            .and_then(|p| p.parent().map(|d| d.join("runtime")))
            .filter(|p| p.is_dir())
            .or_else(|| {
                // Dev fallback: source-code/compiler/runtime/ relative to this file
                option_env!("CARGO_MANIFEST_DIR")
                    .map(|d| std::path::PathBuf::from(d).join("runtime"))
                    .filter(|p| p.is_dir())
            });

        let tmp_base = std::env::temp_dir().join(format!("hsharp_rt_{}", std::process::id()));
        let rt_opt = if self.opts.optimize { "-O2" } else { "-O0" };

        // ── Detect which optional runtime modules the program needs ──────────
        // Walk the AST once to check for regex:: and db:: usage.
        // This determines which .c files (and -l flags) are compiled in.
        let (needs_regex, needs_db) = self.detect_runtime_needs();

        // ── Runtime link flags (built early — used by SharedLib + Binary) ────
        let mut runtime_libs: Vec<String> = Vec::new();
        if needs_regex {
            match pkg_config_libs("libpcre2-8") {
                Some(libs) => runtime_libs.extend(libs),
                None       => runtime_libs.push("-lpcre2-8".to_string()),
            }
        }
        if needs_db {
            match pkg_config_libs("sqlite3") {
                Some(libs) => runtime_libs.extend(libs),
                None       => runtime_libs.push("-lsqlite3".to_string()),
            }
        }
        // Always link pthreads (needed by async_rt.c) — except on Termux,
        // where bionic libc has no separate libpthread.so at all (pthread_*
        // symbols live directly in libc).
        if !Self::is_termux() {
            runtime_libs.push("-lpthread".to_string());
        }

        // ── Compile each runtime C file → object file ────────────────────────
        let mut rt_objects: Vec<String> = Vec::new();

        let rt_files: &[(&str, bool, &[&str])] = &[
            // (filename, always_include, extra_packages_for_pkg_config)
            ("core.c",     true,         &[]),
            ("regex.c",    needs_regex,  &["libpcre2-8"]),
            ("sqlite.c",   needs_db,     &["sqlite3"]),
            // async runtime — always included; links -lpthread
            ("async_rt.c", true,         &[]),
        ];

        for (fname, include, pkgs) in rt_files {
            if !include { continue; }

            let src_path = if let Some(ref dir) = rt_dir {
                dir.join(fname)
            } else {
                // Last resort: write from embedded fallback string
                // (only core.c has a fallback; regex/sqlite don't need one
                // since if rt_dir is missing they also aren't being compiled)
                let p = tmp_base.with_extension(format!("{}.c", fname));
                if *fname == "core.c" {
                    std::fs::write(&p, crate::runtime::runtime_c_source())?;
                }
                p
            };

            let obj_path = tmp_base.with_extension(format!("{}.o", fname));
            let obj_str  = obj_path.to_string_lossy().into_owned();

            let mut cflags: Vec<String> = vec![
                rt_opt.to_string(),
                "-ffunction-sections".into(),
                "-fdata-sections".into(),
                "-fPIC".into(),
            ];
            if self.opts.optimize {
                cflags.push("-fno-asynchronous-unwind-tables".into());
                cflags.push("-fomit-frame-pointer".into());
            }
            for pkg in *pkgs {
                if let Some(flags) = pkg_config_cflags(pkg) {
                    cflags.extend(flags);
                }
            }
            cflags.extend([
                "-c".to_string(),
                src_path.to_string_lossy().into_owned(),
                "-o".to_string(),
                obj_str.clone(),
            ]);

            let ok = std::process::Command::new("cc")
                .args(&cflags)
                .status()?.success();
            if !ok {
                let hint = if *fname == "regex.c" {
                    " — is libpcre2-dev installed? (sudo apt install libpcre2-dev)"
                } else if *fname == "sqlite.c" {
                    " — is libsqlite3-dev installed? (sudo apt install libsqlite3-dev)"
                } else {
                    " — check that cc/gcc is installed"
                };
                return Err(CodegenError::Link(
                    format!("runtime compile failed ({}){}", fname, hint)
                ));
            }
            rt_objects.push(obj_str);
        }

        if let Err(e) = module.verify() {
            return Err(CodegenError::Llvm(format!(
                "LLVM module verification failed — this indicates a bug in the H# codegen itself (invalid IR was generated), not a problem with your source code. Please report this along with the command you ran.\n{}",
                e.to_string()
            )));
        }

        let obj_path = format!("{}_main.o", self.opts.output);
        machine.write_to_file(module, FileType::Object, Path::new(&obj_path))
        .map_err(|e| CodegenError::Llvm(e.to_string()))?;

        // ── Dispatch by output kind ──────────────────────────────────────────
        match self.opts.output_kind {
            OutputKind::Object => {
                let obj_out = format!("{}.o", self.opts.output);
                std::fs::copy(&obj_path, &obj_out)
                    .map_err(|e| CodegenError::Io(e))?;
                std::fs::remove_file(&obj_path).ok();
                for rt_o in &rt_objects { std::fs::remove_file(rt_o).ok(); }
                eprintln!("  note: object file emitted: {}", obj_out);
                return Ok(());
            }
            OutputKind::StaticLib => {
                let arc_out = format!("{}.a", self.opts.output);
                // ar rcs archive.a main.o [rt.o ...]
                let mut ar = std::process::Command::new("ar");
                ar.arg("rcs").arg(&arc_out).arg(&obj_path);
                for rt_o in &rt_objects { ar.arg(rt_o); }
                let ar_res = ar.output()?;
                std::fs::remove_file(&obj_path).ok();
                for rt_o in &rt_objects { std::fs::remove_file(rt_o).ok(); }
                if !ar_res.status.success() {
                    return Err(CodegenError::Link(
                        format!("ar failed: {}", String::from_utf8_lossy(&ar_res.stderr))
                    ));
                }
                eprintln!("  note: static library emitted: {}", arc_out);
                return Ok(());
            }
            OutputKind::SharedLib => {
                let so_suffix = self.opts.output_kind.file_suffix(&self.opts.target);
                let out = format!("{}{}", self.opts.output, so_suffix);
                let extern_args = self.link_flags.borrow().to_cc_args();
                let mut cmd = std::process::Command::new("cc");
                cmd.arg("-shared").arg("-fPIC");
                cmd.arg(&obj_path);
                for rt_o in &rt_objects { cmd.arg(rt_o); }
                cmd.arg("-o").arg(&out);
                if !Self::is_termux() { cmd.args(["-lm", "-lpthread", "-ldl"]); }
                for lib in &runtime_libs { cmd.arg(lib); }
                for a in &extern_args    { cmd.arg(a); }
                if self.opts.optimize { cmd.arg("-O2"); }
                let res = cmd.output()?;
                std::fs::remove_file(&obj_path).ok();
                for rt_o in &rt_objects { std::fs::remove_file(rt_o).ok(); }
                if !res.status.success() {
                    return Err(CodegenError::Link(
                        format!("shared lib link failed: {}", String::from_utf8_lossy(&res.stderr))
                    ));
                }
                eprintln!("  note: shared library emitted: {}", out);
                return Ok(());
            }
            OutputKind::Binary => {}  // fall through to the normal binary link below
        }

        let has_main = module.get_function("main").is_some();
        if !has_main {
            let obj_out = format!("{}.o", self.opts.output);
            std::fs::copy(&obj_path, &obj_out).ok();
            eprintln!("  note: no `main` fn — compiled as object: {}", obj_out);
            std::fs::remove_file(&obj_path).ok();
            for rt_o in &rt_objects { std::fs::remove_file(rt_o).ok(); }
            return Ok(());
        }

        let suffix = self.opts.target.exe_suffix();
        let out    = format!("{}{}", self.opts.output, suffix);

        let extern_args = self.link_flags.borrow().to_cc_args();

        let mut cmd = std::process::Command::new("cc");
        cmd.arg(&obj_path);
        for rt_o in &rt_objects { cmd.arg(rt_o); }
        cmd.arg("-o").arg(&out);
        let on_termux = Self::is_termux();
        if !on_termux { cmd.arg("-no-pie"); }
        if !on_termux { cmd.args(["-lm", "-lpthread", "-ldl"]); }
        for lib in &runtime_libs { cmd.arg(lib); }
        for a in &extern_args    { cmd.arg(a); }
        if self.opts.optimize {
            cmd.args(["-O2", "-Wl,--gc-sections", "-Wl,--as-needed",
                     "-Wl,--strip-all", "-flto"]);
        } else {
            cmd.arg("-O0");
        }
        if self.opts.static_link { cmd.arg("-static"); }

        let result = cmd.output()?;
        if !result.status.success() {
            let mut cmd2 = std::process::Command::new("cc");
            cmd2.arg(&obj_path);
            for rt_o in &rt_objects { cmd2.arg(rt_o); }
            cmd2.arg("-o").arg(&out);
            if !on_termux { cmd2.arg("-no-pie"); }
            if !on_termux { cmd2.args(["-lm", "-lpthread", "-ldl"]); }
            for lib in &runtime_libs { cmd2.arg(lib); }
            for a in &extern_args    { cmd2.arg(a); }
            if self.opts.optimize { cmd2.arg("-O2"); }
            if self.opts.static_link { cmd2.arg("-static"); }
            let r2 = cmd2.output()?;
            if !r2.status.success() {
                let stderr = String::from_utf8_lossy(&result.stderr);
                let hint = if stderr.contains("pcre2") {
                    "\nhint: sudo apt install libpcre2-dev"
                } else if stderr.contains("sqlite3") {
                    "\nhint: sudo apt install libsqlite3-dev"
                } else if stderr.contains("cannot find -l") {
                    "\nhint: check `extern [c/cpp/rust, \"...\"]` library names and that -L search paths include them (LIBRARY_PATH env var)"
                } else {
                    ""
                };
                return Err(CodegenError::Link(format!("{}{}", stderr, hint)));
            }
        }

        if self.opts.optimize {
            let _ = std::process::Command::new("strip")
            .args(["--strip-all", "--strip-unneeded", &out])
            .status();
        }

        let _ = std::fs::remove_file(&obj_path);
        for rt_o in &rt_objects { let _ = std::fs::remove_file(rt_o); }
        Ok(())
    }

    /// Scan the H# module AST once to determine which optional runtime
    /// modules are actually needed. Returns (needs_regex, needs_db).
    ///
    /// - needs_regex → compile runtime/regex.c + link -lpcre2-8
    /// - needs_db    → compile runtime/sqlite.c + link -lsqlite3
    ///
    /// Programs that use neither get a binary with zero pcre2/sqlite3
    /// dependency — the linker never sees those symbols at all.
    fn detect_runtime_needs(&self) -> (bool, bool) {
        (self.uses_regex.get(), self.uses_db.get())
    }
}

/// Walk an Item and set `has_regex`/`has_db` if `regex::` or `db::` paths
/// are found anywhere inside (expressions, sub-items, nested blocks).
fn scan_item_features(item: &Item, has_regex: &mut bool, has_db: &mut bool) {
    match item {
        Item::FnDef(f) => {
            for stmt in &f.body { scan_stmt_features(stmt, has_regex, has_db); }
        }
        Item::ImplBlock(imp) => {
            for m in &imp.methods {
                for stmt in &m.body { scan_stmt_features(stmt, has_regex, has_db); }
            }
        }
        Item::ModDecl { inline: Some(items), .. } => {
            for it in items { scan_item_features(it, has_regex, has_db); }
        }
        _ => {}
    }
}

fn scan_stmt_features(stmt: &Stmt, has_regex: &mut bool, has_db: &mut bool) {
    match stmt {
        Stmt::Let { value: Some(e), .. } | Stmt::Return(Some(e), _) |
        Stmt::Expr(e, _) | Stmt::Break(Some(e), _) =>
            scan_expr_features(e, has_regex, has_db),
        Stmt::Item(it) => scan_item_features(it, has_regex, has_db),
        _ => {}
    }
}

fn scan_expr_features(expr: &Expr, has_regex: &mut bool, has_db: &mut bool) {
    if *has_regex && *has_db { return; }
    match expr {
        Expr::Call(callee, args, _) => {
            if let Expr::Path(segs, _) = callee.as_ref() {
                if !segs.is_empty() {
                    match segs[0].as_str() {
                        "regex" => *has_regex = true,
                        "db"    => *has_db = true,
                        _       => {}
                    }
                }
            }
            scan_expr_features(callee, has_regex, has_db);
            for a in args { scan_expr_features(a, has_regex, has_db); }
        }
        Expr::Path(segs, _) => {
            if !segs.is_empty() {
                match segs[0].as_str() {
                    "regex" => *has_regex = true,
                    "db"    => *has_db = true,
                    _       => {}
                }
            }
        }
        Expr::MethodCall(obj, _, args, _) => {
            scan_expr_features(obj, has_regex, has_db);
            for a in args { scan_expr_features(a, has_regex, has_db); }
        }
        // BinOp(Box<Expr>, BinOp, Box<Expr>, Span)
        Expr::BinOp(a, _, b, _) => {
            scan_expr_features(a, has_regex, has_db);
            scan_expr_features(b, has_regex, has_db);
        }
        // UnOp(UnOp, Box<Expr>, Span)
        Expr::UnOp(_, a, _) => scan_expr_features(a, has_regex, has_db),
        Expr::Try(a, _)   => scan_expr_features(a, has_regex, has_db),
        Expr::Await(a, _) => scan_expr_features(a, has_regex, has_db),
        Expr::FieldAccess(a, _, _) => scan_expr_features(a, has_regex, has_db),
        // IndexAccess(Box<Expr>, Box<Expr>, Span)
        Expr::IndexAccess(a, b, _) => {
            scan_expr_features(a, has_regex, has_db);
            scan_expr_features(b, has_regex, has_db);
        }
        Expr::Return(Some(a), _) => scan_expr_features(a, has_regex, has_db),
        Expr::Cast(a, _, _) => scan_expr_features(a, has_regex, has_db),
        Expr::Range(a, b, _, _) => {
            scan_expr_features(a, has_regex, has_db);
            scan_expr_features(b, has_regex, has_db);
        }
        // Assign(Box<Expr>, Box<Expr>, Span)
        Expr::Assign(a, b, _) => {
            scan_expr_features(a, has_regex, has_db);
            scan_expr_features(b, has_regex, has_db);
        }
        // CompoundAssign(Box<Expr>, BinOp, Box<Expr>, Span)
        Expr::CompoundAssign(a, _, b, _) => {
            scan_expr_features(a, has_regex, has_db);
            scan_expr_features(b, has_regex, has_db);
        }
        // If { condition, then_body, elsif_branches, else_body, .. }
        Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
            scan_expr_features(condition, has_regex, has_db);
            for s in then_body { scan_stmt_features(s, has_regex, has_db); }
            for (cond, body) in elsif_branches {
                scan_expr_features(cond, has_regex, has_db);
                for s in body { scan_stmt_features(s, has_regex, has_db); }
            }
            if let Some(body) = else_body {
                for s in body { scan_stmt_features(s, has_regex, has_db); }
            }
        }
        Expr::Match { subject, arms, .. } => {
            scan_expr_features(subject, has_regex, has_db);
            for arm in arms { for s in &arm.body { scan_stmt_features(s, has_regex, has_db); } }
        }
        // While { condition, body, .. }
        Expr::While { condition, body, .. } => {
            scan_expr_features(condition, has_regex, has_db);
            for s in body { scan_stmt_features(s, has_regex, has_db); }
        }
        // For { pattern, iterable, body, .. }
        Expr::For { iterable, body, .. } => {
            scan_expr_features(iterable, has_regex, has_db);
            for s in body { scan_stmt_features(s, has_regex, has_db); }
        }
        Expr::Do { body, .. } => {
            for s in body { scan_stmt_features(s, has_regex, has_db); }
        }
        // StructLit(String, Vec<(String, Expr)>, Span)
        Expr::StructLit(_, fields, _) => {
            for (_, e) in fields { scan_expr_features(e, has_regex, has_db); }
        }
        // ArrayLit(Vec<Expr>, Span) | TupleLit(Vec<Expr>, Span)
        Expr::ArrayLit(items, _) | Expr::TupleLit(items, _) => {
            for i in items { scan_expr_features(i, has_regex, has_db); }
        }
        Expr::Closure { body, .. } => {
            for s in body { scan_stmt_features(s, has_regex, has_db); }
        }
        Expr::Unsafe(stmts, _, _) => {
            for s in stmts { scan_stmt_features(s, has_regex, has_db); }
        }
        _ => {}
    }
}

/// Type-predicate helpers for the Python trampoline marshaling (above).
fn is_string_type(ty: &TypeExpr) -> bool {
    matches!(ty, TypeExpr::String) || matches!(ty, TypeExpr::Named(n) if n == "string")
}
fn is_float_type(ty: &TypeExpr) -> bool {
    matches!(ty, TypeExpr::F32 | TypeExpr::F64)
    || matches!(ty, TypeExpr::Named(n) if n == "f32" || n == "f64")
}
fn is_bool_type(ty: &TypeExpr) -> bool {
    matches!(ty, TypeExpr::Bool) || matches!(ty, TypeExpr::Named(n) if n == "bool")
}

/// Free-function version of `FnCx::unwrap_call`, usable from
/// `LlvmCodegen::compile_python_trampoline` (which has no `FnCx`).
fn unwrap_call<'ctx>(ctx: &'ctx Context, r: inkwell::values::CallSiteValue<'ctx>) -> BasicValueEnum<'ctx> {
    use inkwell::values::AnyValue;
    match r.as_any_value_enum() {
        inkwell::values::AnyValueEnum::IntValue(v)     => v.into(),
        inkwell::values::AnyValueEnum::FloatValue(v)   => v.into(),
        inkwell::values::AnyValueEnum::PointerValue(v) => v.into(),
        inkwell::values::AnyValueEnum::StructValue(v)  => v.into(),
        inkwell::values::AnyValueEnum::ArrayValue(v)   => v.into(),
        inkwell::values::AnyValueEnum::VectorValue(v)  => v.into(),
        _                                               => ctx.i64_type().const_zero().into(),
    }
}

// ── Per-function compile context ──────────────────────────────────────────

use inkwell::types::BasicMetadataTypeEnum;

/// Convert a BasicMetadataTypeEnum (function signature param type) back into
/// a BasicTypeEnum (value type hint). MetadataType has no Basic equivalent.
fn metadata_to_basic<'ctx>(t: BasicMetadataTypeEnum<'ctx>) -> Option<BasicTypeEnum<'ctx>> {
    match t {
        BasicMetadataTypeEnum::ArrayType(a)   => Some(a.into()),
        BasicMetadataTypeEnum::FloatType(f)   => Some(f.into()),
        BasicMetadataTypeEnum::IntType(i)     => Some(i.into()),
        BasicMetadataTypeEnum::PointerType(p) => Some(p.into()),
        BasicMetadataTypeEnum::StructType(s)  => Some(s.into()),
        BasicMetadataTypeEnum::VectorType(v)  => Some(v.into()),
        _ => None,
    }
}

struct FnCx<'ctx, 'a> {
    ctx:         &'ctx Context,
    module:      &'a Module<'ctx>,
    builder:     &'a Builder<'ctx>,
    builtins:    &'a LlvmBuiltins<'ctx>,
    func_vals:   &'a HashMap<String, FunctionValue<'ctx>>,
    str_globals: &'a mut HashMap<String, PointerValue<'ctx>>,
    vars:        HashMap<String, (PointerValue<'ctx>, BasicTypeEnum<'ctx>)>,
    fn_name:     String,
    ret_type:    Option<TypeExpr>,
    /// H# struct definitions (name -> ordered field list), collected once
    /// from the module's `Item::StructDef` items in `build_module`, so
    /// struct-literal / field-access codegen can resolve field indices.
    structs:     &'a HashMap<String, Vec<StructField>>,
    /// Best-effort map of local variable/parameter name -> resolved struct
    /// type name, for the (common) case where the type is statically known
    /// from a parameter annotation, a `let x: Foo = ...` annotation, or a
    /// direct `Foo { ... }` struct literal. Used by `FieldAccess` codegen to
    /// pick the *correct* struct's field layout instead of guessing by
    /// scanning every struct for a field with a matching name (see
    /// `infer_struct_name` / the FieldAccess arm in `expr()`).
    var_types:   HashMap<String, String>,
    /// Companion to `var_types`, but for the *element* type of an
    /// array-typed variable/parameter (`[Foo]`) rather than the
    /// variable's own type — e.g. `entries: [HackerEntry]` records
    /// `"entries" -> "HackerEntry"` here. Lets `infer_struct_name`
    /// resolve `entries[i].key` correctly (via `infer_array_elem_type`)
    /// instead of falling back to the scan-every-struct-for-a-matching-
    /// field-name guess.
    array_elem_types: HashMap<String, String>,
    /// Broader companion to `array_elem_types`: the actual LLVM
    /// representation type of an array's elements (`ptr` for strings/
    /// bytes/arrays/structs, `i64`/`f64`/etc for numerics), used by
    /// `for_stmt`'s array-iteration loop to know how to unbox each
    /// `hsh_array_get` result — critically, whether it needs an
    /// `inttoptr` (pointer-shaped element) or can be used as-is
    /// (numeric element, already stored as a raw i64 slot).
    array_elem_llvm_ty: HashMap<String, BasicTypeEnum<'ctx>>,
    /// Full-fidelity companion to `array_elem_llvm_ty`: the element's
    /// declared `TypeExpr` rather than its flattened LLVM form. Needed to
    /// handle *nested* arrays (`[[string]]`, i.e. `cmds[i][0]`) — resolving
    /// the outer `cmds[i]` needs to know its element type is itself
    /// `[string]` (another array, to recurse into for the `[0]`), which a
    /// bare `BasicTypeEnum` (just "this is a pointer") can't express; only
    /// the source-level type can.
    array_elem_type_expr: HashMap<String, TypeExpr>,
    /// This function's `@arena`/`@safety`/`@arc`/`@pointers`/`@default`
    /// annotation. `Arena` and `Arc` change codegen behavior (see
    /// `compile_fn`'s prologue and `build_return_coerced`'s epilogue);
    /// `Safety` runs `check_moves_basic` instead; `Pointers` is enforced
    /// by the typechecker (see `typechecker.rs`'s mem-mode gate) rather
    /// than codegen itself.
    mem_mode:    MemoryMode,
    /// `@arc` basic v2 bookkeeping: names of local variables (in
    /// `self.vars`) that currently hold a reference-counted pointer this
    /// function is responsible for releasing — either because they were
    /// bound straight from `arc_alloc(...)`, or because they were bound
    /// from another already-tracked arc local (`let y = x`), in which
    /// case an automatic `arc_retain` was inserted at that point (see the
    /// `Stmt::Let` arm of `stmt()`). Every name still in here at each
    /// return path gets an automatic `arc_release` in
    /// `emit_arc_epilogue`, *except* the one (if any) being returned —
    /// same "don't release what you're handing back to the caller"
    /// rule as the arena epilogue. This is a straight-line, name-based
    /// heuristic (like `check_moves_basic`): it does not model
    /// conditional branches, so a local only assigned inside one arm of
    /// an `if` is still tracked (and released) as if it always exists —
    /// harmless for the release-only-if-present logic below since
    /// release is skipped when the name was never actually bound this
    /// call, but real per-branch precision is future work, same caveat
    /// as `@safety`.
    arc_owned:   std::cell::RefCell<Vec<String>>,
    /// Counts how many nested `if`/`while`/`for`/`match`-arm/`do`/`unsafe`
    /// bodies we're currently compiling inside of (0 = the function's own
    /// flat top-level statement list). `Stmt::Let`'s `@arc` tracking (see
    /// `arc_owned`) only fires at depth 0: `self.vars` itself has no real
    /// per-branch scoping in this codegen (a `let` inside one `if` branch
    /// stays visible afterward at the Rust level, same simplification
    /// `check_moves_basic` already documents), so a name added to
    /// `arc_owned` from inside a branch that *isn't* the one actually
    /// taken at runtime would point at an uninitialized alloca —
    /// `emit_arc_epilogue` would then call `hsh_rc_release` on garbage,
    /// which (unlike a leak) can crash or corrupt the heap. Restricting
    /// to depth 0 trades "can't auto-manage an `arc_alloc` declared
    /// inside a branch/arm yet" (still requires a manual `arc_release`
    /// there) for "never releases a pointer that was never allocated".
    branch_depth: std::cell::Cell<u32>,
    /// Stack of enclosing loops' `(continue_target, break_target)` basic
    /// blocks — pushed on entering a `while`/`for` loop's body, popped on
    /// leaving it. `Stmt::Continue`/`Stmt::Break` consult
    /// `.last()` to know which block to actually branch to.
    ///
    /// BUG FIX: before this existed, `Stmt::Break`/`Stmt::Continue` had no
    /// way to know *which* loop (if any) they were inside, so they always
    /// emitted a bare `unreachable` instruction — telling LLVM this code
    /// path can never execute at runtime. That's true for a `break`/
    /// `continue` genuinely outside any loop (a real program never has
    /// one; the typechecker rejects it), but `continue`/`break` *inside* a
    /// real, running loop are the opposite of unreachable — they're
    /// executed constantly, by design. Marking reachable code as
    /// `unreachable` is a direct request for undefined behavior: the
    /// optimizer is free to assume execution never reaches there and
    /// delete/misorder surrounding code on that assumption, which is
    /// exactly what produced hard-to-explain segfaults in any nontrivial
    /// loop containing an early `continue` followed by more loop-body
    /// code (`bytes_final`'s own `config::parse`, which has exactly that
    /// shape, crashed from this). `while_stmt`/`for_stmt` now push their
    /// real continue/break targets here before compiling their body, so
    /// `break`/`continue` branch to the correct block like every other
    /// working compiler's loop lowering.
    loop_stack: Vec<(inkwell::basic_block::BasicBlock<'ctx>, inkwell::basic_block::BasicBlock<'ctx>)>,
}

impl<'ctx, 'a> FnCx<'ctx, 'a> {
    // ── `@arc` branch-depth bookkeeping (see `branch_depth`'s doc comment) ────
    fn enter_branch(&self) { self.branch_depth.set(self.branch_depth.get() + 1); }
    fn exit_branch(&self)  { self.branch_depth.set(self.branch_depth.get().saturating_sub(1)); }

    // ── Struct field resolution ───────────────────────────────────────────────
    // H# structs store fields as ordered HshArray slots.
    // We look up the StructDef in self.structs (populated once per module in
    // `LlvmCodegen::build_module`, then threaded into every FnCx)
    // and return the 0-based field index for the named field.

    fn get_struct_field_count(&self, struct_name: &str) -> usize {
        // Strip module qualifier if present (e.g. "helpers::Colors" -> "Colors")
        let bare = struct_name.rsplit("::").next().unwrap_or(struct_name);
        if let Some(fields) = self.structs.get(bare).or_else(|| self.structs.get(struct_name)) {
            return fields.len();
        }
        // Unknown struct — safe default
        8
    }

    fn resolve_struct_field_index(&self, struct_name: &str, field: &str) -> usize {
        let bare = struct_name.rsplit("::").next().unwrap_or(struct_name);
        if let Some(fields) = self.structs.get(bare).or_else(|| self.structs.get(struct_name)) {
            for (i, f) in fields.iter().enumerate() {
                if f.name == field { return i; }
            }
        }
        0
    }

    /// Best-effort: figure out the concrete struct type of `e`, so field
    /// access can look up the right struct's layout instead of scanning
    /// every struct definition for a same-named field (which silently picks
    /// the wrong one when two structs share a field name at different
    /// indices). Returns `None` when we genuinely can't tell statically —
    /// callers fall back to the old any-struct scan in that case, but should
    /// surface a compile-time warning when they do, since that fallback can
    /// be wrong.
    fn infer_struct_name(&self, e: &Expr) -> Option<String> {
        match e {
            Expr::StructLit(name, _, _) => Some(name.clone()),
            Expr::Ident(name, _) => self.var_types.get(name).cloned(),
            Expr::FieldAccess(inner, field, _) => {
                // Chained access (`a.b.c`): resolve `a`'s struct, find `b`'s
                // declared field type, and — if that type itself names a
                // known struct — recurse one level.
                let inner_struct = self.infer_struct_name(inner)?;
                let bare = inner_struct.rsplit("::").next().unwrap_or(&inner_struct);
                let fields = self.structs.get(bare).or_else(|| self.structs.get(&inner_struct))?;
                let field_def = fields.iter().find(|f| &f.name == field)?;
                match &field_def.ty {
                    TypeExpr::Named(n) if self.structs.contains_key(n) => Some(n.clone()),
                    _ => None,
                }
            }
            // `arr[i].field` — resolve `arr`'s *element* type (not `arr`'s
            // own type, which would be the array itself) via
            // `infer_array_elem_type`. Previously `IndexAccess` wasn't
            // handled here at all, so every `arr[i].field` access — no
            // matter how clearly `arr` was annotated — fell through to
            // the guess-by-scanning-every-struct fallback.
            Expr::IndexAccess(arr, _, _) => self.infer_array_elem_type(arr),
            _ => None,
        }
    }

    /// Resolves the element struct type of an array-valued expression —
    /// the counterpart to `infer_struct_name`, used specifically for the
    /// `arr[i]` case. Handles a bare variable (`array_elem_types` lookup)
    /// and one level of field chaining (`obj.arr_field[i]`, by resolving
    /// `obj`'s struct and checking if `arr_field`'s declared type is
    /// `[Foo]`).
    fn infer_array_elem_type(&self, e: &Expr) -> Option<String> {
        match e {
            Expr::Ident(name, _) => self.array_elem_types.get(name).cloned(),
            Expr::FieldAccess(inner, field, _) => {
                let inner_struct = self.infer_struct_name(inner)?;
                let bare = inner_struct.rsplit("::").next().unwrap_or(&inner_struct);
                let fields = self.structs.get(bare).or_else(|| self.structs.get(&inner_struct))?;
                let field_def = fields.iter().find(|f| &f.name == field)?;
                match &field_def.ty {
                    TypeExpr::Array(elem) => match elem.as_ref() {
                        TypeExpr::Named(n) if self.structs.contains_key(n) => Some(n.clone()),
                        _ => None,
                    },
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Resolves the `TypeExpr` of what indexing `e` produces (i.e. `e`'s
    /// *element* type — `e` itself must be an array-valued expression).
    /// Unlike `infer_array_elem_type` (struct names only, for
    /// `infer_struct_name`'s benefit) this handles *any* element type, and
    /// — critically — recurses through `IndexAccess` so nested arrays
    /// (`cmds: [[string]]`, i.e. `cmds[i][0]`) resolve correctly: the
    /// outer `[0]` needs to know `cmds[i]`'s type is `[string]`, which
    /// means first resolving what indexing `cmds` produces one level down.
    fn infer_elem_type_expr(&self, e: &Expr) -> Option<TypeExpr> {
        match e {
            Expr::Ident(name, _) => self.array_elem_type_expr.get(name).cloned(),
            Expr::FieldAccess(inner, field, _) => {
                let inner_struct = self.infer_struct_name(inner)?;
                let bare = inner_struct.rsplit("::").next().unwrap_or(&inner_struct);
                let fields = self.structs.get(bare).or_else(|| self.structs.get(&inner_struct))?;
                let field_def = fields.iter().find(|f| &f.name == field)?;
                match &field_def.ty {
                    TypeExpr::Array(elem) => Some(elem.as_ref().clone()),
                    _ => None,
                }
            }
            Expr::IndexAccess(inner, _, _) => {
                // `e` = `inner[idx]`; its own element type is one level
                // deeper than `inner`'s element type, so first find what
                // indexing `inner` produces, then check whether *that* is
                // itself an array.
                match self.infer_elem_type_expr(inner)? {
                    TypeExpr::Array(elem) => Some(elem.as_ref().clone()),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// General counterpart to `infer_array_elem_type`: resolves the
    /// *LLVM* type of an array-valued expression's elements, for *any*
    /// element type (not just structs), including through nested arrays
    /// and struct fields — see `infer_elem_type_expr`, which does the
    /// actual resolution; this just converts the result to its LLVM form.
    /// Used to un-box `hsh_array_get`'s generic `i64` slot back to the
    /// real element type — see the `IndexAccess` fix in `expr()`, which
    /// needs this for shapes like `t.entries[i]` (a struct field) and
    /// `cmds[i][0]` (a nested array) that a bare `array_elem_llvm_ty`
    /// variable lookup alone can't resolve.
    fn infer_array_elem_llvm_ty(&self, e: &Expr) -> Option<BasicTypeEnum<'ctx>> {
        self.infer_elem_type_expr(e).and_then(|t| htype_to_llvm(self.ctx, &t))
    }

    // ── Match lowering ────────────────────────────────────────────────────────
    // Compiles `match subject is pat => body ... end` into an if-else chain.

    fn compile_match(
        &mut self,
        subject: &Expr,
        arms:    &[MatchArm],
        hint:    Option<BasicTypeEnum<'ctx>>,
    ) -> R<BasicValueEnum<'ctx>> {
        let subj_val = self.expr(subject, None)?;
        let i64t     = self.ctx.i64_type();
        let func     = self.builder.get_insert_block().unwrap().get_parent().unwrap();
        let merge_bb = self.ctx.append_basic_block(func, "match_merge");
        let mut phi_incoming: Vec<(BasicValueEnum<'ctx>, inkwell::basic_block::BasicBlock<'ctx>)> = Vec::new();
        // Value-join machinery (`join_branch_values`/`compile_branch_value`)
        // is shared with `compile_if_expr` — see that pair's doc comments
        // for why: this exact "did every arm/branch actually get a real
        // value onto the phi, and does merge_bb end up with a real
        // terminator either way" logic was independently duplicated (and
        // independently buggy) between `if`-as-expression and
        // `match`-as-expression before being pulled out here.
        let result_ty: BasicTypeEnum<'ctx> = hint.unwrap_or_else(|| i64t.into());

        for (arm_idx, arm) in arms.iter().enumerate() {
            let then_bb = self.ctx.append_basic_block(func, &format!("match_arm{}", arm_idx));
            // Every arm gets a real else_bb — including the last one. It
            // used to be aliased straight to `merge_bb` for the last arm,
            // which meant the "this arm's pattern didn't match either"
            // edge landed on `merge_bb` without ever registering a
            // `phi_incoming` entry for it: exactly the missing-predecessor
            // case the LLVM verifier was rejecting on *every* match
            // expression in the program.
            let else_bb = self.ctx.append_basic_block(func, &format!("match_else{}", arm_idx));

            let cond = self.compile_pattern_cond(&subj_val, &arm.pattern, subject)?;
            self.builder.build_conditional_branch(cond.into_int_value(), then_bb, else_bb).unwrap();

            self.builder.position_at_end(then_bb);
            // Bind pattern variables into scope for the arm body (and for the
            // guard expression below, which may reference them).
            self.bind_pattern_vars(&subj_val, &arm.pattern);

            // `if pattern => body` guards were parsed into `arm.guard` but
            // silently never consulted here — a guard that evaluated false
            // would still take the arm. Evaluate it now that bindings exist,
            // and fall through to `else_bb` (i.e. try the next arm) if it's
            // false, exactly like a real guard should.
            if let Some(guard_expr) = &arm.guard {
                let guard_val = self.expr(guard_expr, None)?.into_int_value();
                let guard_body_bb = self.ctx.append_basic_block(func, &format!("match_guard_body{}", arm_idx));
                self.builder.build_conditional_branch(guard_val, guard_body_bb, else_bb).unwrap();
                self.builder.position_at_end(guard_body_bb);
            }

            self.compile_branch_value(&arm.body, result_ty, merge_bb, &mut phi_incoming)?;

            self.builder.position_at_end(else_bb);
        }

        // Reached only if no arm's pattern matched at all (the H#
        // typechecker doesn't currently verify match exhaustiveness, so
        // this path is very much reachable IR, not dead code). Give it its
        // own phi entry instead of silently aliasing this block to
        // `merge_bb`.
        let fallthrough_bb = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(merge_bb).unwrap();
        phi_incoming.push((self.zero(result_ty), fallthrough_bb));

        Ok(self.join_branch_values(merge_bb, result_ty, &phi_incoming))
    }

    /// Build (or reuse a cached) global string constant, returning a pointer
    /// to it. Shares the same cache as `literal()`'s `Literal::String` case
    /// so repeated identical string patterns/tags don't emit duplicate
    /// globals.
    fn build_string_constant(&mut self, s: &str) -> PointerValue<'ctx> {
        if let Some(&g) = self.str_globals.get(s) {
            return g;
        }
        let p = self.builder.build_global_string_ptr(s, ".str").unwrap().as_pointer_value();
        self.str_globals.insert(s.to_string(), p);
        p
    }

    /// Coerce a single value to an exact target type: int<->pointer via
    /// inttoptr/ptrtoint (this runtime bit-reinterprets pointers as `i64`
    /// in several places — struct fields and array elements are stored as
    /// generic `i64` slots regardless of whether they actually hold a
    /// number or a nested string/array/struct pointer), and int<->int
    /// width mismatches via sign-extend/truncate. Anything else (already
    /// matching, or a combination we don't specifically handle) passes
    /// through unchanged.
    fn coerce_basic_value(&mut self, v: BasicValueEnum<'ctx>, target: BasicTypeEnum<'ctx>) -> BasicValueEnum<'ctx> {
        match (v, target) {
            (BasicValueEnum::IntValue(iv), BasicTypeEnum::PointerType(pt)) => {
                self.builder.build_int_to_ptr(iv, pt, "i2p").unwrap().into()
            }
            (BasicValueEnum::PointerValue(pv), BasicTypeEnum::IntType(it)) => {
                self.builder.build_ptr_to_int(pv, it, "p2i").unwrap().into()
            }
            (BasicValueEnum::IntValue(iv), BasicTypeEnum::IntType(it)) if iv.get_type() != it => {
                if iv.get_type().get_bit_width() < it.get_bit_width() {
                    self.builder.build_int_s_extend(iv, it, "sext").unwrap().into()
                } else {
                    self.builder.build_int_truncate(iv, it, "trunc").unwrap().into()
                }
            }
            _ => v,
        }
    }

    /// Build a call, first coercing every argument to the *callee's own
    /// declared parameter type* (queried straight from `f`, so this can
    /// never drift out of sync with how the function was actually
    /// declared in `builtins.rs`/codegen). This is the fix for the whole
    /// class of "Call parameter type does not match function signature!"
    /// LLVM verifier errors: values pulled out of a generic `i64` slot
    /// (a struct field, an array element — this runtime boxes both as
    /// plain `i64`, converting to/from a real pointer only where needed)
    /// were being passed straight into calls expecting a genuine `ptr`,
    /// and vice versa. Every call in codegen should go through this
    /// instead of `self.builder.build_call` directly.
    fn call_coerced(
        &mut self,
        f: FunctionValue<'ctx>,
        args: &[BasicValueEnum<'ctx>],
        name: &str,
    ) -> inkwell::values::CallSiteValue<'ctx> {
        let param_types = f.get_type().get_param_types();
        let mut coerced: Vec<inkwell::values::BasicMetadataValueEnum<'ctx>> = Vec::with_capacity(args.len());
        for (i, a) in args.iter().enumerate() {
            match param_types.get(i).and_then(|pt| metadata_to_basic(*pt)) {
                Some(target) => coerced.push(self.coerce_basic_value(*a, target).into()),
                None => coerced.push((*a).into()),
            }
        }
        self.builder.build_call(f, &coerced, name).unwrap()
    }

    /// Normalize any compiled value down to an `i64` for passing to runtime
    /// helpers that take a "generic value" bit pattern (like
    /// `hsh_val_to_str`, which sniffs whether the i64 it received is
    /// actually a pointer). Passing a `PointerValue` directly where the
    /// declared LLVM parameter type is `i64` is a real type mismatch that
    /// can corrupt the generated IR — this makes sure that never happens.
    fn value_to_i64_bits(&mut self, v: BasicValueEnum<'ctx>) -> inkwell::values::IntValue<'ctx> {
        match v {
            BasicValueEnum::IntValue(iv) => iv,
            BasicValueEnum::PointerValue(pv) =>
                self.builder.build_ptr_to_int(pv, self.ctx.i64_type(), "p2i").unwrap(),
            BasicValueEnum::FloatValue(fv) =>
                self.builder.build_bit_cast(fv, self.ctx.i64_type(), "f2i").unwrap().into_int_value(),
            _ => self.ctx.i64_type().const_zero(),
        }
    }

    fn compile_pattern_cond(
        &mut self,
        subj: &BasicValueEnum<'ctx>,
        pat:  &Pattern,
        orig: &Expr,
    ) -> R<BasicValueEnum<'ctx>> {
        use inkwell::IntPredicate;
        use inkwell::values::BasicValue;
        let i1t  = self.ctx.bool_type();
        let i32t = self.ctx.i32_type();
        let ptr  = self.ctx.ptr_type(inkwell::AddressSpace::default());

        let strcmp_fn = self.module.get_function("strcmp").unwrap_or_else(|| {
            self.module.add_function("strcmp", i32t.fn_type(&[ptr.into(), ptr.into()], false), None)
        });

        match pat {
            Pattern::Wildcard(_) | Pattern::Ident(_, _) => {
                Ok(i1t.const_int(1, false).into())
            }
            Pattern::Literal(lit, _) => {
                match lit {
                    Literal::String(s) => {
                        let pat_str = self.build_string_constant(s);
                        let cmp = self.call_coerced(strcmp_fn, &[(*subj).into(), pat_str.into()], "sc");
                        let ci  = self.unwrap_call(cmp).into_int_value();
                        let z   = i32t.const_zero();
                        let eq  = self.builder.build_int_compare(IntPredicate::EQ, ci, z, "seq").unwrap();
                        Ok(eq.into())
                    }
                    Literal::Int(n) => {
                        let pv = self.ctx.i64_type().const_int(*n as u64, true);
                        let sv = subj.into_int_value();
                        let eq = self.builder.build_int_compare(IntPredicate::EQ, sv, pv, "ieq").unwrap();
                        Ok(eq.into())
                    }
                    Literal::Bool(b) => {
                        let pv = self.ctx.i64_type().const_int(*b as u64, false);
                        let sv = subj.into_int_value();
                        let eq = self.builder.build_int_compare(IntPredicate::EQ, sv, pv, "beq").unwrap();
                        Ok(eq.into())
                    }
                    Literal::Float(f) => {
                        let pv = self.ctx.f64_type().const_float(*f);
                        let sv = subj.into_float_value();
                        let eq = self.builder.build_float_compare(inkwell::FloatPredicate::OEQ, sv, pv, "feq").unwrap();
                        Ok(eq.into())
                    }
                    Literal::Nil => {
                        let sv = subj.into_pointer_value();
                        let is_null = self.builder.build_is_null(sv, "nileq").unwrap();
                        Ok(is_null.into())
                    }
                    other => Err(CodegenError::Llvm(format!(
                        "unsupported literal pattern in match arm: {:?} — only int/float/bool/string/nil literal patterns are implemented",
                        other
                    )))
                }
            }
            Pattern::Enum { variant, inner, .. } => {
                if !inner.is_empty() {
                    // Enum payload extraction needs a runtime representation
                    // for "tag + fields", which the current tag-as-string
                    // encoding doesn't have. Matching bare tags (`Variant`)
                    // still works below; only `Variant(x, y)`-style
                    // destructuring is unimplemented. Fail the build instead
                    // of silently treating the whole pattern as "always
                    // matches" (which is what happened before this fix).
                    return Err(CodegenError::Llvm(format!(
                        "match arm: enum pattern `{}(...)` with payload destructuring is not supported by the codegen yet — only bare tag matching (`{}`) is implemented",
                        variant, variant
                    )));
                }
                // Enum variants lower to string tag comparison
                let tag = self.build_string_constant(variant);
                let cmp = self.call_coerced(strcmp_fn, &[(*subj).into(), tag.into()], "ec");
                let ci  = self.unwrap_call(cmp).into_int_value();
                let z   = i32t.const_zero();
                let eq  = self.builder.build_int_compare(IntPredicate::EQ, ci, z, "eeq").unwrap();
                Ok(eq.into())
            }
            Pattern::Or(pats, _) => {
                // Any pattern matches — chain with OR
                let mut result = i1t.const_int(0, false).as_basic_value_enum();
                for p in pats {
                    let cond = self.compile_pattern_cond(subj, p, orig)?;
                    let lhs  = result.into_int_value();
                    let rhs  = cond.into_int_value();
                    let r8   = self.builder.build_or(lhs, rhs, "por").unwrap();
                    result   = r8.into();
                }
                Ok(result)
            }
            Pattern::Tuple(sub_pats, _) => {
                // TupleLit is compiled the same way as ArrayLit (via
                // hsh_array_new/hsh_array_push), so destructure the same way:
                // index in with hsh_array_get and recurse per element,
                // AND-ing all the per-element conditions together.
                let mut acc: Option<inkwell::values::IntValue> = None;
                for (i, sp) in sub_pats.iter().enumerate() {
                    let idx  = self.ctx.i64_type().const_int(i as u64, false);
                    let call = self.call_coerced(self.builtins.hsh_array_get, &[(*subj).into(), idx.into()], "tup_get");
                    let elem = self.unwrap_call(call);
                    let cond = self.compile_pattern_cond(&elem, sp, orig)?.into_int_value();
                    acc = Some(match acc {
                        None      => cond,
                        Some(acc) => self.builder.build_and(acc, cond, "tand").unwrap(),
                    });
                }
                Ok(acc.unwrap_or_else(|| i1t.const_int(1, false)).into())
            }
            Pattern::Struct { name, fields, .. } => {
                // Same idea as Tuple, but indices come from the struct's
                // field layout (`self.structs`) rather than position.
                let mut acc: Option<inkwell::values::IntValue> = None;
                for (field_name, sub_pat) in fields {
                    let idx   = self.resolve_struct_field_index(name, field_name);
                    let idx_v = self.ctx.i64_type().const_int(idx as u64, false);
                    let call  = self.call_coerced(self.builtins.hsh_struct_get, &[(*subj).into(), idx_v.into()], "sp_get");
                    let elem  = self.unwrap_call(call);
                    let cond  = self.compile_pattern_cond(&elem, sub_pat, orig)?.into_int_value();
                    acc = Some(match acc {
                        None      => cond,
                        Some(acc) => self.builder.build_and(acc, cond, "sand").unwrap(),
                    });
                }
                Ok(acc.unwrap_or_else(|| i1t.const_int(1, false)).into())
            }
            Pattern::Range(lo, hi, inclusive, span) => {
                // Only integer literal bounds are meaningful here.
                let lo_v = Self::pattern_literal_int(lo).ok_or_else(|| CodegenError::Llvm(
                    format!("range pattern at {}: lower bound must be an integer literal", span)))?;
                let hi_v = Self::pattern_literal_int(hi).ok_or_else(|| CodegenError::Llvm(
                    format!("range pattern at {}: upper bound must be an integer literal", span)))?;
                let sv    = subj.into_int_value();
                let lo_c  = self.ctx.i64_type().const_int(lo_v as u64, true);
                let hi_c  = self.ctx.i64_type().const_int(hi_v as u64, true);
                let ge    = self.builder.build_int_compare(IntPredicate::SGE, sv, lo_c, "rge").unwrap();
                let hi_pred = if *inclusive { IntPredicate::SLE } else { IntPredicate::SLT };
                let le    = self.builder.build_int_compare(hi_pred, sv, hi_c, "rle").unwrap();
                let and   = self.builder.build_and(ge, le, "rand").unwrap();
                Ok(and.into())
            }
        }
    }

    /// Extract an `i64` out of a `Pattern::Literal(Literal::Int(_))`, used by
    /// range-pattern bounds (`1..10 => ...`). Returns `None` for anything
    /// else so the caller can report a proper error instead of guessing.
    fn pattern_literal_int(p: &Pattern) -> Option<i64> {
        match p {
            Pattern::Literal(Literal::Int(n), _) => Some(*n),
            _ => None,
        }
    }

    fn bind_pattern_vars(&mut self, subj: &BasicValueEnum<'ctx>, pat: &Pattern) {
        match pat {
            // Bind Ident patterns (like `x` in `match val is x => ...`)
            // as local variable pointing to the subject value.
            Pattern::Ident(name, _) => {
                if name != "_" {
                    let ty = subj.get_type();
                    let ptr = self.builder.build_alloca(ty, name).unwrap();
                    self.builder.build_store(ptr, *subj).unwrap();
                    self.vars.insert(name.clone(), (ptr, ty));
                }
            }
            // Recurse into tuple elements (same runtime layout as arrays —
            // see the matching Pattern::Tuple arm in compile_pattern_cond).
            Pattern::Tuple(sub_pats, _) => {
                for (i, sp) in sub_pats.iter().enumerate() {
                    let idx  = self.ctx.i64_type().const_int(i as u64, false);
                    let call = self.call_coerced(self.builtins.hsh_array_get, &[(*subj).into(), idx.into()], "tup_bind");
                    let elem = self.unwrap_call(call);
                    self.bind_pattern_vars(&elem, sp);
                }
            }
            // Recurse into struct fields.
            Pattern::Struct { name, fields, .. } => {
                for (field_name, sub_pat) in fields {
                    let idx   = self.resolve_struct_field_index(name, field_name);
                    let idx_v = self.ctx.i64_type().const_int(idx as u64, false);
                    let call  = self.call_coerced(self.builtins.hsh_struct_get, &[(*subj).into(), idx_v.into()], "sp_bind");
                    let elem  = self.unwrap_call(call);
                    self.bind_pattern_vars(&elem, sub_pat);
                }
            }
            // Wildcard/Literal/Range/Enum(bare tag) introduce no bindings.
            // Pattern::Or intentionally isn't handled here: its alternatives
            // may bind different names, and we have no way at this point to
            // know which alternative actually matched at runtime — binding
            // for e.g. the first alternative would silently give wrong
            // values if a *different* alternative was the one that matched.
            // (Requiring identical bindings across `Or` arms, like Rust does,
            // is a typechecker-level check that isn't implemented yet.)
            _ => {}
        }
    }

    fn expr_is_string(&self, e: &Expr) -> bool {
        matches!(e, Expr::Literal(Literal::String(_), _))
    }
    fn unwrap_call(&self, r: inkwell::values::CallSiteValue<'ctx>) -> BasicValueEnum<'ctx> {
        use inkwell::values::AnyValue;
        match r.as_any_value_enum() {
            inkwell::values::AnyValueEnum::IntValue(v)     => v.into(),
            inkwell::values::AnyValueEnum::FloatValue(v)   => v.into(),
            inkwell::values::AnyValueEnum::PointerValue(v) => v.into(),
            inkwell::values::AnyValueEnum::StructValue(v)  => v.into(),
            inkwell::values::AnyValueEnum::ArrayValue(v)   => v.into(),
            inkwell::values::AnyValueEnum::VectorValue(v)  => v.into(),
            _                                               => self.ctx.i64_type().const_zero().into(),
        }
    }

    fn stmts(&mut self, stmts: &[Stmt]) -> R<bool> {
        for stmt in stmts {
            if self.stmt(stmt)? { return Ok(true); }
        }
        Ok(false)
    }

    fn stmt(&mut self, s: &Stmt) -> R<bool> {
        match s {
            Stmt::Let { name, ty, value, .. } => {
                let annotated_ty = ty.as_ref().and_then(|t| htype_to_llvm(self.ctx, t));
                let (ptr, llvm_ty) = if let Some(e) = value {
                    let v = self.expr(e, annotated_ty)?;
                    // Prefer the explicit annotation when present (it's
                    // authoritative — e.g. picks a specific int width or a
                    // struct type a bare value might not carry). Otherwise
                    // use the *actual* type of the computed value — this is
                    // the fix: unannotated `let x = some_string_expr()`
                    // used to always allocate an `i64` slot regardless of
                    // what `some_string_expr()` actually returned, so
                    // string/struct/array values got silently stored into
                    // (and later loaded back out of, see `Expr::Ident`) an
                    // `i64`-typed slot — which produces exactly-wrong LLVM
                    // types at every subsequent use of that variable.
                    let vty = annotated_ty.unwrap_or_else(|| v.get_type());
                    let p = self.builder.build_alloca(vty, name).unwrap();
                    self.builder.build_store(p, v).unwrap();
                    (p, vty)
                } else {
                    let vty = annotated_ty.unwrap_or_else(|| self.ctx.i64_type().into());
                    let p = self.builder.build_alloca(vty, name).unwrap();
                    let z = self.zero(vty);
                    self.builder.build_store(p, z).unwrap();
                    (p, vty)
                };
                self.vars.insert(name.clone(), (ptr, llvm_ty));

                // `@arc` basic v2: track locals holding a reference-counted
                // pointer so `emit_arc_epilogue` can auto-release them at
                // every return this function compiles. Two cases (both
                // name-based, like `check_moves_basic`'s move tracking — a
                // static heuristic, not a real alias/points-to analysis):
                //   - `let x = arc_alloc(n)`   — `x` now owns a fresh ref.
                //   - `let y = x` where `x` is already tracked — an alias;
                //     H# has no destructors to insert an implicit retain on
                //     assignment yet, so one is emitted right here instead,
                //     and `y` becomes an independent tracked owner too.
                // Only at `branch_depth == 0` — see its doc comment.
                if self.mem_mode == MemoryMode::Arc && self.branch_depth.get() == 0 {
                    let is_arc_alloc_call = if let Some(Expr::Call(callee, _, _)) = value {
                        matches!(callee.as_ref(), Expr::Ident(n, _) if n == "arc_alloc")
                    } else { false };
                    let aliased_owned = if let Some(Expr::Ident(src, _)) = value {
                        self.arc_owned.borrow().contains(src)
                    } else { false };
                    if is_arc_alloc_call {
                        self.arc_owned.borrow_mut().push(name.clone());
                    } else if aliased_owned {
                        let cur = self.builder.build_load(llvm_ty, ptr, "arc_alias").unwrap();
                        self.call_coerced(self.builtins.hsh_rc_retain, &[cur], "");
                        self.arc_owned.borrow_mut().push(name.clone());
                    }
                }
                // Remember the struct type of this binding, if we can tell —
                // either from an explicit `let x: Foo = ...` annotation, or
                // (if unannotated) from a direct `Foo { ... }` literal on the
                // right-hand side. Used later by FieldAccess to resolve
                // `x.field` against the *actual* struct instead of scanning
                // every struct definition for a same-named field.
                let inferred = match ty {
                    Some(TypeExpr::Named(n)) if self.structs.contains_key(n) => Some(n.clone()),
                    _ => value.as_ref().and_then(|e| self.infer_struct_name(e)),
                };
                match inferred {
                    Some(n) => { self.var_types.insert(name.clone(), n); }
                    None    => { self.var_types.remove(name); }
                }
                // Same idea, but for `let entries: [Foo] = ...` — records
                // the *element* type (both the struct name, for
                // FieldAccess resolution, and the LLVM representation
                // type, for `for_stmt`'s array-iteration unboxing) so
                // `entries[i].field` and `for e in entries is ... end`
                // both resolve correctly instead of guessing.
                let elem_ty: Option<&TypeExpr> = match ty {
                    Some(TypeExpr::Array(elem)) => Some(elem.as_ref()),
                    None => match value {
                        // Unannotated `let entries = [...]` — nothing to
                        // recover the *LLVM* element type from here
                        // (that needs a real TypeExpr, not a value), but
                        // the struct-name case can still fall back to the
                        // first literal element for FieldAccess purposes.
                        _ => None,
                    },
                    _ => None,
                };
                match elem_ty {
                    Some(TypeExpr::Named(n)) if self.structs.contains_key(n) => {
                        self.array_elem_types.insert(name.clone(), n.clone());
                    }
                    _ => {
                        if let Some(Expr::ArrayLit(items, _)) = value {
                            if let Some(n) = items.first().and_then(|first| self.infer_struct_name(first)) {
                                self.array_elem_types.insert(name.clone(), n);
                            } else {
                                self.array_elem_types.remove(name);
                            }
                        } else {
                            self.array_elem_types.remove(name);
                        }
                    }
                }
                match elem_ty.and_then(|t| htype_to_llvm(self.ctx, t)) {
                    Some(llvm_ty) => { self.array_elem_llvm_ty.insert(name.clone(), llvm_ty); }
                    None => { self.array_elem_llvm_ty.remove(name); }
                }
                match elem_ty {
                    Some(t) => { self.array_elem_type_expr.insert(name.clone(), t.clone()); }
                    None    => { self.array_elem_type_expr.remove(name); }
                }
                Ok(false)
            }
            Stmt::Return(e, _) => {
                self.build_return_coerced(e.as_ref())?;
                Ok(true)
            }
            Stmt::Expr(e, _) => {
                match e {
                    Expr::If { condition, then_body, elsif_branches, else_body, .. } =>
                    self.if_stmt(condition, then_body, elsif_branches, else_body),
                    Expr::While { condition, body, .. } =>
                    self.while_stmt(condition, body),
                    Expr::For { pattern, iterable, body, .. } =>
                    self.for_stmt(pattern, iterable, body),
                    Expr::Assign(lhs, rhs, _) => {
                        let target_ty = match lhs.as_ref() {
                            Expr::Ident(name, _) => self.vars.get(name.as_str()).map(|&(_, ty)| ty),
                            _ => None,
                        };
                        let v = self.expr(rhs, target_ty)?;
                        self.assign_lvalue(lhs, v)?;
                        Ok(false)
                    }
                    Expr::CompoundAssign(lhs, op, rhs, _) => {
                        // BUG FIX: same gap as plain `Assign` (see
                        // `assign_lvalue`'s doc comment) — this used to
                        // only handle a bare `Expr::Ident` on the left,
                        // silently doing nothing for `c.count += 1` or
                        // `arr[i] += 1`. Reads the current value through
                        // the same general path `expr()` already uses for
                        // any lvalue, then writes back through
                        // `assign_lvalue` — one read/modify/write instead
                        // of duplicating field/index resolution a third time.
                        let lv  = self.expr(lhs, None)?;
                        let rv  = self.expr(rhs, None)?;
                        let res = self.binop(op, lv, rv)?;
                        self.assign_lvalue(lhs, res)?;
                        Ok(false)
                    }
                    Expr::Return(val, _) => {
                        self.build_return_coerced(val.as_deref())?;
                        Ok(true)
                    }
                    // `exit(code)`/`panic(msg)` used as a bare statement:
                    // both end their own basic block with a real
                    // `unreachable` terminator right after the call (see
                    // call_fn's "exit"/"panic" arms) — exit() never
                    // returns by the C standard, and panic() calls
                    // hsh_panic which itself never returns either. But
                    // the catch-all arm below reports `Ok(false)` ("this
                    // statement didn't terminate the block") for *any*
                    // expression it doesn't specifically recognize, and
                    // every caller that receives `false` responds by
                    // appending its own fallthrough branch onto a block
                    // that already has a terminator instruction — a
                    // basic block with two terminators is malformed IR.
                    // Recognizing both here and reporting `Ok(true)`
                    // (matching how `Stmt::Break`/`Stmt::Continue` already
                    // report themselves as terminating, above) stops the
                    // second, spurious branch from ever being added.
                    //
                    // BUG FIX: this used to match on the identifier's
                    // *name* alone. `call_fn` (a few hundred lines down)
                    // deliberately checks `func_vals` — user-defined *and*
                    // `extern`-declared functions — before ever reaching
                    // its own hardcoded "exit"/"panic" arms, specifically
                    // so a user's own `fn exit(...)`/`fn panic(...)`
                    // shadows the built-in (see the comment there). Both
                    // example projects in this repo declare their own
                    // `extern dynamic [c] fn exit(code: int)` in
                    // helpers.h#/config.h# — which means every `exit(...)`
                    // call in them actually resolves through
                    // `call_user_fn`, a perfectly ordinary call that does
                    // *not* build an `unreachable` terminator. This arm
                    // was reporting `Ok(true)` regardless, lying about a
                    // terminator that was never actually emitted — exactly
                    // the "does not have terminator" failures on `then`/
                    // `match_arm*` blocks ending in `exit(1)` throughout
                    // `hacker_hsharp`/`bytes_final`. Only trust the
                    // built-in's guaranteed `unreachable` when nothing in
                    // `func_vals` shadows the name — i.e. mirror call_fn's
                    // own precedence exactly, instead of duplicating (and
                    // silently disagreeing with) it.
                    Expr::Call(callee, _, _)
                        if matches!(callee.as_ref(), Expr::Ident(n, _)
                            if (n == "exit" || n == "panic") && !self.func_vals.contains_key(n.as_str())) =>
                    {
                        self.expr(e, None)?;
                        Ok(true)
                    }
                    _ => { self.expr(e, None)?; Ok(false) }
                }
            }
            Stmt::Continue(_) => {
                match self.loop_stack.last() {
                    Some(&(continue_target, _)) => {
                        self.builder.build_unconditional_branch(continue_target).unwrap();
                    }
                    None => {
                        // No enclosing loop — the typechecker should
                        // reject a `continue` outside any loop before
                        // codegen ever sees one. `unreachable` here is a
                        // defensive fallback for that "should be
                        // impossible" case, not the general-case behavior
                        // it used to be unconditionally (see `loop_stack`'s
                        // doc comment for why that was a real bug).
                        self.builder.build_unreachable().unwrap();
                    }
                }
                Ok(true)
            }
            Stmt::Break(_value, _) => {
                // `break <value>` (loop-as-expression) parses today but
                // the value isn't wired to anything yet — no codegen path
                // makes a `while`/`for` loop itself produce a value the
                // way `if`/`match` now do (see `compile_if_expr`/
                // `compile_match`). Branching to the correct exit block
                // (fixing the crash) is independent of that and worth
                // doing now regardless; a future `loop { ... break x }`
                // expression form would need its own phi-join at the
                // loop's exit block, same pattern as `join_branch_values`.
                match self.loop_stack.last() {
                    Some(&(_, break_target)) => {
                        self.builder.build_unconditional_branch(break_target).unwrap();
                    }
                    None => {
                        self.builder.build_unreachable().unwrap();
                    }
                }
                Ok(true)
            }
            Stmt::Item(_) | Stmt::Import(..) => Ok(false),
        }
    }

    fn if_stmt(&mut self, cond: &Expr, then_b: &[Stmt],
               elsifs: &[(Expr, Vec<Stmt>)], else_b: &Option<Vec<Stmt>>) -> R<bool>
               {
                   let parent = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                   let cv     = self.as_bool(cond)?;
                   let then_blk  = self.ctx.append_basic_block(parent, "then");
                   let else_blk  = self.ctx.append_basic_block(parent, "else");
                   let merge_blk = self.ctx.append_basic_block(parent, "merge");
                   self.builder.build_conditional_branch(cv, then_blk, else_blk).unwrap();

                   // Tracks whether *any* branch of this if/elsif/else chain
                   // actually reaches `merge_blk` (i.e. whether it will end
                   // up with at least one predecessor). BUG FIX: this used
                   // to be unconditionally assumed true — `if_stmt` always
                   // returned `Ok(false)` ("this if did not terminate") and
                   // always left the builder positioned on `merge_blk`,
                   // even when *every* branch (then/elsif/else) ends its own
                   // block with a real terminator (`return`, `exit(...)`,
                   // `panic(...)`, `break`/`continue`). In that case nothing
                   // ever branches into `merge_blk` — it's a live block with
                   // zero predecessors and zero instructions, which LLVM's
                   // verifier rejects as "does not have terminator" the
                   // moment nothing downstream happens to fill it in (e.g.
                   // this `if` is the last statement in its enclosing
                   // function, match arm, or another if-branch — exactly
                   // the `then`/`match_arm*`/`else` blocks the verifier was
                   // flagging). `compile_match` already avoids the
                   // equivalent trap by always emitting an unconditional
                   // "no arm matched" fallthrough edge into its merge
                   // block; `if_stmt` gets the same guarantee here instead
                   // of leaving `merge_blk` to chance.
                   let mut merge_has_pred = false;

                   self.builder.position_at_end(then_blk);
                   self.enter_branch();
                   let t1 = self.stmts(then_b)?;
                   self.exit_branch();
                   if !t1 {
                       self.builder.build_unconditional_branch(merge_blk).unwrap();
                       merge_has_pred = true;
                   }

                   self.builder.position_at_end(else_blk);
                   if !elsifs.is_empty() {
                       let (ec, eb) = &elsifs[0];
                       // Note: the recursive `if_stmt` call for the elsif
                       // chain manages its own `enter_branch`/`exit_branch`
                       // around *its* then/else bodies — no extra guard
                       // needed here. Its return value is now trustworthy
                       // (see above), so branch into *our* merge_blk only
                       // when the elsif chain didn't already terminate
                       // every path through itself.
                       let elsif_terminated = self.if_stmt(ec, eb, &elsifs[1..], else_b)?;
                       if !elsif_terminated {
                           self.builder.build_unconditional_branch(merge_blk).unwrap();
                           merge_has_pred = true;
                       }
                   } else if let Some(eb) = else_b {
                       self.enter_branch();
                       let t2 = self.stmts(eb)?;
                       self.exit_branch();
                       if !t2 {
                           self.builder.build_unconditional_branch(merge_blk).unwrap();
                           merge_has_pred = true;
                       }
                   } else {
                       // No `else` at all ⇒ the implicit "condition was
                       // false" path always falls through to merge_blk.
                       self.builder.build_unconditional_branch(merge_blk).unwrap();
                       merge_has_pred = true;
                   }

                   self.builder.position_at_end(merge_blk);
                   if merge_has_pred {
                       Ok(false)
                   } else {
                       // Every path through this if/elsif/else terminated
                       // its own block — merge_blk is unreachable dead
                       // code, but it still needs a real terminator to be
                       // valid IR. Give it one, and report upward that the
                       // whole construct terminates (so a caller that is
                       // itself another `if_stmt`/`compile_match` arm knows
                       // not to also try branching out of it).
                       self.builder.build_unreachable().unwrap();
                       Ok(true)
                   }
               }

               /// Compiles `then`/`elsif`/`else` bodies where the *value* of
               /// the branch matters (an `if` used as an expression, e.g.
               /// `let x = if cond then a else b`, or `"prefix " + if v then
               /// "a" else "b"`), producing a real phi-joined result instead
               /// of discarding it. Mirrors `compile_match`'s
               /// phi_incoming/"give every path a real terminator or a real
               /// phi entry" approach — `if_stmt` above is the void
               /// (statement) sibling of this function and intentionally
               /// shares none of its value-tracking, since a void `if` has
               /// no value to join.
               /// Shared machinery behind *every* value-producing multi-way
               /// branch in this compiler (`if`-as-expression,
               /// `match`-as-expression — and, going forward, whatever's
               /// next: a future `loop { ... break value }` or similar).
               ///
               /// # Why this exists
               /// `if`-as-expression and `match`-as-expression used to each
               /// hand-roll their own "compile each branch, coerce its
               /// value, wire it into a phi at a shared merge block, and —
               /// if literally every branch terminated its own block
               /// instead of falling through — give the merge block a real
               /// `unreachable` terminator instead of leaving it as
               /// predecessor-less invalid IR" logic, independently, at
               /// different times. Both copies had the exact same bug
               /// shape at different points in this codebase's history:
               /// `if`-as-expression once just discarded its branches'
               /// values and returned a hardcoded zero; `match`-as-
               /// expression had that *same* bug independently, well after
               /// the first one was already fixed and documented as the
               /// pattern to follow. Two independent copies of one
               /// mechanism drifting out of sync with each other is exactly
               /// how that class of bug keeps recurring — this function is
               /// the fix for the *pattern*, not just the two known
               /// instances of it: any future value-producing branch
               /// construct calls this instead of writing a third copy.
               ///
               /// Callers build their own basic blocks and drive their own
               /// pattern-matching/condition logic (an `if`'s boolean
               /// condition and a `match`'s pattern conditions have nothing
               /// in common structurally) — this only owns the part that
               /// *was* duplicated: turning a list of `(value, block)`
               /// pairs, one per branch that didn't terminate, into a
               /// single joined value at `merge_bb`. Positions the builder
               /// at `merge_bb` before returning either way.
               fn join_branch_values(
                   &mut self,
                   merge_bb: inkwell::basic_block::BasicBlock<'ctx>,
                   result_ty: BasicTypeEnum<'ctx>,
                   incoming: &[(BasicValueEnum<'ctx>, inkwell::basic_block::BasicBlock<'ctx>)],
               ) -> BasicValueEnum<'ctx> {
                   self.builder.position_at_end(merge_bb);
                   if incoming.is_empty() {
                       // Every branch terminated its own block (e.g. every
                       // arm of a `match` ends in `return`) — merge_bb has
                       // no predecessors. Give it a real terminator instead
                       // of leaving invalid IR; the returned value is
                       // unreachable at runtime so its exact bit pattern
                       // doesn't matter, only that *some* well-typed value
                       // is returned to keep this function's signature honest.
                       self.builder.build_unreachable().unwrap();
                       return self.zero(result_ty);
                   }
                   let phi = self.builder.build_phi(result_ty, "branch_val").unwrap();
                   for (v, bb) in incoming { phi.add_incoming(&[(v, *bb)]); }
                   phi.as_basic_value()
               }

               /// Compiles one branch body (an `if`/`elsif`/`else` body, or
               /// a `match` arm's body) at the current insertion point for
               /// `join_branch_values` above: evaluates it via
               /// `stmts_with_value`, and — if it didn't terminate its own
               /// block — coerces its value to `result_ty`, branches to
               /// `merge_bb`, and appends the `(value, block)` pair to
               /// `incoming` for the eventual phi. Returns whether the
               /// branch terminated, so callers with their own control
               /// flow around this (e.g. `if_stmt`'s elsif recursion) know
               /// whether to keep going.
               fn compile_branch_value(
                   &mut self,
                   body: &[Stmt],
                   result_ty: BasicTypeEnum<'ctx>,
                   merge_bb: inkwell::basic_block::BasicBlock<'ctx>,
                   incoming: &mut Vec<(BasicValueEnum<'ctx>, inkwell::basic_block::BasicBlock<'ctx>)>,
               ) -> R<bool> {
                   self.enter_branch();
                   let (terminated, val) = self.stmts_with_value(body, Some(result_ty))?;
                   self.exit_branch();
                   if !terminated {
                       let coerced = self.coerce_basic_value(val, result_ty);
                       let end_bb  = self.builder.get_insert_block().unwrap();
                       self.builder.build_unconditional_branch(merge_bb).unwrap();
                       incoming.push((coerced, end_bb));
                   }
                   Ok(terminated)
               }

               fn compile_if_expr(
                   &mut self,
                   condition: &Expr,
                   then_body: &[Stmt],
                   elsif_branches: &[(Expr, Vec<Stmt>)],
                   else_body: &Option<Vec<Stmt>>,
                   hint: Option<BasicTypeEnum<'ctx>>,
               ) -> R<BasicValueEnum<'ctx>> {
                   let parent = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                   let result_ty: BasicTypeEnum<'ctx> = hint.unwrap_or_else(|| self.ctx.i64_type().into());

                   let cv        = self.as_bool(condition)?;
                   let then_bb   = self.ctx.append_basic_block(parent, "if_then");
                   let else_bb   = self.ctx.append_basic_block(parent, "if_else");
                   let merge_bb  = self.ctx.append_basic_block(parent, "if_merge");
                   self.builder.build_conditional_branch(cv, then_bb, else_bb).unwrap();

                   let mut incoming: Vec<(BasicValueEnum<'ctx>, inkwell::basic_block::BasicBlock<'ctx>)> = Vec::new();

                   self.builder.position_at_end(then_bb);
                   self.compile_branch_value(then_body, result_ty, merge_bb, &mut incoming)?;

                   self.builder.position_at_end(else_bb);
                   if !elsif_branches.is_empty() {
                       let (ec, eb) = &elsif_branches[0];
                       let v = self.compile_if_expr(ec, eb, &elsif_branches[1..], else_body, Some(result_ty))?;
                       if let Some(cur) = self.builder.get_insert_block() {
                           if cur.get_terminator().is_none() {
                               let vc = self.coerce_basic_value(v, result_ty);
                               self.builder.build_unconditional_branch(merge_bb).unwrap();
                               incoming.push((vc, cur));
                           }
                       }
                   } else if let Some(eb) = else_body {
                       self.compile_branch_value(eb, result_ty, merge_bb, &mut incoming)?;
                   } else {
                       // No `else` on a value-producing `if` — nothing
                       // meaningful to hand back on this path; fall through
                       // with the result type's zero rather than leaving
                       // this edge unaccounted for.
                       let zero   = self.zero(result_ty);
                       let end_bb = self.builder.get_insert_block().unwrap();
                       self.builder.build_unconditional_branch(merge_bb).unwrap();
                       incoming.push((zero, end_bb));
                   }

                   Ok(self.join_branch_values(merge_bb, result_ty, &incoming))
               }

               /// Statement-list helper for value contexts: runs every
               /// statement except the last normally, then — if the last
               /// statement is a bare value expression (not a void control
               /// construct like `while`/`for`/assignment/`return`) —
               /// evaluates it as the tail *value* of the block, Rust-block
               /// style, instead of routing it through `stmt()` (which
               /// always discards expression values). Returns
               /// `(terminated, value)`.
               ///
               /// `Expr::If`/`Expr::Match` are deliberately *not* excluded
               /// here (unlike `While`/`For`) — this function is only ever
               /// called on the body of an `if`/`elsif`/`else` branch or a
               /// `match` arm (its one call site is `compile_branch_value`,
               /// shared by `compile_if_expr`/`compile_match`), never on a
               /// whole function body, so a *nested* `if`/`match` in tail
               /// position here really is this branch's value — exactly
               /// the shape `else if cond then a else b` desugars to (see
               /// `parse_if`'s ternary-shorthand elsif handling). Treating
               /// it as void instead (the previous behavior) silently
               /// discarded the real value of every `else if`-chained
               /// branch in a value-producing `if`, in favor of a dummy
               /// zero — a real, user-visible bug in `bytes_final`'s own
               /// `config.h#` (`hk_parse_value`), not just a hypothetical
               /// one.
               fn stmts_with_value(&mut self, stmts: &[Stmt], hint: Option<BasicTypeEnum<'ctx>>) -> R<(bool, BasicValueEnum<'ctx>)> {
                   let zero: BasicValueEnum<'ctx> = self.zero(hint.unwrap_or_else(|| self.ctx.i64_type().into()));
                   if stmts.is_empty() { return Ok((false, zero)); }
                   let (init, last) = stmts.split_at(stmts.len() - 1);
                   for s in init {
                       if self.stmt(s)? { return Ok((true, zero)); }
                   }
                   match &last[0] {
                       Stmt::Expr(e, _) if !matches!(e,
                           Expr::While{..} | Expr::For{..} |
                           Expr::Assign(..) | Expr::CompoundAssign(..) | Expr::Return(..)) =>
                       {
                           let v = self.expr(e, hint)?;
                           // A nested `Expr::If`/`Expr::Match` in tail
                           // position can itself terminate every path it
                           // contains (e.g. every arm ends in `return`) —
                           // in which case `compile_if_expr`/`compile_match`
                           // already gave *their own* merge block a real
                           // `unreachable` terminator and left the builder
                           // positioned there. Detect that and report
                           // `terminated = true` instead of `(false, v)`;
                           // `v` is unreachable at runtime either way, but
                           // the caller (`compile_branch_value`) must not
                           // try to add a *second* terminator on top of the
                           // `unreachable` that's already in this block —
                           // that's invalid IR, the same class of bug this
                           // whole file's `join_branch_values` mechanism
                           // exists to prevent elsewhere.
                           let already_terminated = self.builder.get_insert_block()
                               .map(|b| b.get_terminator().is_some()).unwrap_or(false);
                           Ok((already_terminated, v))
                       }
                       s => {
                           let terminated = self.stmt(s)?;
                           Ok((terminated, zero))
                       }
                   }
               }

               /// Stores `value` into the storage location `lhs` refers
               /// to — the write-side counterpart to how `expr()` already
               /// reads `Expr::Ident`/`Expr::FieldAccess`/`Expr::IndexAccess`.
               ///
               /// # BUG FIX — this capability didn't exist at all before
               /// Both `Expr::Assign` codegen sites (statement form and
               /// value-expression form) only ever handled `lhs` being a
               /// bare `Expr::Ident` — `if let Expr::Ident(name, _) =
               /// lhs.as_ref() { ... }` with **no `else` branch at all**.
               /// Assigning through a field or an index —
               /// `proj.package.name = val`, `c.bold = "..."`,
               /// `arr[i] = x` — silently compiled to a complete no-op:
               /// no error, no warning, the assignment just didn't
               /// happen. This is what made `bytes_final`'s own
               /// `config::parse()` always report `name=unnamed`: every
               /// `proj.package.NAME = val` assignment in that function
               /// silently did nothing.
               ///
               /// Mirrors the read-side logic exactly (see
               /// `Expr::FieldAccess`/`Expr::IndexAccess` in `expr()`):
               /// resolve the field index the same way, box `value` down
               /// to the generic `i64` slot this runtime stores every
               /// field/element as (via `call_coerced`, which already
               /// auto-coerces call arguments to the callee's declared
               /// parameter types), and call `hsh_struct_set`/
               /// `hsh_array_set` — both already existed in the runtime
               /// and were simply never called from here.
               fn assign_lvalue(&mut self, lhs: &Expr, value: BasicValueEnum<'ctx>) -> R<()> {
                   match lhs {
                       Expr::Ident(name, _) => {
                           if let Some(&(ptr, ty)) = self.vars.get(name.as_str()) {
                               // BUG FIX (extending `@arc`): reassigning an
                               // `arc_owned` variable — `x = arc_alloc(n)`
                               // a second time, or `x = other_arc_var` —
                               // used to just overwrite the pointer with
                               // no release of what it held before,
                               // because `arc_owned` tracking only ever
                               // ran inside the `Let` handler (a *new*
                               // binding), never on plain assignment to an
                               // *existing* one. Every reassignment of an
                               // `@arc`-tracked local was a guaranteed
                               // leak of whatever it held previously — the
                               // epilogue only ever sees (and releases)
                               // the *final* value at return, not
                               // whatever was overwritten along the way.
                               // Release the old value first, mirroring
                               // `emit_arc_epilogue`'s own
                               // load-then-`hsh_rc_release` pattern,
                               // whenever this name is one `@arc` is
                               // actually tracking.
                               if self.mem_mode == MemoryMode::Arc && self.arc_owned.borrow().contains(name) {
                                   let old = self.builder.build_load(ty, ptr, "arc_realloc_old").unwrap();
                                   self.call_coerced(self.builtins.hsh_rc_release, &[old], "");
                               }
                               let v = self.coerce_basic_value(value, ty);
                               self.builder.build_store(ptr, v).unwrap();
                           }
                           Ok(())
                       }
                       Expr::FieldAccess(obj_e, field_name, _span) => {
                           let obj = self.expr(obj_e, None)?;
                           let field_idx = match self.infer_struct_name(obj_e) {
                               Some(struct_name) => self.resolve_struct_field_index(&struct_name, field_name),
                               None => {
                                   // Same "can't statically determine the
                                   // struct type" fallback the read side
                                   // uses — scan every struct for a
                                   // matching field name. Same ambiguity
                                   // caveat applies; kept consistent with
                                   // the read path rather than silently
                                   // diverging from it.
                                   let mut found = 0usize;
                                   'outer: for fields in self.structs.values() {
                                       for (i, f) in fields.iter().enumerate() {
                                           if &f.name == field_name { found = i; break 'outer; }
                                       }
                                   }
                                   found
                               }
                           };
                           let idx_v = self.ctx.i64_type().const_int(field_idx as u64, false);
                           self.call_coerced(self.builtins.hsh_struct_set, &[obj.into(), idx_v.into(), value.into()], "fset");
                           Ok(())
                       }
                       Expr::IndexAccess(arr_e, idx_e, _) => {
                           let arr = self.expr(arr_e, None)?;
                           let idx = self.expr(idx_e, None)?;
                           self.call_coerced(self.builtins.hsh_array_set, &[arr.into(), idx.into(), value.into()], "aset");
                           Ok(())
                       }
                       _ => Ok(()), // Not a valid assignment target — the typechecker should reject this before codegen sees it.
                   }
               }

               fn while_stmt(&mut self, cond: &Expr, body: &[Stmt]) -> R<bool> {
                   let parent = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                   let header = self.ctx.append_basic_block(parent, "while_hdr");
                   let body_b = self.ctx.append_basic_block(parent, "while_body");
                   let exit   = self.ctx.append_basic_block(parent, "while_exit");
                   self.builder.build_unconditional_branch(header).unwrap();
                   self.builder.position_at_end(header);
                   let cv = self.as_bool(cond)?;
                   self.builder.build_conditional_branch(cv, body_b, exit).unwrap();
                   self.builder.position_at_end(body_b);
                   self.enter_branch();
                   // `continue` re-checks the condition (branches to
                   // `header`); `break` exits the loop (branches to
                   // `exit`) — see `loop_stack`'s doc comment for why this
                   // needs to be explicit rather than left to a bare
                   // `unreachable`.
                   self.loop_stack.push((header, exit));
                   let t = self.stmts(body)?;
                   self.loop_stack.pop();
                   self.exit_branch();
                   if !t { self.builder.build_unconditional_branch(header).unwrap(); }
                   self.builder.position_at_end(exit);
                   Ok(false)
               }

               fn for_stmt(&mut self, pat: &Pattern, iter: &Expr, body: &[Stmt]) -> R<bool> {
                   if let Expr::Range(start, end_e, inclusive, _) = iter {
                       let vname = match pat { Pattern::Ident(n, _) => n.as_str(), _ => "__i" };
                       let i64t  = self.ctx.i64_type();
                       let sv    = self.expr(start, Some(i64t.into()))?;
                       let ev    = self.expr(end_e,  Some(i64t.into()))?;
                       let loop_ptr = self.builder.build_alloca(i64t, vname).unwrap();
                       self.builder.build_store(loop_ptr, sv).unwrap();
                       self.vars.insert(vname.to_string(), (loop_ptr, i64t.into()));
                       let parent = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                       let header = self.ctx.append_basic_block(parent, "for_hdr");
                       let body_b = self.ctx.append_basic_block(parent, "for_body");
                       // `continue`'s target is *not* `header` directly —
                       // `header` only checks the loop condition against
                       // the current counter value, it doesn't advance it.
                       // Jumping straight there from `continue` would skip
                       // the increment below and spin forever on the same
                       // value. `for_continue` does the increment, *then*
                       // re-checks via `header` — the natural end-of-body
                       // fallthrough and an explicit `continue` both need
                       // to go through it, not around it.
                       let continue_b = self.ctx.append_basic_block(parent, "for_continue");
                       let exit   = self.ctx.append_basic_block(parent, "for_exit");
                       self.builder.build_unconditional_branch(header).unwrap();
                       self.builder.position_at_end(header);
                       let cur  = self.builder.build_load(i64t, loop_ptr, "cur").unwrap();
                       let cond = if *inclusive {
                           self.builder.build_int_compare(
                               inkwell::IntPredicate::SLE, cur.into_int_value(), ev.into_int_value(), "cmp").unwrap()
                       } else {
                           self.builder.build_int_compare(
                               inkwell::IntPredicate::SLT, cur.into_int_value(), ev.into_int_value(), "cmp").unwrap()
                       };
                       self.builder.build_conditional_branch(cond, body_b, exit).unwrap();
                       self.builder.position_at_end(body_b);
                       self.enter_branch();
                       self.loop_stack.push((continue_b, exit));
                       let t = self.stmts(body)?;
                       self.loop_stack.pop();
                       self.exit_branch();
                       if !t { self.builder.build_unconditional_branch(continue_b).unwrap(); }
                       self.builder.position_at_end(continue_b);
                       let c2  = self.builder.build_load(i64t, loop_ptr, "c2").unwrap().into_int_value();
                       let one = i64t.const_int(1, false);
                       let nxt = self.builder.build_int_add(c2, one, "nxt").unwrap();
                       self.builder.build_store(loop_ptr, nxt).unwrap();
                       self.builder.build_unconditional_branch(header).unwrap();
                       self.builder.position_at_end(exit);
                   } else {
                       // ── Array iteration (`for x in arr is ... end`) ────
                       // CRITICAL FIX: this whole branch used to be just
                       // `self.expr(iter, None)?;` — evaluate the iterable
                       // once, throw the result away, and never touch
                       // `body` at all. Every `for` loop whose iterable
                       // wasn't a literal `a..b` range (i.e. any loop
                       // over an array — `for c in candidates is ...`,
                       // `for line in lines is ...`, the overwhelming
                       // majority of real `for` loops in any nontrivial
                       // program) silently compiled to a no-op: the
                       // variable got evaluated and discarded, the loop
                       // body — everything inside it — never ran, not
                       // even once. No error, no warning: the function
                       // just quietly did nothing.
                       let vname = match pat { Pattern::Ident(n, _) => n.as_str(), _ => "__it" };
                       let i64t  = self.ctx.i64_type();
                       let arr_v = self.expr(iter, None)?;

                       // What LLVM type should each unboxed element be
                       // treated as? `hsh_array_get` always returns a raw
                       // `i64` slot value (this runtime boxes every
                       // element the same way, string or int or struct
                       // pointer) — look up the source array's declared
                       // element type (tracked at `let`/param sites via
                       // `array_elem_llvm_ty`) to know how to unbox it.
                       // Default to `ptr` when unknown (a function-call
                       // result, an untyped variable, ...): the large
                       // majority of real `for`-loop bodies observed in
                       // practice iterate over strings or structs, both
                       // pointer-shaped, so this is the safer default —
                       // a numeric array wrongly treated as pointer-typed
                       // would still print/compare as *some* pointer
                       // value rather than silently doing nothing, which
                       // is strictly better than this branch's previous
                       // behavior regardless.
                       let elem_ty: BasicTypeEnum = self.infer_array_elem_llvm_ty(iter)
                           .unwrap_or_else(|| self.ctx.ptr_type(inkwell::AddressSpace::default()).into());

                       let len_call = self.call_coerced(self.builtins.hsh_array_len, &[arr_v], "flen");
                       let len_v    = self.unwrap_call(len_call).into_int_value();

                       let idx_ptr = self.builder.build_alloca(i64t, "for_idx").unwrap();
                       self.builder.build_store(idx_ptr, i64t.const_zero()).unwrap();
                       let elem_ptr = self.builder.build_alloca(elem_ty, vname).unwrap();
                       self.vars.insert(vname.to_string(), (elem_ptr, elem_ty));

                       let parent = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                       let header = self.ctx.append_basic_block(parent, "forarr_hdr");
                       let body_b = self.ctx.append_basic_block(parent, "forarr_body");
                       // Same reasoning as the range-based `for` above:
                       // `continue` must go through the index increment,
                       // not straight to `header` (which would skip it and
                       // spin forever re-checking the same index).
                       let continue_b = self.ctx.append_basic_block(parent, "forarr_continue");
                       let exit   = self.ctx.append_basic_block(parent, "forarr_exit");
                       self.builder.build_unconditional_branch(header).unwrap();

                       self.builder.position_at_end(header);
                       let idx_cur = self.builder.build_load(i64t, idx_ptr, "idx").unwrap().into_int_value();
                       let cond = self.builder.build_int_compare(
                           inkwell::IntPredicate::SLT, idx_cur, len_v, "forarr_cmp").unwrap();
                       self.builder.build_conditional_branch(cond, body_b, exit).unwrap();

                       self.builder.position_at_end(body_b);
                       let idx_b = self.builder.build_load(i64t, idx_ptr, "idx_b").unwrap();
                       let get_call = self.call_coerced(self.builtins.hsh_array_get, &[arr_v, idx_b], "fget");
                       let raw = self.unwrap_call(get_call);
                       let unboxed = self.coerce_basic_value(raw, elem_ty);
                       self.builder.build_store(elem_ptr, unboxed).unwrap();

                       self.enter_branch();
                       self.loop_stack.push((continue_b, exit));
                       let t = self.stmts(body)?;
                       self.loop_stack.pop();
                       self.exit_branch();
                       if !t { self.builder.build_unconditional_branch(continue_b).unwrap(); }
                       self.builder.position_at_end(continue_b);
                       let idx_c2 = self.builder.build_load(i64t, idx_ptr, "idx_c2").unwrap().into_int_value();
                       let one    = i64t.const_int(1, false);
                       let nxt    = self.builder.build_int_add(idx_c2, one, "idx_nxt").unwrap();
                       self.builder.build_store(idx_ptr, nxt).unwrap();
                       self.builder.build_unconditional_branch(header).unwrap();
                       self.builder.position_at_end(exit);
                   }
                   Ok(false)
               }

               /// Normalizes an already-evaluated value to a genuine LLVM
               /// `i1` boolean (`icmp ne 0`), without re-evaluating the
               /// source expression (unlike `as_bool`, which takes an
               /// `&Expr` and evaluates it itself — calling that a second
               /// time on an expression already evaluated once would
               /// duplicate side effects and waste work). Needed because
               /// H#'s builtins/comparisons don't uniformly return `i1`:
               /// `binop`'s `==`/`<`/etc. do (via LLVM `icmp`, which is
               /// always `i1`), but plain-boolean-returning builtins like
               /// `string_contains`/`string_starts_with` return a full
               /// `i64` (0 or 1) — both are valid "truthy ints" at the
               /// language level, but LLVM requires an exact `i1` for a
               /// branch condition or a phi typed `i1`.
               fn to_i1(&mut self, v: BasicValueEnum<'ctx>) -> R<inkwell::values::IntValue<'ctx>> {
                   Ok(match v {
                       BasicValueEnum::IntValue(i) if i.get_type().get_bit_width() == 1 => i,
                       BasicValueEnum::IntValue(i) => {
                           let z = i.get_type().const_zero();
                           self.builder.build_int_compare(inkwell::IntPredicate::NE, i, z, "toi1").unwrap()
                       }
                       BasicValueEnum::FloatValue(f) => {
                           let z = f.get_type().const_float(0.0);
                           self.builder.build_float_compare(inkwell::FloatPredicate::ONE, f, z, "ftoi1").unwrap()
                       }
                       BasicValueEnum::PointerValue(p) => {
                           let z = p.get_type().const_null();
                           self.builder.build_int_compare(inkwell::IntPredicate::NE,
                               self.builder.build_ptr_to_int(p, self.ctx.i64_type(), "p2i").unwrap(),
                               self.builder.build_ptr_to_int(z, self.ctx.i64_type(), "z2i").unwrap(),
                               "ptoi1").unwrap()
                       }
                       _ => self.ctx.bool_type().const_int(1, false),
                   })
               }

               fn expr(&mut self, e: &Expr, hint: Option<BasicTypeEnum<'ctx>>) -> R<BasicValueEnum<'ctx>> {
                   match e {
                       Expr::Literal(lit, _) => self.literal(lit, hint),
                       Expr::Ident(name, span)  => {
                           let (ptr, ty) = self.vars.get(name.as_str())
                           .copied()
                           .ok_or_else(|| CodegenError::UndefinedVar { name: name.clone(), span: span.clone() })?;
                           Ok(self.builder.build_load(ty, ptr, name).unwrap())
                       }
                       Expr::BinOp(l, op, r, _) => {
                           // BUG FIX: `&&`/`||` used to fall straight
                           // through to the generic path below — evaluate
                           // *both* operands unconditionally, then combine
                           // them with a plain bitwise `and`/`or` LLVM
                           // instruction. That's wrong: `&&`/`||` are
                           // supposed to short-circuit, and real code
                           // throughout this project's own example
                           // programs depends on that — e.g. `if argc == 0
                           // || args[0] == "help" is ...` (unpack.h#) is
                           // only safe to write *because* a short-
                           // circuiting `||` guarantees `args[0]` is never
                           // touched once `argc == 0` is already true.
                           // Without short-circuiting, that `args[0]`
                           // still gets evaluated on an empty array —
                           // reading garbage/out-of-bounds memory and
                           // handing it to `strcmp`, which is exactly the
                           // segfault this fix resolves (`hacker unpack`
                           // with no arguments). Compile these as real
                           // branches instead: for `a || b`, only
                           // evaluate `b` when `a` was false; for `a &&
                           // b`, only evaluate `b` when `a` was true.
                           if matches!(op, BinOp::And | BinOp::Or) {
                               let parent = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                               let lv_raw = self.expr(l, None)?;
                               let lv = self.to_i1(lv_raw)?;
                               let rhs_bb  = self.ctx.append_basic_block(parent, "sc_rhs");
                               let merge_bb = self.ctx.append_basic_block(parent, "sc_merge");
                               let short_circuit_bb = self.ctx.append_basic_block(parent, "sc_skip");
                               // `||`: skip straight to `true` if `lv` is
                               // already true, otherwise evaluate `r`.
                               // `&&`: skip straight to `false` if `lv` is
                               // already false, otherwise evaluate `r`.
                               match op {
                                   BinOp::Or  => self.builder.build_conditional_branch(lv, short_circuit_bb, rhs_bb).unwrap(),
                                   _          => self.builder.build_conditional_branch(lv, rhs_bb, short_circuit_bb).unwrap(),
                               };
                               let entry_bb = self.builder.get_insert_block().unwrap();

                               self.builder.position_at_end(short_circuit_bb);
                               self.builder.build_unconditional_branch(merge_bb).unwrap();

                               self.builder.position_at_end(rhs_bb);
                               let rv_raw = self.expr(r, None)?;
                               let rv = self.to_i1(rv_raw)?;
                               let rhs_end_bb = self.builder.get_insert_block().unwrap();
                               self.builder.build_unconditional_branch(merge_bb).unwrap();

                               self.builder.position_at_end(merge_bb);
                               let i1t = self.ctx.bool_type();
                               let phi = self.builder.build_phi(i1t, "sc_result").unwrap();
                               let short_circuit_val = match op {
                                   BinOp::Or => i1t.const_int(1, false),
                                   _         => i1t.const_int(0, false),
                               };
                               phi.add_incoming(&[(&short_circuit_val, short_circuit_bb), (&rv, rhs_end_bb)]);
                               let _ = entry_bb;
                               return Ok(phi.as_basic_value());
                           }
                           let lv = self.expr(l, hint)?;
                           let rv = self.expr(r, hint)?;
                           // String concat for pointer + pointer
                           if matches!(op, BinOp::Add) {
                               if let (BasicValueEnum::PointerValue(_), BasicValueEnum::PointerValue(_)) = (&lv, &rv) {
                                   let r2 = self.call_coerced(
                                       self.builtins.hsh_strcat, &[lv.into(), rv.into()], "cat");
                                       return Ok(self.unwrap_call(r2));
                               }
                           }
                           self.binop(op, lv, rv)
                       }
                       Expr::UnOp(op, inner, _) => {
                           let v = self.expr(inner, hint)?;
                           Ok(match op {
                               UnOp::Neg => match v {
                                   BasicValueEnum::IntValue(i)   => self.builder.build_int_neg(i, "neg").unwrap().into(),
                              BasicValueEnum::FloatValue(f) => self.builder.build_float_neg(f, "fneg").unwrap().into(),
                              _                             => v,
                               },
                               UnOp::Not => {
                                   let i = v.into_int_value();
                                   let z = i.get_type().const_zero();
                                   self.builder.build_int_compare(inkwell::IntPredicate::EQ, i, z, "not").unwrap().into()
                               }
                               _ => v,
                           })
                       }
                       Expr::Call(callee, args, call_span) => {
                           if let Expr::Ident(name, _) = callee.as_ref() {
                               self.call_fn(name, args, hint, call_span)
                           } else if let Expr::Path(segments, _) = callee.as_ref() {
                               // module::function — try the snake_case mangled
                               // runtime symbol first (matches the interpreter's
                               // stdlib bridge convention: json::parse ->
                               // json_parse; env::args -> env_args, etc.).
                               // `call_fn` itself already checks both
                               // user-defined functions (func_vals) *and*
                               // built-ins for this name, so there's no need
                               // (and it was wrong) to pre-filter on
                               // func_vals membership here — that pre-filter
                               // is exactly why `env::args()` used to resolve
                               // to the bare, nonexistent name `args` instead
                               // of the real built-in `env_args`.
                               let snake = segments.join("_");
                               match self.call_fn(&snake, args, hint, call_span) {
                                   Ok(v) => Ok(v),
                                   Err(CodegenError::UndefinedFn { .. }) => {
                                       // snake_case join didn't resolve to
                                       // anything — fall back to the bare
                                       // last segment (e.g. a namespace that
                                       // is only a visual grouping, not part
                                       // of the mangled runtime name).
                                       if let Some(last) = segments.last() {
                                           self.call_fn(last, args, hint, call_span)
                                       } else {
                                           Err(CodegenError::UndefinedFn { name: snake, span: call_span.clone() })
                                       }
                                   }
                                   Err(other) => Err(other),
                               }
                           } else {
                               // Callee is some other expression (e.g. a
                               // function value stored in a variable/field).
                               // Indirect calls through a computed function
                               // pointer aren't implemented in codegen yet —
                               // silently returning 0 here used to hide that;
                               // fail loudly instead.
                               Err(CodegenError::Llvm(
                                   "unsupported call expression: callee is not a plain identifier or module::path (indirect/computed function calls aren't implemented yet)".to_string()
                               ))
                           }
                       }
                       Expr::Assign(lhs, rhs, _) => {
                           let target_ty = match lhs.as_ref() {
                               Expr::Ident(name, _) => self.vars.get(name.as_str()).map(|&(_, ty)| ty),
                               _ => None,
                           };
                           let v = self.expr(rhs, target_ty)?;
                           self.assign_lvalue(lhs, v)?;
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
                           // BUG FIX: this used to always call the void
                           // `if_stmt` and return a hardcoded zero,
                           // silently discarding the actual branch value —
                           // meaning every ternary-style `if cond then a
                           // else b` used as an expression (`let x = if
                           // ... then ... else ...`, string concatenation
                           // like `"prefix " + if v then "a" else "b"`,
                           // etc. — a pattern used pervasively throughout
                           // both example projects) silently evaluated to
                           // `0`/null instead of `a`/`b`. `compile_if_expr`
                           // mirrors `compile_match`'s real phi-based value
                           // join instead.
                           self.compile_if_expr(condition, then_body, elsif_branches, else_body, hint)
                       }
                       Expr::While { condition, body, .. } => {
                           self.while_stmt(condition, body)?;
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       Expr::For { pattern, iterable, body, .. } => {
                           self.for_stmt(pattern, iterable, body)?;
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       Expr::Cast(inner, ty, _) => {
                           let v   = self.expr(inner, None)?;
                           let dst = htype_to_llvm(self.ctx, ty).unwrap_or(self.ctx.i64_type().into());
                           self.cast(v, dst)
                       }
                       Expr::Return(val, _) => {
                           self.build_return_coerced(val.as_deref())?;
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       Expr::Try(inner, _) => {
                           let val = self.expr(inner, hint)?;
                           let fn_val = self.builder.get_insert_block()
                           .and_then(|b| b.get_parent()).unwrap();
                           let then_bb  = self.ctx.append_basic_block(fn_val, "try_err");
                           let merge_bb = self.ctx.append_basic_block(fn_val, "try_ok");
                           let zero     = self.ctx.i64_type().const_zero();
                           let is_err   = if let BasicValueEnum::IntValue(iv) = val {
                               self.builder.build_int_compare(inkwell::IntPredicate::EQ, iv, zero, "is_err").unwrap()
                           } else { self.ctx.bool_type().const_zero() };
                           self.builder.build_conditional_branch(is_err, then_bb, merge_bb).unwrap();
                           self.builder.position_at_end(then_bb);
                           self.builder.build_return(Some(&BasicValueEnum::IntValue(zero))).unwrap();
                           self.builder.position_at_end(merge_bb);
                           Ok(val)
                       }
                       // ── await expr ──────────────────────────────────────────
                       // Compiled model: an async fn returns an opaque *i64 handle
                       // (pointer to a heap-allocated HshTask).  `await expr` calls
                       // the runtime helper `hsh_task_wait(handle) -> i64` which
                       // blocks the calling pthread until the task completes and
                       // returns the payload.  For synchronous values (non-task
                       // pointers) `hsh_task_wait` is a no-op and returns the value
                       // unchanged — so `await non_async_fn()` is safe and free.
                       Expr::Await(inner, _) => {
                           let task_ptr = self.expr(inner, hint)?;
                           // Call hsh_task_wait(task_ptr) -> i64
                           let wait_fn = self.func_vals.get("hsh_task_wait")
                               .copied()
                               .or_else(|| self.module.get_function("hsh_task_wait"));
                           if let Some(wfn) = wait_fn {
                               let call = self.call_coerced(
                                   wfn,
                                   &[task_ptr.into()],
                                   "await_result"
                               );
                               Ok(self.unwrap_call(call))
                           } else {
                               // hsh_task_wait not linked yet — fall back to passthrough
                               // (handles synchronous callers gracefully)
                               Ok(task_ptr)
                           }
                       }
                       Expr::Range(start, _, _, _) => self.expr(start, hint),
                       Expr::SelfExpr(span) => {
                           self.vars.get("self").map(|&(ptr, ty)|
                           self.builder.build_load(ty, ptr, "self").unwrap()
                           ).ok_or(CodegenError::UndefinedVar { name: "self".into(), span: span.clone() })
                       }
                       // ── ArrayLit [] ──────────────────────────────────
                       Expr::ArrayLit(items, _) => {
                           // Allocate a new HshArray and push each item.
                           let new_call = self.call_coerced(
                               self.builtins.hsh_array_new, &[], "arr");
                           let mut arr = self.unwrap_call(new_call);
                           for item in items {
                               let v = self.expr(item, None)?;
                               let push = self.call_coerced(
                                   self.builtins.hsh_array_push,
                                   &[arr.into(), v.into()], "ap");
                               arr = self.unwrap_call(push);
                           }
                           Ok(arr)
                       }

                       // ── IndexAccess arr[idx] ──────────────────────────
                       Expr::IndexAccess(arr_e, idx_e, _) => {
                           let arr = self.expr(arr_e, None)?;
                           let idx = self.expr(idx_e, None)?;
                           let call = self.call_coerced(
                               self.builtins.hsh_array_get,
                               &[arr.into(), idx.into()], "aget");
                           let raw = self.unwrap_call(call);
                           // BUG FIX: this used to return `raw` straight
                           // from `hsh_array_get` — which, exactly like
                           // `hsh_struct_get` (see the `FieldAccess` fix
                           // just below), always hands back a generic
                           // boxed `i64` slot regardless of the array's
                           // real element type. `for_stmt`'s array-loop
                           // already had to solve this exact problem (see
                           // `array_elem_llvm_ty` below) to unbox each
                           // element correctly — this is the same fix,
                           // applied to a plain `arr[i]` *expression*
                           // (not just the implicit unboxing inside a
                           // `for x in arr` loop). Without it, `arr[i]`
                           // for a `[string]` came back looking like a
                           // bare integer with no LLVM-level indication it
                           // was ever a pointer: `"prefix " + arr[i]`
                           // landed in `binop`'s int+int (or mismatched)
                           // arm instead of the pointer+pointer
                           // `hsh_strcat` arm, silently producing garbage
                           // or an empty string instead of a crash — the
                           // exact bug behind `translations::get()`
                           // always returning what looked like an empty
                           // value in `hacker_hsharp`/`bytes_final`.
                           let elem_ty: Option<BasicTypeEnum> = self.infer_array_elem_llvm_ty(arr_e);
                           match elem_ty {
                               Some(target) => Ok(self.coerce_basic_value(raw, target)),
                               None => Ok(raw),
                           }
                       }

                       // ── FieldAccess expr.field ─────────────────────────
                       Expr::FieldAccess(obj_e, field_name, span) => {
                           let obj = self.expr(obj_e, None)?;
                           let (field_idx, field_ty): (usize, Option<TypeExpr>) = match self.infer_struct_name(obj_e) {
                               Some(struct_name) => {
                                   let idx = self.resolve_struct_field_index(&struct_name, field_name);
                                   let ty = self.structs.get(&struct_name)
                                       .and_then(|fields| fields.iter().find(|f| &f.name == field_name))
                                       .map(|f| f.ty.clone());
                                   (idx, ty)
                               }
                               None => {
                                   // Couldn't statically determine the struct
                                   // type of `obj_e` (e.g. it's the result of
                                   // a function call, or a variable with no
                                   // type annotation we could track) — fall
                                   // back to the old heuristic of scanning
                                   // every struct for a matching field name.
                                   // This is a real ambiguity risk if two
                                   // structs share a field name at different
                                   // indices, so make sure it's visible
                                   // instead of failing silently.
                                   eprintln!(
                                       "warning: {}: cannot statically determine the struct type of `.{}` — guessing by scanning all structs for a matching field name; add a type annotation to avoid ambiguity if multiple structs share this field name",
                                       span, field_name
                                   );
                                   let mut found = 0usize;
                                   let mut found_ty: Option<TypeExpr> = None;
                                   'outer: for fields in self.structs.values() {
                                       for (i, f) in fields.iter().enumerate() {
                                           if &f.name == field_name {
                                               found = i;
                                               found_ty = Some(f.ty.clone());
                                               break 'outer;
                                           }
                                       }
                                   }
                                   (found, found_ty)
                               }
                           };
                           let idx_v = self.ctx.i64_type().const_int(field_idx as u64, false);
                           let call = self.call_coerced(
                               self.builtins.hsh_struct_get,
                               &[obj.into(), idx_v.into()], "fget");
                           let raw = self.unwrap_call(call);
                           // CRITICAL FIX: this used to just return `raw`
                           // directly — `hsh_struct_get` always returns a
                           // generic boxed `i64` slot (every H# struct
                           // field, whatever its real type, is stored as
                           // one i64-sized slot), so a field declared
                           // `string` (or `bytes`/an array/another
                           // struct — anything pointer-shaped) came back
                           // to the caller looking exactly like a plain
                           // number, with no LLVM-level indication it was
                           // ever meant to be a pointer. `binop()` (and
                           // everything else downstream) then had no way
                           // to tell `c.bold` apart from an actual
                           // integer field: `c.bold + "text"` silently
                           // did *raw integer addition* on two pointer
                           // values reinterpreted as numbers instead of
                           // calling `hsh_strcat`, producing a garbage
                           // "pointer" that was then handed to
                           // `println`/whatever used it — exactly the
                           // kind of silent, no-crash-just-wrong-output
                           // bug that's nearly impossible to notice from
                           // reading the source. Coercing to the field's
                           // real declared type here (same
                           // `coerce_basic_value` used for array-element
                           // unboxing) makes `c.bold` a genuine
                           // `PointerValue` again, so string concatenation
                           // and comparison on it go through the correct
                           // path from here on.
                           match field_ty.as_ref().and_then(|t| htype_to_llvm(self.ctx, t)) {
                               Some(target) => Ok(self.coerce_basic_value(raw, target)),
                               None => Ok(raw),
                           }
                       }

                       // ── StructLit Name { field: val, ... } ────────────
                       Expr::StructLit(name, fields, _) => {
                           let n_fields = self.get_struct_field_count(name);
                           let n_v = self.ctx.i64_type().const_int(n_fields as u64, false);
                           let new_call = self.call_coerced(
                               self.builtins.hsh_struct_new, &[n_v.into()], "snew");
                           let sptr = self.unwrap_call(new_call);
                           for (field_nm, val_e) in fields {
                               let idx = self.resolve_struct_field_index(name, field_nm);
                               let val = self.expr(val_e, None)?;
                               let idx_v = self.ctx.i64_type().const_int(idx as u64, false);
                               let set_call = self.call_coerced(
                                   self.builtins.hsh_struct_set,
                                   &[sptr.into(), idx_v.into(), val.into()], "fset");
                               let _ = set_call;
                           }
                           Ok(sptr)
                       }

                       // ── Match expr is pat => body ──────────────────────
                       // Lowered to an if-else chain comparing the subject.
                       Expr::Match { subject, arms, .. } => {
                           self.compile_match(subject, arms, hint)
                       }

                       // ── TupleLit (a, b, ...) ───────────────────────────
                       Expr::TupleLit(items, _) => {
                           // Tuple = HshArray of values
                           let new_call = self.call_coerced(
                               self.builtins.hsh_array_new, &[], "tup");
                           let mut arr = self.unwrap_call(new_call);
                           for item in items {
                               let v = self.expr(item, None)?;
                               let push = self.call_coerced(
                                   self.builtins.hsh_array_push,
                                   &[arr.into(), v.into()], "tp");
                               arr = self.unwrap_call(push);
                           }
                           Ok(arr)
                       }

                       // ── MethodCall obj.method(args) ────────────────────
                       Expr::MethodCall(obj_e, method, method_args, _) => {
                           let obj = self.expr(obj_e, None)?;
                           // Dispatch common methods on the object's type
                           match method.as_str() {
                               // Array methods
                               "push" | "append" => {
                                   let v = self.expr(&method_args[0], None)?;
                                   let call = self.call_coerced(
                                       self.builtins.hsh_array_push,
                                       &[obj.into(), v.into()], "mpush");
                                   Ok(self.unwrap_call(call))
                               }
                               "len" | "length" | "count" => {
                                   let call = self.call_coerced(
                                       self.builtins.hsh_array_len, &[obj.into()], "mlen");
                                   Ok(self.unwrap_call(call))
                               }
                               "get" => {
                                   let i = self.expr(&method_args[0], None)?;
                                   let call = self.call_coerced(
                                       self.builtins.hsh_array_get,
                                       &[obj.into(), i.into()], "mget");
                                   Ok(self.unwrap_call(call))
                               }
                               // String methods
                               "to_upper" | "upper" => {
                                   let call = self.call_coerced(
                                       self.builtins.hsh_to_upper, &[obj.into()], "mup");
                                   Ok(self.unwrap_call(call))
                               }
                               "to_lower" | "lower" => {
                                   let call = self.call_coerced(
                                       self.builtins.hsh_to_lower, &[obj.into()], "mlo");
                                   Ok(self.unwrap_call(call))
                               }
                               "trim" => {
                                   let call = self.call_coerced(
                                       self.builtins.hsh_trim, &[obj.into()], "mtr");
                                   Ok(self.unwrap_call(call))
                               }
                               _ => {
                                   // Unknown method — try as a function call f(obj, args...)
                                   let mut _all_args = vec![obj];
                                   for a in method_args {
                                       _all_args.push(self.expr(a, None)?);
                                   }
                                   let _name_slug = format!("{}_{}", "obj", method);
                                   // method dispatch: call as module_method(obj, args...)
                                   // Since call_fn takes &[Expr], just return zero for now
                                   Ok(self.ctx.i64_type().const_zero().into())
                               }
                           }
                       }
                       // ── Do (bare `is ... end` block used as an expression) ──
                       // Previously fell through to the catch-all below —
                       // meaning the body was never compiled at all, just
                       // silently discarded. Runs its statements for
                       // side effects; a `do` block doesn't have a
                       // "tail expression is the value" convention
                       // anywhere else in this codegen (If/While used as
                       // statements discard their value the same way), so
                       // it yields zero, consistently.
                       Expr::Do { body, .. } => {
                           self.enter_branch();
                           self.stmts(body)?;
                           self.exit_branch();
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       // ── Unsafe (`unsafe [arena(...)|manual(...)] is ... end`) ──
                       // Also previously fell through to the catch-all —
                       // an `unsafe arena(...)` block's body was *never
                       // compiled*, the whole thing silently vanished.
                       Expr::Unsafe(body, config, _) => {
                           match config.as_ref().map(|c| &c.mode) {
                               Some(UnsafeMode::Arena { size, kind }) => {
                                   // Same bump-allocator trick as `@arena`
                                   // on a function, just scoped to this
                                   // block: push a fresh arena, run the
                                   // body, pop and free it. `kind` (Fixed/
                                   // Pool/Page/Ring/General) is threaded
                                   // through to `hsh_arena_new_kind` now —
                                   // previously it was parsed and then
                                   // discarded (`{ size, .. }`), so every
                                   // kind silently behaved like General.
                                   //
                                   // KNOWN LIMITATION (documented, not
                                   // silently unsafe): if the body assigns
                                   // an arena-backed value — a freshly
                                   // built string/array/struct — into a
                                   // variable declared *outside* this
                                   // block, that variable is left holding
                                   // a dangling pointer once the arena is
                                   // freed here. This basic version does
                                   // not track that (a real fix needs
                                   // escape analysis on assignments, not
                                   // just return values like the
                                   // function-level `@arena` case
                                   // handles). Only rely on this for
                                   // values that stay inside the block.
                                   let cap = size.map(|s| s as u64).unwrap_or(1024 * 1024);
                                   let cap_v = self.ctx.i64_type().const_int(cap, false);
                                   let kind_tag: u64 = match kind {
                                       ArenaKind::General => 0,
                                       ArenaKind::Fixed   => 1,
                                       ArenaKind::Pool    => 2,
                                       ArenaKind::Page    => 3,
                                       ArenaKind::Ring    => 4,
                                   };
                                   let kind_v = self.ctx.i64_type().const_int(kind_tag, false);
                                   let arena = self.call_coerced(self.builtins.hsh_arena_new_kind, &[cap_v.into(), kind_v.into()], "blk_arena");
                                   let arena_val = self.unwrap_call(arena);
                                   self.call_coerced(self.builtins.hsh_arena_push_current, &[arena_val], "");
                                   self.enter_branch();
                                   self.stmts(body)?;
                                   self.exit_branch();
                                   let popped = self.call_coerced(self.builtins.hsh_arena_pop_current, &[], "popped_blk_arena");
                                   let popped_val = self.unwrap_call(popped);
                                   self.call_coerced(self.builtins.hsh_arena_free, &[popped_val], "");
                                   Ok(self.ctx.i64_type().const_zero().into())
                               }
                               // `manual(...)` / bare `unsafe is ... end` (Raw) / no
                               // config at all: no special memory strategy is
                               // wired up for these yet — but the body now
                               // actually compiles and runs, which it
                               // didn't before at all.
                               Some(UnsafeMode::Manual(_)) | Some(UnsafeMode::Raw) | None => {
                                   self.enter_branch();
                                   self.stmts(body)?;
                                   self.exit_branch();
                                   Ok(self.ctx.i64_type().const_zero().into())
                               }
                           }
                       }
                       _ => Ok(self.ctx.i64_type().const_zero().into()),
                   }
               }

               fn literal(&mut self, lit: &Literal, hint: Option<BasicTypeEnum<'ctx>>) -> R<BasicValueEnum<'ctx>> {
                   Ok(match lit {
                       Literal::Int(n) => {
                           let t = match hint { Some(BasicTypeEnum::IntType(t)) => t, _ => self.ctx.i64_type() };
                           t.const_int(*n as u64, true).into()
                       }
                       Literal::Float(f) => {
                           let t = match hint { Some(BasicTypeEnum::FloatType(t)) => t, _ => self.ctx.f64_type() };
                           t.const_float(*f).into()
                       }
                       Literal::Bool(b)  => self.ctx.i8_type().const_int(if *b { 1 } else { 0 }, false).into(),
                      Literal::Nil      => self.ctx.i64_type().const_zero().into(),
                      Literal::String(s) => {
                          if let Some(&g) = self.str_globals.get(s.as_str()) {
                              g.into()
                          } else {
                              let gs = self.builder.build_global_string_ptr(s, ".str").unwrap();
                              let p  = gs.as_pointer_value();
                              self.str_globals.insert(s.clone(), p);
                              p.into()
                          }
                      }
                      Literal::Interpolated(parts) => {
                          let empty = self.builder.build_global_string_ptr("", ".istart").unwrap().as_pointer_value();
                          let mut acc: BasicValueEnum = empty.into();
                          for part in parts {
                              let pv: BasicValueEnum = match part {
                                  hsharp_parser::ast::InterpPart::Text(t) => {
                                      self.builder.build_global_string_ptr(t.as_str(), ".itext").unwrap()
                                      .as_pointer_value().into()
                                  }
                                  hsharp_parser::ast::InterpPart::Expr(e) => {
                                      let v  = self.expr(e, None)?;
                                      let iv = self.value_to_i64_bits(v);
                                      let r  = self.call_coerced(
                                          self.builtins.hsh_val_to_str, &[iv.into()], "its");
                                          self.unwrap_call(r).into()
                                  }
                              };
                              let r = self.call_coerced(
                                  self.builtins.hsh_strcat, &[acc.into(), pv.into()], "cat");
                                  acc = self.unwrap_call(r).into();
                          }
                          acc
                      }
                      Literal::Bytes(_) => self.ctx.i64_type().const_zero().into(),
                   })
               }

               fn call_fn(&mut self, name: &str, args: &[Expr], _hint: Option<BasicTypeEnum<'ctx>>, call_span: &Span) -> R<BasicValueEnum<'ctx>> {
                   // A user-defined H# function always shadows a built-in of the
                   // same name — otherwise `fn len(...)`/`fn print(...)`/etc. in
                   // user code would be silently unreachable forever, since the
                   // big `match name { ... }` below used to run unconditionally
                   // before we ever checked `func_vals`.
                   if let Some(&fv) = self.func_vals.get(name) {
                       return self.call_user_fn(fv, args, name);
                   }
                   let i8ptr = self.ctx.ptr_type(AddressSpace::default());
                   macro_rules! str_arg {
                       ($i:expr) => {
                           if let Some(a) = args.get($i) { self.expr(a, Some(i8ptr.into()))? }
                           else { self.builder.build_global_string_ptr("", ".empty").unwrap().as_pointer_value().into() }
                       }
                   }
                   macro_rules! call1 {
                       ($f:expr, $name:expr) => {{ let a = str_arg!(0); let r = self.call_coerced($f, &[a.into()], $name); Ok(self.unwrap_call(r)) }}
                   }
                   macro_rules! call2 {
                       ($f:expr, $name:expr) => {{ let a = str_arg!(0); let b = str_arg!(1); let r = self.call_coerced($f, &[a.into(), b.into()], $name); Ok(self.unwrap_call(r)) }}
                   }
                   macro_rules! call3 {
                       ($f:expr, $name:expr) => {{ let a = str_arg!(0); let b = str_arg!(1); let c = str_arg!(2); let r = self.call_coerced($f, &[a.into(), b.into(), c.into()], $name); Ok(self.unwrap_call(r)) }}
                   }
                   match name {
                       "write" | "writeln" | "println" => {
                           let a = str_arg!(0);
                           self.call_coerced(self.builtins.hsh_println, &[a.into()], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "print" => {
                           let a = str_arg!(0);
                           self.call_coerced(self.builtins.hsh_print, &[a.into()], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "to_string" => {
                           let a = if let Some(e) = args.first() { self.expr(e, None)? }
                           else { self.ctx.i64_type().const_zero().into() };
                           let iv = self.value_to_i64_bits(a);
                           let r = self.call_coerced(self.builtins.hsh_val_to_str, &[iv.into()], "ts");
                           Ok(self.unwrap_call(r))
                       }
                       "len" => {
                           let a = str_arg!(0);
                           let r = self.call_coerced(self.builtins.hsh_strlen, &[a.into()], "len");
                           Ok(self.unwrap_call(r))
                       }
                       "panic" => {
                           let a = str_arg!(0);
                           self.call_coerced(self.builtins.hsh_panic, &[a.into()], "");
                           self.builder.build_unreachable().unwrap();
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "exit" => {
                           let code = if let Some(e) = args.first() {
                               let v = self.expr(e, Some(self.ctx.i32_type().into()))?;
                               match v { BasicValueEnum::IntValue(i) => i, _ => self.ctx.i32_type().const_zero() }
                           } else { self.ctx.i32_type().const_zero() };
                           // Declare libc exit(i32) -> void locally (not part of LlvmBuiltins)
                           let exit_fn = self.module.get_function("exit").unwrap_or_else(|| {
                               let sig = self.ctx.void_type().fn_type(&[self.ctx.i32_type().into()], false);
                               self.module.add_function("exit", sig, Some(inkwell::module::Linkage::External))
                           });
                           self.call_coerced(exit_fn, &[code.into()], "");
                           self.builder.build_unreachable().unwrap();
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "shell" | "cmd" => call1!(self.builtins.hsh_shell, "sh"),
                       // ── §0 SECURITY: shell-injection mitigations ──────────────────
                       "shell_escape" | "shquote" => call1!(self.builtins.hsh_shell_escape, "shq"),
                       // exec(cmd[,a1[,a2[,a3]]]) — direct fork+execve, no shell.
                       // Resolved by call arity to hsh_exec1..4.
                       "exec" => match args.len() {
                           0 | 1 => call1!(self.builtins.hsh_exec1, "exec1"),
                           2     => call2!(self.builtins.hsh_exec2, "exec2"),
                           3     => call3!(self.builtins.hsh_exec3, "exec3"),
                           _     => {
                               let a = str_arg!(0); let b = str_arg!(1); let c = str_arg!(2); let d = str_arg!(3);
                               let r = self.call_coerced(self.builtins.hsh_exec4, &[a.into(), b.into(), c.into(), d.into()], "exec4");
                               Ok(self.unwrap_call(r))
                           }
                       },
                       // extern [python, "mod"] phase-1 bridge (manual py_eval calls)
                       "py_eval" => call1!(self.builtins.hsh_py_eval, "pyeval"),
                       "trim" | "str_trim" => call1!(self.builtins.hsh_trim, "trim"),
                       "to_lower" | "lower" => call1!(self.builtins.hsh_to_lower, "lower"),
                       "to_upper" | "upper" => call1!(self.builtins.hsh_to_upper, "upper"),
                       "contains" | "str_contains" => call2!(self.builtins.hsh_str_contains, "cont"),
                       "starts_with" => call2!(self.builtins.hsh_starts_with, "startsw"),
                       "ends_with"   => call2!(self.builtins.hsh_ends_with, "endsw"),
                       "replace" | "str_replace" => call3!(self.builtins.hsh_str_replace, "replace"),
                       "fs_write" | "write_file" | "file_write" => call2!(self.builtins.hsh_write_file, "fw"),
                       "fs_read"  | "read_file" | "file_read" => call1!(self.builtins.hsh_read_file, "fr"),
                       "file_exists" | "fs_exists" => call1!(self.builtins.hsh_file_exists, "fexists"),
                       "fs_mkdir_all" | "mkdir_all" => call1!(self.builtins.hsh_mkdir_all, "mkdirall"),
                       "file_size_bytes" | "file_size" => call1!(self.builtins.hsh_file_size, "fsize"),
                       "is_dir" => call1!(self.builtins.hsh_is_dir, "isdir"),
                       "bold"        => call1!(self.builtins.hsh_bold, "bold"),
                       "green_text" | "green" => call1!(self.builtins.hsh_green_text, "grn"),
                       "red_text"   | "red"   => call1!(self.builtins.hsh_red_text, "red"),
                       "yellow_text"| "yellow"=> call1!(self.builtins.hsh_yellow_text, "yel"),
                       "dim_text"   | "dim"   => call1!(self.builtins.hsh_dim_text, "dim"),
                       "cyan_text"  | "cyan"  => call1!(self.builtins.hsh_cyan_text, "cyn"),
                       // ── Random / crypto ────────────────────────────────────────────
                       "random_hex" => {
                           let n = if let Some(e) = args.first() { self.expr(e, Some(self.ctx.i64_type().into()))? }
                           else { self.ctx.i64_type().const_int(8, false).into() };
                           let r = self.call_coerced(self.builtins.hsh_random_hex, &[n.into()], "rndhex");
                           Ok(self.unwrap_call(r))
                       }
                       "random_string" => {
                           let n = if let Some(e) = args.first() { self.expr(e, Some(self.ctx.i64_type().into()))? }
                           else { self.ctx.i64_type().const_int(8, false).into() };
                           let r = self.call_coerced(self.builtins.hsh_random_string, &[n.into()], "rndstr");
                           Ok(self.unwrap_call(r))
                       }
                       "random_int" => {
                           let lo = if let Some(e) = args.first() { self.expr(e, Some(self.ctx.i64_type().into()))? } else { self.ctx.i64_type().const_zero().into() };
                           let hi = if let Some(e) = args.get(1)  { self.expr(e, Some(self.ctx.i64_type().into()))? } else { self.ctx.i64_type().const_int(100, false).into() };
                           let r = self.call_coerced(self.builtins.hsh_random_int, &[lo.into(), hi.into()], "rndint");
                           Ok(self.unwrap_call(r))
                       }
                       "uuid_v4" | "new_uuid" => {
                           let r = self.call_coerced(self.builtins.hsh_uuid_v4, &[], "uuid");
                           Ok(self.unwrap_call(r))
                       }
                       // ── Regex (§11 — PCRE2) ────────────────────────────────────────
                       "regex_match" => {
                           let a = str_arg!(0); let b = str_arg!(1);
                           let r = self.call_coerced(self.builtins.hsh_regex_match, &[a.into(), b.into()], "rxmatch");
                           Ok(self.unwrap_call(r))
                       }
                       "regex_find"    => call2!(self.builtins.hsh_regex_find, "rxfind"),
                       "regex_replace" => call3!(self.builtins.hsh_regex_replace, "rxrepl"),
                       // ── SQLite (§12 — real libsqlite3, prepared statements) ────────
                       "sqlite_open"  => call1!(self.builtins.hsh_sqlite_open, "dbopen"),
                       "sqlite_exec"  => call2!(self.builtins.hsh_sqlite_exec, "dbexec"),
                       "sqlite_query" => call2!(self.builtins.hsh_sqlite_query, "dbquery"),
                       "sqlite_close" => {
                           let a = str_arg!(0);
                           self.call_coerced(self.builtins.hsh_sqlite_close, &[a.into()], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       // db_query_bind(db, sql, b1[, b2[, b3]]) — parameterized
                       // queries, SQL-injection-safe by construction (§12). Resolved
                       // by arity (3-5 args -> bind1/2/3) like exec()->exec1..4.
                       "db_query_bind" => match args.len() {
                           0 | 1 | 2 | 3 => call3!(self.builtins.hsh_sqlite_query_bind1, "dbbind1"),
                           4 => {
                               let a = str_arg!(0); let b = str_arg!(1); let c = str_arg!(2); let d = str_arg!(3);
                               let r = self.call_coerced(self.builtins.hsh_sqlite_query_bind2, &[a.into(), b.into(), c.into(), d.into()], "dbbind2");
                               Ok(self.unwrap_call(r))
                           }
                           _ => {
                               let a = str_arg!(0); let b = str_arg!(1); let c = str_arg!(2); let d = str_arg!(3); let f5 = str_arg!(4);
                               let r = self.call_coerced(self.builtins.hsh_sqlite_query_bind3, &[a.into(), b.into(), c.into(), d.into(), f5.into()], "dbbind3");
                               Ok(self.unwrap_call(r))
                           }
                       },
                       // ── Network ─────────────────────────────────────────────────────
                       "dns_resolve" => call1!(self.builtins.hsh_dns_resolve, "dns"),
                       "http_get"    => call1!(self.builtins.hsh_http_get, "httpget"),
                       "http_post"   => call2!(self.builtins.hsh_http_post, "httppost"),
                       "json_get"    => call2!(self.builtins.hsh_json_get, "jsonget"),
                       "scan_port" => {
                           let host = str_arg!(0);
                           let port = if let Some(e) = args.get(1) { self.expr(e, Some(self.ctx.i64_type().into()))? } else { self.ctx.i64_type().const_zero().into() };
                           let timeout = if let Some(e) = args.get(2) { self.expr(e, Some(self.ctx.i64_type().into()))? } else { self.ctx.i64_type().const_int(500, false).into() };
                           let r = self.call_coerced(self.builtins.hsh_scan_port, &[host.into(), port.into(), timeout.into()], "scanport");
                           Ok(self.unwrap_call(r))
                       }
                       // ── Dynamic array builtins ──────────────────────────
                       "array_push" => {
                           let arr = self.expr(&args[0], None)?;
                           let val = self.expr(&args[1], None)?;
                           let call = self.call_coerced(
                               self.builtins.hsh_array_push,
                               &[arr.into(), val.into()], "arr_push");
                           Ok(self.unwrap_call(call))
                       }
                       "array_pop" => {
                           let arr = self.expr(&args[0], None)?;
                           let n = self.call_coerced(self.builtins.hsh_array_len, &[arr.into()], "al");
                           let nl = self.unwrap_call(n);
                           let one = self.ctx.i64_type().const_int(1, false);
                           let last_idx = self.builder.build_int_sub(nl.into_int_value(), one, "li").unwrap();
                           let call = self.call_coerced(self.builtins.hsh_array_get, &[arr.into(), last_idx.into()], "ag");
                           Ok(self.unwrap_call(call))
                       }
                       "array_len" | "array_count" => {
                           let arr = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_array_len, &[arr.into()], "alen");
                           Ok(self.unwrap_call(call))
                       }
                       "array_get" => {
                           let arr = self.expr(&args[0], None)?;
                           let idx = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_array_get, &[arr.into(), idx.into()], "aget");
                           Ok(self.unwrap_call(call))
                       }
                       "array_set" => {
                           let arr = self.expr(&args[0], None)?;
                           let idx = self.expr(&args[1], None)?;
                           let val = self.expr(&args[2], None)?;
                           let call = self.call_coerced(self.builtins.hsh_array_set, &[arr.into(), idx.into(), val.into()], "aset");
                           Ok(self.unwrap_call(call))
                       }
                       "array_contains" => {
                           let arr = self.expr(&args[0], None)?;
                           let val = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_array_contains, &[arr.into(), val.into()], "ahas");
                           Ok(self.unwrap_call(call))
                       }
                       "array_new" => {
                           let call = self.call_coerced(self.builtins.hsh_array_new, &[], "anew");
                           Ok(self.unwrap_call(call))
                       }
                       "array_concat" => {
                           let a = self.expr(&args[0], None)?;
                           let b = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_array_concat, &[a.into(), b.into()], "acat");
                           Ok(self.unwrap_call(call))
                       }
                       // ── env::args ────────────────────────────────────────
                       "env_args" => {
                           let call = self.call_coerced(self.builtins.hsh_env_args, &[], "args");
                           Ok(self.unwrap_call(call))
                       }
                       // ── Struct helpers ───────────────────────────────────
                       "hsh_struct_new" => {
                           let n = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_struct_new, &[n.into()], "snew");
                           Ok(self.unwrap_call(call))
                       }
                       "hsh_struct_get" => {
                           let s = self.expr(&args[0], None)?;
                           let i = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_struct_get, &[s.into(), i.into()], "sget");
                           Ok(self.unwrap_call(call))
                       }
                       "hsh_struct_set" => {
                           let s = self.expr(&args[0], None)?;
                           let i = self.expr(&args[1], None)?;
                           let v = self.expr(&args[2], None)?;
                           let call = self.call_coerced(self.builtins.hsh_struct_set, &[s.into(), i.into(), v.into()], "sset");
                           Ok(self.unwrap_call(call))
                       }
                       // ── Extra string helpers ─────────────────────────────
                       "string_split" => {
                           let s = self.expr(&args[0], None)?;
                           let sep = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_split, &[s.into(), sep.into()], "sspl");
                           Ok(self.unwrap_call(call))
                       }
                       "string_find" => {
                           let s = self.expr(&args[0], None)?;
                           let n = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_find, &[s.into(), n.into()], "sfnd");
                           Ok(self.unwrap_call(call))
                       }
                       "string_rfind" => {
                           let s = self.expr(&args[0], None)?;
                           let n = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_rfind, &[s.into(), n.into()], "srfnd");
                           Ok(self.unwrap_call(call))
                       }
                       "string_slice" => {
                           let s = self.expr(&args[0], None)?;
                           let a = self.expr(&args[1], None)?;
                           let b = self.expr(&args[2], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_slice, &[s.into(), a.into(), b.into()], "sslc");
                           Ok(self.unwrap_call(call))
                       }
                       "string_at" => {
                           let s = self.expr(&args[0], None)?;
                           let i = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_at, &[s.into(), i.into()], "sat");
                           Ok(self.unwrap_call(call))
                       }
                       "string_pad_right" => {
                           let s = self.expr(&args[0], None)?;
                           let w = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_pad_right, &[s.into(), w.into()], "spr");
                           Ok(self.unwrap_call(call))
                       }
                       "string_repeat" => {
                           let s = self.expr(&args[0], None)?;
                           let n = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_repeat, &[s.into(), n.into()], "srpt");
                           Ok(self.unwrap_call(call))
                       }
                       "string_trim_right" => {
                           let s = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_trim_right, &[s.into()], "str");
                           Ok(self.unwrap_call(call))
                       }
                       "to_int" => {
                           let s = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_to_int, &[s.into()], "toi");
                           Ok(self.unwrap_call(call))
                       }
                       "to_int_from_hex" => {
                           let s = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_to_int_from_hex, &[s.into()], "toih");
                           Ok(self.unwrap_call(call))
                       }
                       // ── @arc basic v2 ────────────────────────────────────
                       // `arc_alloc` actually allocates a refcounted block
                       // (see core.c's hsh_rc_alloc) — previously that
                       // runtime function was declared but never called
                       // from anywhere, so there was no way to get an
                       // arc-managed pointer at all. `arc_retain`/
                       // `arc_release`/`arc_count` remain directly callable
                       // too (e.g. for a pointer that came from elsewhere),
                       // but plain `let x = arc_alloc(n)` / `let y = x`
                       // bindings inside an `@arc` function are now also
                       // retained/released *automatically* — see the
                       // `Stmt::Let` arm of `stmt()` and
                       // `emit_arc_epilogue`. The typechecker (see
                       // `typechecker.rs`) restricts these four builtins to
                       // `@arc` functions and `unsafe ... end` blocks — they
                       // used to be callable from any function regardless
                       // of its `@` annotation, which made the annotation
                       // purely decorative.
                       "arc_alloc" => {
                           let n = self.expr(&args[0], Some(self.ctx.i64_type().into()))?;
                           let call = self.call_coerced(self.builtins.hsh_rc_alloc, &[n], "arcalloc");
                           Ok(self.unwrap_call(call))
                       }
                       "arc_retain" => {
                           let p = self.expr(&args[0], None)?;
                           self.call_coerced(self.builtins.hsh_rc_retain, &[p], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "arc_release" => {
                           let p = self.expr(&args[0], None)?;
                           self.call_coerced(self.builtins.hsh_rc_release, &[p], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "arc_count" => {
                           let p = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_rc_count, &[p], "rcc");
                           Ok(self.unwrap_call(call))
                       }
                       // ── @arc weak references ──────────────────────────────
                       // See core.c's hsh_arc_downgrade/_upgrade doc
                       // comment: `arc_upgrade` returns the same kind of
                       // nilable pointer `arc_alloc` does (nil = the
                       // object's strong count already hit zero), so
                       // check it the same way you'd check any other
                       // `nil`-able value before dereferencing.
                       "arc_downgrade" => {
                           let p = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_arc_downgrade, &[p], "weak");
                           Ok(self.unwrap_call(call))
                       }
                       "arc_upgrade" => {
                           let p = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_arc_upgrade, &[p], "strong");
                           Ok(self.unwrap_call(call))
                       }
                       "arc_weak_release" => {
                           let p = self.expr(&args[0], None)?;
                           self.call_coerced(self.builtins.hsh_arc_weak_release, &[p], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "arc_weak_count" => {
                           let p = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_arc_weak_count, &[p], "wc");
                           Ok(self.unwrap_call(call))
                       }
                       // ── @pointers basic v2: raw, unchecked memory access ─
                       // at every common width, plus f32/f64/ptr — see
                       // core.c's hsh_ptr_{read,write}_* for the actual
                       // load/store. All of these, and the four `arc_*`
                       // builtins above, are gated by the typechecker to
                       // `@pointers`/`@arc` functions (or an
                       // `unsafe ... end` block) — see typechecker.rs.
                       "ptr_read_i64" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let call = self.call_coerced(self.builtins.hsh_ptr_read_i64, &[p, off], "pread");
                           Ok(self.unwrap_call(call))
                       }
                       "ptr_write_i64" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let val = self.expr(&args[2], Some(self.ctx.i64_type().into()))?;
                           self.call_coerced(self.builtins.hsh_ptr_write_i64, &[p, off, val], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "ptr_read_i32" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let call = self.call_coerced(self.builtins.hsh_ptr_read_i32, &[p, off], "pread32");
                           Ok(self.unwrap_call(call))
                       }
                       "ptr_write_i32" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let val = self.expr(&args[2], Some(self.ctx.i64_type().into()))?;
                           self.call_coerced(self.builtins.hsh_ptr_write_i32, &[p, off, val], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "ptr_read_i16" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let call = self.call_coerced(self.builtins.hsh_ptr_read_i16, &[p, off], "pread16");
                           Ok(self.unwrap_call(call))
                       }
                       "ptr_write_i16" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let val = self.expr(&args[2], Some(self.ctx.i64_type().into()))?;
                           self.call_coerced(self.builtins.hsh_ptr_write_i16, &[p, off, val], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "ptr_read_i8" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let call = self.call_coerced(self.builtins.hsh_ptr_read_i8, &[p, off], "pread8");
                           Ok(self.unwrap_call(call))
                       }
                       "ptr_write_i8" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let val = self.expr(&args[2], Some(self.ctx.i64_type().into()))?;
                           self.call_coerced(self.builtins.hsh_ptr_write_i8, &[p, off, val], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "ptr_read_f64" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let call = self.call_coerced(self.builtins.hsh_ptr_read_f64, &[p, off], "preadf64");
                           Ok(self.unwrap_call(call))
                       }
                       "ptr_write_f64" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let val = self.expr(&args[2], Some(self.ctx.f64_type().into()))?;
                           self.call_coerced(self.builtins.hsh_ptr_write_f64, &[p, off, val], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "ptr_read_f32" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let call = self.call_coerced(self.builtins.hsh_ptr_read_f32, &[p, off], "preadf32");
                           Ok(self.unwrap_call(call))
                       }
                       "ptr_write_f32" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let val = self.expr(&args[2], Some(self.ctx.f64_type().into()))?;
                           self.call_coerced(self.builtins.hsh_ptr_write_f32, &[p, off, val], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "ptr_read_ptr" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let call = self.call_coerced(self.builtins.hsh_ptr_read_ptr, &[p, off], "preadp");
                           Ok(self.unwrap_call(call))
                       }
                       "ptr_write_ptr" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let val = self.expr(&args[2], None)?;
                           self.call_coerced(self.builtins.hsh_ptr_write_ptr, &[p, off, val], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "ptr_is_null" => {
                           let p = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_ptr_is_null, &[p], "pnull");
                           Ok(self.unwrap_call(call))
                       }
                       "ptr_add" => {
                           let p   = self.expr(&args[0], None)?;
                           let off = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let call = self.call_coerced(self.builtins.hsh_ptr_add, &[p, off], "padd");
                           Ok(self.unwrap_call(call))
                       }
                       // ── @pointers basic v3 ────────────────────────────────
                       // Fills the gaps basic v2 left: no way to check a
                       // pointer's allocation size, no bulk copy/compare.
                       // See core.c's hsh_ptr_alloc_size/_copy/_compare.
                       "ptr_alloc_size" => {
                           let p = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_ptr_alloc_size, &[p], "pallocsz");
                           Ok(self.unwrap_call(call))
                       }
                       "ptr_copy" => {
                           let dst = self.expr(&args[0], None)?;
                           let src = self.expr(&args[1], None)?;
                           let n   = self.expr(&args[2], Some(self.ctx.i64_type().into()))?;
                           self.call_coerced(self.builtins.hsh_ptr_copy, &[dst, src, n], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "ptr_compare" => {
                           let a = self.expr(&args[0], None)?;
                           let b = self.expr(&args[1], None)?;
                           let n = self.expr(&args[2], Some(self.ctx.i64_type().into()))?;
                           let call = self.call_coerced(self.builtins.hsh_ptr_compare, &[a, b, n], "pcmp");
                           Ok(self.unwrap_call(call))
                       }
                       "ptr_fill" => {
                           let p   = self.expr(&args[0], None)?;
                           let val = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let n   = self.expr(&args[2], Some(self.ctx.i64_type().into()))?;
                           self.call_coerced(self.builtins.hsh_ptr_fill, &[p, val, n], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "ptr_zero" => {
                           let p = self.expr(&args[0], None)?;
                           let n = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           self.call_coerced(self.builtins.hsh_ptr_zero, &[p, n], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       // ── @arena basic v2 — checkpoint/rewind + stats ──────
                       // Reuse part of a longer-lived arena's lifetime for
                       // a burst of temporary allocations without
                       // freeing the whole arena — see core.c's
                       // hsh_arena_checkpoint/_rewind doc comment. All
                       // operate on whichever arena is currently active
                       // (same as every other arena-aware allocator);
                       // harmless no-ops outside any arena.
                       "arena_checkpoint" => {
                           let call = self.call_coerced(self.builtins.hsh_arena_checkpoint, &[], "ckpt");
                           Ok(self.unwrap_call(call))
                       }
                       "arena_rewind" => {
                           let mark = self.expr(&args[0], Some(self.ctx.i64_type().into()))?;
                           self.call_coerced(self.builtins.hsh_arena_rewind, &[mark], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "arena_used" => {
                           let call = self.call_coerced(self.builtins.hsh_arena_used, &[], "aused");
                           Ok(self.unwrap_call(call))
                       }
                       "arena_capacity" => {
                           let call = self.call_coerced(self.builtins.hsh_arena_capacity, &[], "acap");
                           Ok(self.unwrap_call(call))
                       }
                       // ── @pointers basic v4 — opt-in bounds-checked ────────
                       // `hsh_panic`s on out-of-bounds instead of silently
                       // corrupting memory; only meaningful for arc_alloc
                       // pointers (see core.c's hsh_ptr_read_checked doc
                       // comment) — this is a safety net for the one case
                       // that's actually checkable, not a general one.
                       "ptr_read_checked" => {
                           let p      = self.expr(&args[0], None)?;
                           let offset = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let width  = self.expr(&args[2], Some(self.ctx.i64_type().into()))?;
                           let call = self.call_coerced(self.builtins.hsh_ptr_read_checked, &[p, offset, width], "predchk");
                           Ok(self.unwrap_call(call))
                       }
                       "ptr_write_checked" => {
                           let p      = self.expr(&args[0], None)?;
                           let offset = self.expr(&args[1], Some(self.ctx.i64_type().into()))?;
                           let width  = self.expr(&args[2], Some(self.ctx.i64_type().into()))?;
                           let val    = self.expr(&args[3], Some(self.ctx.i64_type().into()))?;
                           self.call_coerced(self.builtins.hsh_ptr_write_checked, &[p, offset, width, val], "");
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       // `ptr_field_offset(StructName, "field")` — unlike
                       // every other `ptr_*` builtin, this isn't wired to
                       // a core.c runtime function at all: it's a
                       // compile-time constant, computed here directly
                       // from `self.structs`' field layout, because its
                       // first argument is a *type name*, not a value —
                       // there's no way to answer "what's the byte offset
                       // of this field" at runtime without already
                       // knowing the struct type, which is exactly what
                       // this exists to avoid making callers re-derive by
                       // hand (previously: manually counting bytes).
                       "ptr_field_offset" => {
                           let struct_name = match &args[0] {
                               Expr::Ident(n, _) => n.clone(),
                               other => return Err(CodegenError::Llvm(format!(
                                   "ptr_field_offset's first argument must be a bare struct type name (e.g. `ptr_field_offset(MyStruct, \"field\")`), found {:?}", other
                               ))),
                           };
                           let field_name = match &args[1] {
                               Expr::Literal(Literal::String(s), _) => s.clone(),
                               other => return Err(CodegenError::Llvm(format!(
                                   "ptr_field_offset's second argument must be a string literal field name, found {:?}", other
                               ))),
                           };
                           let fields = self.structs.get(&struct_name).ok_or_else(|| CodegenError::Llvm(
                               format!("ptr_field_offset: unknown struct `{}`", struct_name)
                           ))?;
                           let mut offset: u64 = 0;
                           let mut found = false;
                           for f in fields.iter() {
                               let size = LlvmCodegen::field_natural_size(&f.ty);
                               offset = (offset + size - 1) / size * size; // natural alignment
                               if f.name == field_name { found = true; break; }
                               offset += size;
                           }
                           if !found {
                               return Err(CodegenError::Llvm(format!(
                                   "ptr_field_offset: struct `{}` has no field `{}`", struct_name, field_name
                               )));
                           }
                           Ok(self.ctx.i64_type().const_int(offset, false).into())
                       }
                       "to_float" => {
                           let s = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_to_float_fn, &[s.into()], "tof");
                           Ok(self.unwrap_call(call))
                       }
                       "proc_id" => {
                           let call = self.call_coerced(self.builtins.hsh_proc_id, &[], "pid");
                           Ok(self.unwrap_call(call))
                       }
                       "file_delete" => {
                           let p = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_file_delete, &[p.into()], "fdel");
                           Ok(self.unwrap_call(call))
                       }
                       "dir_create" => {
                           let p = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_dir_create, &[p.into()], "dcreat");
                           Ok(self.unwrap_call(call))
                       }
                       "dir_exists" => {
                           let p = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_dir_exists, &[p.into()], "dex");
                           Ok(self.unwrap_call(call))
                       }
                       "io_readline" => {
                           // Read a line from stdin — returns char* (heap allocated)
                           let getline_ty = self.ctx.ptr_type(inkwell::AddressSpace::default())
                               .fn_type(&[], false);
                           let getline_fn = self.module.get_function("hsh_readline")
                               .unwrap_or_else(|| self.module.add_function("hsh_readline", getline_ty, None));
                           let call = self.call_coerced(getline_fn, &[], "readline");
                           Ok(self.unwrap_call(call))
                       }
                       "io_print" => {
                           let s = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_print, &[s.into()], "iop");
                           Ok(self.unwrap_call(call))
                       }
                       "time_ms" => {
                           let call = self.call_coerced(self.builtins.hsh_now_ms, &[], "tms");
                           Ok(self.unwrap_call(call))
                       }

                       "string_chars" => {
                           let s = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_chars, &[s.into()], "schar");
                           Ok(self.unwrap_call(call))
                       }
                       "dir_remove_all" => {
                           let p = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_dir_remove_all, &[p.into()], "dra");
                           Ok(self.unwrap_call(call))
                       }
                       "bytes_to_string" => {
                           let b = self.expr(&args[0], None)?;
                           let n = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_bytes_to_string, &[b.into(), n.into()], "bts");
                           Ok(self.unwrap_call(call))
                       }
                       "string_to_bytes" => {
                           let s = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_to_bytes, &[s.into()], "stb");
                           Ok(self.unwrap_call(call))
                       }
                       "string_contains" | "string_contains_str" => {
                           let s = self.expr(&args[0], None)?;
                           let n = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_contains, &[s.into(), n.into()], "sc");
                           Ok(self.unwrap_call(call))
                       }
                       "string_replace" => {
                           let s = self.expr(&args[0], None)?;
                           let f = self.expr(&args[1], None)?;
                           let r = self.expr(&args[2], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_replace, &[s.into(), f.into(), r.into()], "sr");
                           Ok(self.unwrap_call(call))
                       }
                       "string_trim" => {
                           let s = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_trim, &[s.into()], "st");
                           Ok(self.unwrap_call(call))
                       }
                       "string_upper" | "string_to_upper" => {
                           let s = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_upper, &[s.into()], "su");
                           Ok(self.unwrap_call(call))
                       }
                       "string_lower" | "string_to_lower" => {
                           let s = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_lower, &[s.into()], "sl");
                           Ok(self.unwrap_call(call))
                       }
                       "string_starts_with" => {
                           let s = self.expr(&args[0], None)?;
                           let p = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_starts_with, &[s.into(), p.into()], "ssw");
                           Ok(self.unwrap_call(call))
                       }
                       "string_ends_with" => {
                           let s = self.expr(&args[0], None)?;
                           let p = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_ends_with, &[s.into(), p.into()], "sew");
                           Ok(self.unwrap_call(call))
                       }
                       "string_len" => {
                           let s = self.expr(&args[0], None)?;
                           let call = self.call_coerced(self.builtins.hsh_string_len, &[s.into()], "slen2");
                           Ok(self.unwrap_call(call))
                       }
                       "array_remove" => {
                           let a = self.expr(&args[0], None)?;
                           let i = self.expr(&args[1], None)?;
                           let call = self.call_coerced(self.builtins.hsh_array_remove, &[a.into(), i.into()], "arm");
                           Ok(self.unwrap_call(call))
                       }
                       _ => {
                           if let Some(&fv) = self.func_vals.get(name) {
                               self.call_user_fn(fv, args, name)
                           } else {
                               // Previously this silently returned 0 for *any*
                               // unrecognized name — meaning a typo'd function
                               // call (`pint(x)` instead of `print(x)`) would
                               // compile cleanly and just produce 0 at runtime.
                               // That's exactly the kind of silent-failure bug
                               // a compiler must not allow: fail loudly instead.
                               Err(CodegenError::UndefinedFn { name: name.to_string(), span: call_span.clone() })
                           }
                       }
                   }
               }

               /// Compile a call to a user-defined (H#-level) function. Shared by
               /// the shadowing check at the top of `call_fn` and by the
               /// "not a built-in" fallback at the bottom of it.
               fn call_user_fn(&mut self, fv: FunctionValue<'ctx>, args: &[Expr], _name: &str) -> R<BasicValueEnum<'ctx>> {
                   let sig = fv.get_type();
                   let mut avs = Vec::new();
                   for (i, a) in args.iter().enumerate() {
                       let expected: Option<BasicTypeEnum> = sig.get_param_types().get(i)
                           .and_then(|pt| metadata_to_basic(*pt));
                       avs.push(self.expr(a, expected)?);
                   }
                   let r = self.call_coerced(fv, &avs, "call");
                   if sig.get_return_type().is_none() {
                       Ok(self.ctx.i64_type().const_zero().into())
                   } else {
                       Ok(self.unwrap_call(r))
                   }
               }

               fn binop(&mut self, op: &BinOp, lv: BasicValueEnum<'ctx>, rv: BasicValueEnum<'ctx>) -> R<BasicValueEnum<'ctx>> {
                   // Unify mismatched int widths before doing anything else.
                   // `l`/`r` can legitimately arrive with different bit
                   // widths — e.g. `argc < 2` where `argc` is a variable
                   // with its own natural `i64` type, but the literal `2`
                   // was compiled under a `hint` meant for the *outer*
                   // boolean context (as_bool hints i8), not for this
                   // operand. LLVM requires both operands of an int
                   // binary/compare op to be the exact same type, so widen
                   // the narrower one (sign-extend) to match rather than
                   // emitting mismatched-type IR.
                   let (lv, rv) = match (lv, rv) {
                       (BasicValueEnum::IntValue(l), BasicValueEnum::IntValue(r)) => {
                           let lw = l.get_type().get_bit_width();
                           let rw = r.get_type().get_bit_width();
                           if lw < rw {
                               (self.builder.build_int_s_extend(l, r.get_type(), "wl").unwrap().into(), r.into())
                           } else if rw < lw {
                               (l.into(), self.builder.build_int_s_extend(r, l.get_type(), "wr").unwrap().into())
                           } else {
                               (l.into(), r.into())
                           }
                       }
                       other => other,
                   };
                   Ok(match (lv, rv) {
                       (BasicValueEnum::IntValue(l), BasicValueEnum::IntValue(r)) => {
                           match op {
                               BinOp::Add    => self.builder.build_int_add(l, r, "add").unwrap().into(),
                      BinOp::Sub    => self.builder.build_int_sub(l, r, "sub").unwrap().into(),
                      BinOp::Mul    => self.builder.build_int_mul(l, r, "mul").unwrap().into(),
                      BinOp::Div    => self.builder.build_int_signed_div(l, r, "div").unwrap().into(),
                      BinOp::Mod    => self.builder.build_int_signed_rem(l, r, "rem").unwrap().into(),
                      BinOp::BitAnd => self.builder.build_and(l, r, "and").unwrap().into(),
                      BinOp::BitOr  => self.builder.build_or(l, r, "or").unwrap().into(),
                      BinOp::BitXor => self.builder.build_xor(l, r, "xor").unwrap().into(),
                      BinOp::Shl    => self.builder.build_left_shift(l, r, "shl").unwrap().into(),
                      BinOp::Shr    => self.builder.build_right_shift(l, r, true, "shr").unwrap().into(),
                      BinOp::Eq     => self.builder.build_int_compare(inkwell::IntPredicate::EQ,  l, r, "eq").unwrap().into(),
                      BinOp::NotEq  => self.builder.build_int_compare(inkwell::IntPredicate::NE,  l, r, "ne").unwrap().into(),
                      BinOp::Lt     => self.builder.build_int_compare(inkwell::IntPredicate::SLT, l, r, "lt").unwrap().into(),
                      BinOp::Gt     => self.builder.build_int_compare(inkwell::IntPredicate::SGT, l, r, "gt").unwrap().into(),
                      BinOp::LtEq   => self.builder.build_int_compare(inkwell::IntPredicate::SLE, l, r, "le").unwrap().into(),
                      BinOp::GtEq   => self.builder.build_int_compare(inkwell::IntPredicate::SGE, l, r, "ge").unwrap().into(),
                      BinOp::And    => self.builder.build_and(l, r, "land").unwrap().into(),
                      BinOp::Or     => self.builder.build_or(l, r, "lor").unwrap().into(),
                           }
                       }
                       (BasicValueEnum::FloatValue(l), BasicValueEnum::FloatValue(r)) => {
                           match op {
                               BinOp::Add  => self.builder.build_float_add(l, r, "fadd").unwrap().into(),
                      BinOp::Sub  => self.builder.build_float_sub(l, r, "fsub").unwrap().into(),
                      BinOp::Mul  => self.builder.build_float_mul(l, r, "fmul").unwrap().into(),
                      BinOp::Div  => self.builder.build_float_div(l, r, "fdiv").unwrap().into(),
                      BinOp::Eq   => self.builder.build_float_compare(inkwell::FloatPredicate::OEQ, l, r, "feq").unwrap().into(),
                      BinOp::Lt   => self.builder.build_float_compare(inkwell::FloatPredicate::OLT, l, r, "flt").unwrap().into(),
                      BinOp::Gt   => self.builder.build_float_compare(inkwell::FloatPredicate::OGT, l, r, "fgt").unwrap().into(),
                      _           => self.ctx.f64_type().const_zero().into(),
                           }
                       }
                       (BasicValueEnum::PointerValue(l), BasicValueEnum::PointerValue(r)) => {
                           // CRITICAL FIX: this whole arm was previously
                           // missing entirely — pointer/pointer operands
                           // (which is what H# `string` values are
                           // represented as) fell through to the
                           // catch-all `_ => const_zero()` below,
                           // silently turning *every* bare `s1 == s2` /
                           // `s1 != s2` comparison anywhere in a program
                           // (outside a `match`, which has its own
                           // separate, correct strcmp-based comparison in
                           // `compile_pattern_cond`) into a hardcoded
                           // constant `false` — not a wrong runtime
                           // comparison, an actual `br i1 false` baked
                           // into the IR regardless of the operator or
                           // the values involved. A pattern as basic as
                           // `if cmd == "" is ...` or `while name != ""
                           // is ...` never worked correctly; a fix
                           // upstream in the `elsif cmd == ""` case, gated
                           // behind an always-false branch, was exactly
                           // why an assignment guarded by it silently
                           // never ran.
                           //
                           // Uses the same strcmp-based content comparison
                           // `compile_pattern_cond` already uses for
                           // match-arm string patterns, for consistency:
                           // two different string allocations with equal
                           // *content* compare equal, which is what every
                           // existing match-based string comparison in
                           // this codebase already does and what H# source
                           // written assuming value semantics for strings
                           // expects. (This does mean `==`/`!=` on a
                           // non-string pointer — an array, a struct
                           // reference, an `@arc`/`@pointers` raw pointer
                           // — also goes through strcmp now rather than a
                           // raw address comparison; those aren't
                           // null-terminated text, so comparing them this
                           // way is a separate, narrower concern, but
                           // vastly preferable to silently-always-false,
                           // which is what every one of these comparisons
                           // — string or not — was doing before.)
                           // `+` on two pointer values is string
                           // concatenation (`hsh_strcat`) — checked
                           // *before* the comparison operators below,
                           // since it doesn't need (and shouldn't pay
                           // for) a strcmp call at all. This was the
                           // other half of the pointer-comparison fix
                           // above: `c.bold + "text"` (`c.bold` a struct
                           // field declared `string`) reaching this
                           // function as two genuine `PointerValue`s only
                           // became possible once `Expr::FieldAccess`
                           // started coercing struct-field reads to their
                           // real declared type instead of always
                           // returning a raw, un-typed `i64` slot — before
                           // that fix, both operands showed up here as
                           // `IntValue`s and silently did *plain integer
                           // addition* on what were actually two pointer
                           // values, producing a garbage "string" that
                           // then got handed to `println`/whatever used
                           // it. Every other pointer op besides `+` and
                           // the six comparisons below (Sub/Mul/Div/...)
                           // still isn't meaningful for pointers and
                           // keeps returning zero rather than guessing.
                           if matches!(op, BinOp::Add) {
                               let call = self.call_coerced(self.builtins.hsh_strcat, &[l.into(), r.into()], "cat");
                               return Ok(self.unwrap_call(call));
                           }
                           let i32t = self.ctx.i32_type();
                           let ptr_t = self.ctx.ptr_type(inkwell::AddressSpace::default());
                           let strcmp_fn = self.module.get_function("strcmp").unwrap_or_else(|| {
                               self.module.add_function("strcmp", i32t.fn_type(&[ptr_t.into(), ptr_t.into()], false), None)
                           });
                           let cmp = self.call_coerced(strcmp_fn, &[l.into(), r.into()], "pcmp");
                           let ci  = self.unwrap_call(cmp).into_int_value();
                           let z   = i32t.const_zero();
                           match op {
                               BinOp::Eq    => self.builder.build_int_compare(inkwell::IntPredicate::EQ,  ci, z, "peq").unwrap().into(),
                               BinOp::NotEq => self.builder.build_int_compare(inkwell::IntPredicate::NE,  ci, z, "pne").unwrap().into(),
                               BinOp::Lt    => self.builder.build_int_compare(inkwell::IntPredicate::SLT, ci, z, "plt").unwrap().into(),
                               BinOp::Gt    => self.builder.build_int_compare(inkwell::IntPredicate::SGT, ci, z, "pgt").unwrap().into(),
                               BinOp::LtEq  => self.builder.build_int_compare(inkwell::IntPredicate::SLE, ci, z, "ple").unwrap().into(),
                               BinOp::GtEq  => self.builder.build_int_compare(inkwell::IntPredicate::SGE, ci, z, "pge").unwrap().into(),
                               // Not meaningful for pointers (Sub/Mul/etc)
                               // — fall back to the previous behavior
                               // (zero) rather than guessing.
                               _ => self.ctx.i64_type().const_zero().into(),
                           }
                       }
                       _ => self.ctx.i64_type().const_zero().into(),
                   })
               }

               fn cast(&mut self, v: BasicValueEnum<'ctx>, dst: BasicTypeEnum<'ctx>) -> R<BasicValueEnum<'ctx>> {
                   Ok(match (v, dst) {
                       (BasicValueEnum::IntValue(i), BasicTypeEnum::IntType(t)) => {
                           if i.get_type().get_bit_width() > t.get_bit_width() {
                               self.builder.build_int_truncate(i, t, "trunc").unwrap().into()
                           } else {
                               self.builder.build_int_s_extend(i, t, "sext").unwrap().into()
                           }
                       }
                       (BasicValueEnum::IntValue(i), BasicTypeEnum::FloatType(t)) =>
                       self.builder.build_signed_int_to_float(i, t, "i2f").unwrap().into(),
                      (BasicValueEnum::FloatValue(f), BasicTypeEnum::IntType(t)) =>
                      self.builder.build_float_to_signed_int(f, t, "f2i").unwrap().into(),
                      _ => v,
                   })
               }

               fn as_bool(&mut self, e: &Expr) -> R<inkwell::values::IntValue<'ctx>> {
                   let v = self.expr(e, Some(self.ctx.i8_type().into()))?;
                   match &v {
                       BasicValueEnum::IntValue(i) => {
                           let z = i.get_type().const_zero();
                           Ok(self.builder.build_int_compare(inkwell::IntPredicate::NE, *i, z, "bool").unwrap())
                       }
                       BasicValueEnum::FloatValue(f) => {
                           let z = f.get_type().const_float(0.0);
                           Ok(self.builder.build_float_compare(inkwell::FloatPredicate::ONE, *f, z, "fbool").unwrap())
                       }
                       _ => Ok(self.ctx.i8_type().const_int(1, false)),
                   }
               }

               /// Emit a `ret` instruction whose value (if any) matches the
               /// function's *actual* compiled LLVM return type exactly —
               /// shared by `Stmt::Return` and both `Expr::Return` sites.
               /// `main` is a fixed i32 regardless of any H# annotation
               /// (see `build_fn_type`'s main special-case); an H#
               /// function with no `-> T` at all compiles to a `void`
               /// signature; otherwise it's whatever `-> T` maps to via
               /// `htype_to_llvm`. Getting this wrong is exactly what
               /// produced every "Function return type does not match
               /// operand type of return inst!" verifier error — e.g. a
               /// function returning a struct (`ptr`) whose last statement
               /// happened to compute a plain `i64`, or vice versa.
               fn build_return_coerced(&mut self, val: Option<&Expr>) -> R<()> {
                   let actual_ret_ty: Option<BasicTypeEnum> = if self.fn_name == "main" {
                       Some(self.ctx.i32_type().into())
                   } else {
                       self.ret_type.as_ref().and_then(|t| htype_to_llvm(self.ctx, t))
                   };
                   // `@arc`: if we're returning a bare `x`, don't auto-release
                   // it in the epilogue below — same "don't release what
                   // you're handing back to the caller" rule
                   // `emit_arena_epilogue` already applies to arena memory.
                   let returned_ident: Option<&str> = match val {
                       Some(Expr::Ident(name, _)) => Some(name.as_str()),
                       _ => None,
                   };
                   match (val, actual_ret_ty) {
                       (Some(expr), Some(target)) => {
                           let v = self.expr(expr, Some(target))?;
                           let v = self.coerce_basic_value(v, target);
                           self.emit_arena_epilogue(matches!(target, BasicTypeEnum::PointerType(_)));
                           self.emit_arc_epilogue(returned_ident);
                           self.builder.build_return(Some(&v)).unwrap();
                       }
                       (_, None) => {
                           // Declared signature is void — can't attach a
                           // value even if the source wrote `return expr`.
                           // Still evaluate `expr` for side effects.
                           if let Some(expr) = val { self.expr(expr, None)?; }
                           self.emit_arena_epilogue(false);
                           self.emit_arc_epilogue(returned_ident);
                           self.builder.build_return(None).unwrap();
                       }
                       (None, Some(target)) => {
                           // Bare `return` in a function that *does* have a
                           // declared return type — every path through a
                           // non-void function needs a value. This is
                           // always a zero/null, never arena memory, so
                           // it's always safe to free here.
                           let z = self.zero(target);
                           self.emit_arena_epilogue(false);
                           self.emit_arc_epilogue(returned_ident);
                           self.builder.build_return(Some(&z)).unwrap();
                       }
                   }
                   Ok(())
               }

               /// `@arc` basic v2 epilogue (see `arc_owned`'s doc comment):
               /// auto-release every still-tracked arc local at this return
               /// path, except the one being returned as a bare identifier
               /// (`returned_ident`, computed in `build_return_coerced`).
               /// Like `emit_arena_epilogue`, this is a leak-not-corrupt
               /// trade-off: an arc pointer returned *inside* a struct/array
               /// rather than as a bare `x` isn't recognized here and will
               /// be over-released — escape analysis through aggregates is
               /// future work, same caveat the arena epilogue documents. A
               /// no-op outside `@arc` functions.
               fn emit_arc_epilogue(&mut self, returned_ident: Option<&str>) {
                   if self.mem_mode != MemoryMode::Arc { return; }
                   let owned = self.arc_owned.borrow().clone();
                   for name in owned {
                       if Some(name.as_str()) == returned_ident { continue; }
                       if let Some(&(ptr, ty)) = self.vars.get(&name) {
                           let v = self.builder.build_load(ty, ptr, "arc_rel").unwrap();
                           self.call_coerced(self.builtins.hsh_rc_release, &[v], "");
                       }
                   }
               }

               /// `@arena` epilogue, emitted on every return path right
               /// before the `ret` instruction. Pops this call's arena off
               /// the thread-local current-arena stack (restoring whatever
               /// was active before it, so a caller that's itself an
               /// `@arena` function keeps working correctly), and frees it
               /// — *unless* `retains_pointer` says the value being
               /// returned might itself be memory this call just
               /// bump-allocated (a string built during the call, a
               /// struct/array literal, ...). Freeing the arena in that
               /// case would hand the caller a dangling pointer, so instead
               /// we deliberately leak that one arena rather than corrupt
               /// the return value — same "leak, don't corrupt" trade-off
               /// as the rest of H# today, just bounded to one call's worth
               /// of memory instead of accumulating forever.
               fn emit_arena_epilogue(&mut self, retains_pointer: bool) {
                   if self.mem_mode != MemoryMode::Arena { return; }
                   let popped    = self.call_coerced(self.builtins.hsh_arena_pop_current, &[], "popped_arena");
                   let arena_val = self.unwrap_call(popped);
                   if retains_pointer { return; }
                   self.call_coerced(self.builtins.hsh_arena_free, &[arena_val], "");
               }

               fn zero(&self, ty: BasicTypeEnum<'ctx>) -> BasicValueEnum<'ctx> {
                   match ty {
                       BasicTypeEnum::IntType(t)     => t.const_zero().into(),
                       BasicTypeEnum::FloatType(t)   => t.const_zero().into(),
                       BasicTypeEnum::PointerType(t) => t.const_null().into(),
                       _                             => self.ctx.i64_type().const_zero().into(),
                   }
               }
}

/// §11/§12: query `pkg-config --cflags <pkg>` for compiler flags needed to
/// find PCRE2/sqlite3 headers. Returns `None` if `pkg-config` or the
/// package isn't available — callers fall back gracefully (relying on
/// default include paths, which works on most distros where these headers
/// live in /usr/include anyway).
fn pkg_config_cflags(pkg: &str) -> Option<Vec<String>> {
    let out = std::process::Command::new("pkg-config").args(["--cflags", pkg]).output().ok()?;
    if !out.status.success() { return None; }
    let s = String::from_utf8_lossy(&out.stdout);
    Some(s.split_whitespace().map(|s| s.to_string()).collect())
}

/// §11/§12: query `pkg-config --libs <pkg>` for the correct `-l...` link
/// flags (handles distro naming differences, e.g. `libpcre2-8` provides
/// `-lpcre2-8`, plus any extra transitive deps pkg-config knows about).
/// Returns `None` if unavailable — caller falls back to a hardcoded guess.
fn pkg_config_libs(pkg: &str) -> Option<Vec<String>> {
    let out = std::process::Command::new("pkg-config").args(["--libs", pkg]).output().ok()?;
    if !out.status.success() { return None; }
    let s = String::from_utf8_lossy(&out.stdout);
    let libs: Vec<String> = s.split_whitespace().map(|s| s.to_string()).collect();
    if libs.is_empty() { None } else { Some(libs) }
}
