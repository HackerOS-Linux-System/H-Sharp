use inkwell::module::Module;
use inkwell::targets::TargetMachine;
use inkwell::passes::PassBuilderOptions;
use inkwell::values::FunctionValue;

/// Run the LLVM optimization pipeline — call ONCE per module.
///
/// SEGFAULT FIX (kept from earlier): previously `compile_full` called both
/// `optimize_module(O3)` AND `minimize_size()`. Running two full pipelines
/// on the same module corrupts LLVM's internal pass-manager state ->
/// segfault on --release. Solution: single pipeline call only; O3 already
/// includes DCE + inlining + vectorization.
///
/// opt_level: 0 = none, 1 = O1, 2 = O2, 3 = O3 (production, default for
/// `--release`)
pub fn optimize_module(module: &Module, machine: &TargetMachine, opt_level: u32) {
    if opt_level == 0 { return; }

    let passes = match opt_level {
        1 => "default<O1>",
        2 => "default<O2>",
        _ => "default<O3>",   // single combined pipeline — never call minimize_size after this
    };

    let opts = PassBuilderOptions::create();
    opts.set_loop_unrolling(opt_level >= 2);
    opts.set_loop_vectorization(opt_level >= 2);
    opts.set_loop_slp_vectorization(opt_level >= 2);
    opts.set_loop_interleaving(opt_level >= 2);
    opts.set_merge_functions(opt_level >= 2);
    // Verification is expensive and only useful while debugging the
    // codegen itself; keep it off for normal builds so -O3 + LTO doesn't
    // pay for re-verifying IR after every pass.
    opts.set_verify_each(false);

    if let Err(e) = module.run_passes(passes, machine, opts) {
        // Non-fatal: binary still links correctly without optimisation
        eprintln!("  warn: LLVM opt pass failed ({}), continuing without optimisation", e.to_string());
    }
}

/// Size-minimising pass — safe ONLY at opt_level < 3.
/// At O3 the main pipeline already covers everything this does.
/// Calling it after O3 = double-pipeline = segfault.
pub fn minimize_size(module: &Module, machine: &TargetMachine) {
    let opts = PassBuilderOptions::create();
    opts.set_merge_functions(true);
    opts.set_verify_each(false);
    if let Err(e) = module.run_passes("default<Os>", machine, opts) {
        eprintln!("  warn: size pass failed: {}", e.to_string());
    }
}

/// Mark every H#-defined function `nounwind` (H# has no exception
/// unwinding — `panic` is `abort`/`exit`, see `runtime.rs`). This lets
/// LLVM's optimizer skip generating exception-handling landing pads and
/// unwind tables entirely, which:
///   - shrinks the resulting object/binary (no `.eh_frame` bloat for code
///     that never unwinds)
///   - allows more aggressive inlining (functions that might unwind are
///     harder to inline safely)
///
/// Call this once per `FunctionValue` right after it's declared, before
/// any pass pipeline runs. This is a cheap, purely additive optimization —
/// safe to apply unconditionally (it does not change program behavior,
/// since H# never throws/unwinds).
pub fn mark_nounwind(f: FunctionValue) {
    let ctx = f.get_type().get_context();
    let kind_id = inkwell::attributes::Attribute::get_named_enum_kind_id("nounwind");
    let attr = ctx.create_enum_attribute(kind_id, 0);
    f.add_attribute(inkwell::attributes::AttributeLoc::Function, attr);
}

/// Apply `noundef`+`nonnull` parameter attributes to every pointer
/// (string/bytes) parameter of an H#-defined function.
///
/// H# strings are always non-null (the runtime guarantees `hsh_*` string
/// functions never return a literal NULL — they return `""` instead, per
/// the `if (!s) return "";` guards throughout `runtime.rs`). Telling LLVM
/// this via `nonnull` lets it elide null checks it would otherwise insert
/// defensively around pointer parameters, and `noundef` allows more
/// aggressive load/store reordering since the optimizer doesn't need to
/// account for the parameter being `undef`.
///
/// This is opt-in per function (call from `compile_fn` for each pointer
/// param) rather than global, because extern C functions with genuinely
/// nullable pointer parameters (e.g. `void* arg` in a C library that
/// accepts NULL) must NOT get this attribute — only H#-defined functions,
/// whose calling convention guarantees non-null strings.
pub fn mark_param_nonnull(f: FunctionValue, param_index: u32) {
    let ctx = f.get_type().get_context();
    for name in ["nonnull", "noundef"] {
        let kind_id = inkwell::attributes::Attribute::get_named_enum_kind_id(name);
        let attr = ctx.create_enum_attribute(kind_id, 0);
        f.add_attribute(inkwell::attributes::AttributeLoc::Param(param_index), attr);
    }
}
