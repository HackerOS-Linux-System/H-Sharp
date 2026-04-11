use inkwell::module::Module;
use inkwell::targets::TargetMachine;

/// Optimize the LLVM module using LLVM 20's new pass manager.
/// opt_level: 0=O0, 1=O1, 2=O2, 3=O3 (aggressive)
pub fn optimize_module(module: &Module, machine: &TargetMachine, opt_level: u32) {
    // LLVM 20 exposes run_passes via TargetMachine
    let passes = match opt_level {
        0 => "",
        1 => "default<O1>",
        2 => "default<O2>",
        _ => "default<O3>",
    };

    if passes.is_empty() { return; }

    use inkwell::passes::PassBuilderOptions;
    let opts = PassBuilderOptions::create();
    opts.set_loop_unrolling(opt_level >= 2);
    opts.set_loop_vectorization(opt_level >= 2);
    opts.set_loop_slp_vectorization(opt_level >= 3);
    opts.set_merge_functions(opt_level >= 2);

    if let Err(e) = module.run_passes(passes, machine, opts) {
        // Non-fatal: optimization failure doesn't prevent linking
        eprintln!("  warn: optimization pass failed: {}", e.to_string());
    }
}
