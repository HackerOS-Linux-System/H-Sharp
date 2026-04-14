use inkwell::module::Module;
use inkwell::targets::TargetMachine;
use inkwell::passes::PassBuilderOptions;

/// Full optimization pipeline for H# release binaries.
/// opt_level: 0=debug, 1=O1, 2=O2, 3=O3+size (production)
pub fn optimize_module(module: &Module, machine: &TargetMachine, opt_level: u32) {
    if opt_level == 0 { return; }

    // Build the pass pipeline string for LLVM 21 new pass manager
    let passes = match opt_level {
        1 => "default<O1>",
        2 => "default<O2>",
        _ => {
            // Level 3: full pipeline for maximum performance + minimum size
            // Note: separate size and perf passes — size pass uses Os/Oz
            "default<O3>"
        }
    };

    let opts = PassBuilderOptions::create();

    match opt_level {
        1 => {
            opts.set_loop_unrolling(false);
            opts.set_loop_vectorization(false);
        }
        2 => {
            opts.set_loop_unrolling(true);
            opts.set_loop_vectorization(true);
            opts.set_loop_slp_vectorization(true);
            opts.set_merge_functions(true);
        }
        _ => {
            // Maximum performance settings
            opts.set_loop_unrolling(true);
            opts.set_loop_vectorization(true);
            opts.set_loop_slp_vectorization(true);
            opts.set_merge_functions(true);
            // Verify after optimization (catches codegen bugs)
            opts.set_verify_each(false); // disable for speed
        }
    }

    if let Err(e) = module.run_passes(passes, machine, opts) {
        eprintln!("  warn: optimization: {}", e.to_string());
    }
}

/// Apply size-reduction passes after optimization.
/// Eliminates dead globals, strips metadata, inlines small fns.
pub fn minimize_size(module: &Module, machine: &TargetMachine) {
    let opts = PassBuilderOptions::create();
    opts.set_merge_functions(true);

    // Size-optimized pipeline
    if let Err(e) = module.run_passes("default<Os>", machine, opts) {
        eprintln!("  warn: size pass: {}", e.to_string());
    }
}
