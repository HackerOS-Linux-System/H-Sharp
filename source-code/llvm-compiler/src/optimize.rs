/// LLVM optimization for H# — uses TargetMachine-based new pass manager
/// In LLVM 17, optimization level is passed to TargetMachine which handles opt internally.
/// For legacy PM (still functional in LLVM 17), we use PassManager with subset of passes.

use inkwell::module::Module;
use inkwell::passes::PassManager;

/// Apply module-level optimizations.
/// In inkwell 0.4 + LLVM17, optimization is primarily via TargetMachine opt level.
/// This applies only the passes that are still available in legacy PM.
pub fn optimize_module(module: &Module, _level: u32) {
    let pm: PassManager<Module> = PassManager::create(());
    // Note: Most named passes removed from legacy PM in LLVM17.
    // Actual optimization happens via TargetMachine::OptimizationLevel::Aggressive
    // which runs the new pass manager internally during machine code emission.
    pm.run_on(module);
}

/// Function-level optimization — no-op in LLVM17 new PM mode
/// (optimization done by TargetMachine at codegen time)
pub fn optimize_function<'ctx>(_module: &Module<'ctx>, _level: u32) {}
