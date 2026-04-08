fn main() {
    // Auto-detect LLVM 17 installation
    let llvm_prefix = std::env::var("LLVM_SYS_170_PREFIX")
        .unwrap_or_else(|_| "/usr/lib/llvm-17".into());

    // Tell cargo to link against LLVM 17 dynamically
    println!("cargo:rustc-link-search=native={}/lib", llvm_prefix);
    println!("cargo:rustc-link-lib=dylib=LLVM-17");

    // Set prefix env for llvm-sys
    println!("cargo:rustc-env=LLVM_SYS_170_PREFIX={}", llvm_prefix);
}
