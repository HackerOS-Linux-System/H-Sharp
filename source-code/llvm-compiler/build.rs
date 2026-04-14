fn main() {
    let prefix = std::env::var("LLVM_SYS_210_PREFIX")
        .or_else(|_| std::env::var("LLVM_SYS_181_PREFIX"))
        .or_else(|_| std::env::var("LLVM_SYS_180_PREFIX"))
        .or_else(|_| std::env::var("LLVM_SYS_170_PREFIX"))
        .unwrap_or_else(|_| {
            for p in &["/usr/lib/llvm-21", "/usr/lib/llvm-20",
                       "/usr/lib/llvm-18", "/usr/lib/llvm-17"] {
                if std::path::Path::new(p).join("bin/llvm-config").exists() {
                    return p.to_string();
                }
            }
            "/usr/lib/llvm-18".into()
        });
    println!("cargo:rustc-link-search=native={}/lib", prefix);
    println!("cargo:rustc-env=LLVM_SYS_210_PREFIX={}", prefix);
}
