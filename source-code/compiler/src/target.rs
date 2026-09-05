#[derive(Debug, Clone, PartialEq)]
pub struct TargetTriple {
    pub arch: Arch,
    pub os: Os,
    pub abi: Abi,
    pub llvm_triple: String,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Arch {
    X86_64,
    Aarch64,
    Riscv64,
    Wasm32,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Os {
    Linux,
    Windows,
    MacOS,
    /// wasm32-unknown-unknown: no OS at all — no processes, no
    /// filesystem, no environment variables, nothing `core.c`'s POSIX
    /// runtime (fork/popen/getenv/mkdir/...) can call into. See
    /// `TargetTriple::wasm32()`'s doc comment for what that means for
    /// which H# programs can actually target it.
    Freestanding,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Abi {
    Gnu,
    Musl,
    Msvc,
    None,
}

impl TargetTriple {
    pub fn host() -> Self {
        #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
        return Self::linux_x86_64_musl();
        #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
        return Self::windows_x86_64();
        #[cfg(all(target_arch = "x86_64", target_os = "macos"))]
        return Self::macos_x86_64();
        #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
        return Self::macos_aarch64();
        #[cfg(not(any(
            all(target_arch = "x86_64", target_os = "linux"),
            all(target_arch = "x86_64", target_os = "windows"),
            all(target_arch = "x86_64", target_os = "macos"),
            all(target_arch = "aarch64", target_os = "macos"),
        )))]
        return Self::linux_x86_64_musl();
    }

    pub fn linux_x86_64_musl() -> Self {
        Self {
            arch: Arch::X86_64,
            os: Os::Linux,
            abi: Abi::Musl,
            llvm_triple: "x86_64-unknown-linux-musl".to_string(),
        }
    }

    pub fn linux_x86_64_gnu() -> Self {
        Self {
            arch: Arch::X86_64,
            os: Os::Linux,
            abi: Abi::Gnu,
            llvm_triple: "x86_64-unknown-linux-gnu".to_string(),
        }
    }

    pub fn linux_aarch64() -> Self {
        Self {
            arch: Arch::Aarch64,
            os: Os::Linux,
            abi: Abi::Gnu,
            llvm_triple: "aarch64-unknown-linux-gnu".to_string(),
        }
    }

    /// Added alongside `cross_toolchain`'s cross-linker resolution (see
    /// codegen.rs) — `Arch::Riscv64` already existed as an enum variant,
    /// but had no constructor, no `from_str` entry, and no `all_named()`
    /// listing, so `--target riscv64-*` had no way to actually be
    /// selected from the CLI even though the LLVM backend itself (and
    /// now the cross-linker lookup table) both already understand it.
    pub fn linux_riscv64() -> Self {
        Self {
            arch: Arch::Riscv64,
            os: Os::Linux,
            abi: Abi::Gnu,
            llvm_triple: "riscv64gc-unknown-linux-gnu".to_string(),
        }
    }

    pub fn linux_riscv64_musl() -> Self {
        Self {
            arch: Arch::Riscv64,
            os: Os::Linux,
            abi: Abi::Musl,
            llvm_triple: "riscv64gc-unknown-linux-musl".to_string(),
        }
    }

    pub fn windows_x86_64() -> Self {
        Self {
            arch: Arch::X86_64,
            os: Os::Windows,
            abi: Abi::Msvc,
            llvm_triple: "x86_64-pc-windows-msvc".to_string(),
        }
    }

    pub fn windows_aarch64() -> Self {
        Self {
            arch: Arch::Aarch64,
            os: Os::Windows,
            abi: Abi::Msvc,
            llvm_triple: "aarch64-pc-windows-msvc".to_string(),
        }
    }

    pub fn macos_x86_64() -> Self {
        Self {
            arch: Arch::X86_64,
            os: Os::MacOS,
            abi: Abi::None,
            llvm_triple: "x86_64-apple-darwin".to_string(),
        }
    }

    pub fn macos_aarch64() -> Self {
        Self {
            arch: Arch::Aarch64,
            os: Os::MacOS,
            abi: Abi::None,
            llvm_triple: "aarch64-apple-darwin".to_string(),
        }
    }

    /// `wasm32-unknown-unknown` — no OS, no libc, no filesystem, no
    /// processes. **Not** general-purpose H# codegen the way every other
    /// target above is: `core.c`'s runtime (this whole compiler's only
    /// C runtime — see `runtime/core.c`) is built entirely on POSIX
    /// (`fork`, `popen`, `getenv`, `mkdir`, `fgets` from a real stdin,
    /// ...), none of which exist under this target. See `CompileOptions
    /// ::validate_wasm_compat` (in `lib.rs`) for the compile-time check
    /// this implies: a program using `fs::`/`proc::`/`env::`/
    /// `shell()`/`cmd()` gets a clear error naming the offending call
    /// instead of a binary that links (or doesn't) into something
    /// broken. Pure-computation H# (arithmetic, strings, structs,
    /// control flow, `write()`) targets this fine.
    ///
    /// For running *arbitrary* H# (including `fs::`/`proc::`-using
    /// programs like getit) inside a browser, use the `hsharp-playground`
    /// crate instead (`playground/`, wired up on the docs site's
    /// Playground section) — it wraps the pure-Rust *interpreter*, which
    /// has no POSIX dependency in the first place, rather than trying to
    /// make this LLVM/C-runtime pipeline target a freestanding
    /// environment it wasn't designed for.
    pub fn wasm32() -> Self {
        Self {
            arch: Arch::Wasm32,
            os: Os::Freestanding,
            abi: Abi::None,
            llvm_triple: "wasm32-unknown-unknown".to_string(),
        }
    }

    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "linux-x86_64" | "linux" => Some(Self::linux_x86_64_musl()),
            "linux-x86_64-gnu" => Some(Self::linux_x86_64_gnu()),
            "linux-aarch64" => Some(Self::linux_aarch64()),
            "linux-riscv64" => Some(Self::linux_riscv64()),
            "linux-riscv64-musl" => Some(Self::linux_riscv64_musl()),
            "windows" | "windows-x86_64" => Some(Self::windows_x86_64()),
            "windows-aarch64" => Some(Self::windows_aarch64()),
            "macos" | "macos-x86_64" => Some(Self::macos_x86_64()),
            "macos-aarch64" => Some(Self::macos_aarch64()),
            "wasm32" | "wasm" => Some(Self::wasm32()),
            _ => None,
        }
    }

    pub fn is_wasm(&self) -> bool {
        self.arch == Arch::Wasm32
    }

    pub fn exe_suffix(&self) -> &'static str {
        match self.os {
            Os::Windows => ".exe",
            Os::Freestanding => ".wasm",
            _ => "",
        }
    }

    pub fn all_named() -> Vec<(&'static str, &'static str)> {
        vec![
            ("linux-x86_64", "Linux x86_64 (musl, fully static) [default]"),
            ("linux-x86_64-gnu", "Linux x86_64 (gnu)"),
            ("linux-aarch64", "Linux ARM64"),
            ("linux-riscv64", "Linux RISC-V 64-bit (gnu, RV64GC)"),
            ("linux-riscv64-musl", "Linux RISC-V 64-bit (musl, RV64GC)"),
            ("windows-x86_64", "Windows x86_64"),
            ("windows-aarch64", "Windows ARM64"),
            ("macos-x86_64", "macOS Intel"),
            ("macos-aarch64", "macOS Apple Silicon"),
            ("wasm32", "WebAssembly (wasm32-unknown-unknown) — pure-computation H# only, see TargetTriple::wasm32()'s doc comment"),
        ]
    }
}

impl std::fmt::Display for TargetTriple {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.llvm_triple)
    }
}
