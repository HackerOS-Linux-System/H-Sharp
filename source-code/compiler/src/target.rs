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
}

#[derive(Debug, Clone, PartialEq)]
pub enum Os {
    Linux,
    Windows,
    MacOS,
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

    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "linux-x86_64" | "linux" => Some(Self::linux_x86_64_musl()),
            "linux-x86_64-gnu" => Some(Self::linux_x86_64_gnu()),
            "linux-aarch64" => Some(Self::linux_aarch64()),
            "windows" | "windows-x86_64" => Some(Self::windows_x86_64()),
            "windows-aarch64" => Some(Self::windows_aarch64()),
            "macos" | "macos-x86_64" => Some(Self::macos_x86_64()),
            "macos-aarch64" => Some(Self::macos_aarch64()),
            _ => None,
        }
    }

    pub fn exe_suffix(&self) -> &'static str {
        match self.os {
            Os::Windows => ".exe",
            _ => "",
        }
    }

    pub fn all_named() -> Vec<(&'static str, &'static str)> {
        vec![
            ("linux-x86_64", "Linux x86_64 (musl, fully static) [default]"),
            ("linux-x86_64-gnu", "Linux x86_64 (gnu)"),
            ("linux-aarch64", "Linux ARM64"),
            ("windows-x86_64", "Windows x86_64"),
            ("windows-aarch64", "Windows ARM64"),
            ("macos-x86_64", "macOS Intel"),
            ("macos-aarch64", "macOS Apple Silicon"),
        ]
    }
}

impl std::fmt::Display for TargetTriple {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.llvm_triple)
    }
}
