# Homebrew formula for H#. Lives in this repo (rather than only in a
# homebrew-core PR) so `brew install --build-from-source
# config/packaging/macos/hsharp.rb` works straight out of a checkout, and
# so a `brew tap HackerOS-Linux-System/hsharp` tap repo can just symlink
# or copy this file in — single source of truth either way.
#
# VERIFICATION NOTE: `brew` doesn't run on this Linux sandbox, so unlike
# debian/ubuntu/fedora/opensuse (all built and verified for real here)
# and windows (compiled for real with makensis), this formula has only
# been checked by hand against Homebrew's documented Formula DSL/style
# guide — see .github/workflows/build.yml's `macos` job, which runs
# `brew install --build-from-source` against this exact file on a real
# `macos-latest` GitHub runner, for the actual verification.
class Hsharp < Formula
  desc "H# programming language compiler and interpreter"
  homepage "https://github.com/HackerOS-Linux-System/H-Sharp"
  url "https://github.com/HackerOS-Linux-System/H-Sharp/archive/refs/tags/v0.9.0.tar.gz"
  sha256 "" # filled in by build.yml's release job from the real release tarball's checksum — see that workflow's "compute sha256" step
  license "MPL-2.0"
  head "https://github.com/HackerOS-Linux-System/H-Sharp.git", branch: "main"

  depends_on "rust" => :build
  depends_on "llvm@21"

  def install
    # LLVM 21 via Homebrew is keg-only (not symlinked into
    # /usr/local|/opt/homebrew by default, to avoid clashing with
    # Apple's own bundled LLVM/clang) — llvm-sys/inkwell find it via
    # LLVM_SYS_211_PREFIX, not by searching PATH, so this needs to be set
    # explicitly rather than just adding llvm's bin dir to PATH.
    ENV["LLVM_SYS_211_PREFIX"] = Formula["llvm@21"].opt_prefix

    system "cargo", "install", *std_cargo_args(path: "source-code/cli")

    # `h#` alongside the `hsharp` Cargo bin name — macOS's HFS+/APFS both
    # allow `#` in filenames just fine (unlike the Windows PATHEXT
    # situation this project's NSIS installer has to work around — see
    # config/packaging/windows/installer.nsi), so a plain symlink is
    # enough here, no wrapper script needed.
    bin.install_symlink bin/"hsharp" => "h#"
  end

  test do
    # `std_cargo_args`-installed binaries are always named after the
    # crate's own [[bin]] name (see source-code/cli/Cargo.toml) —
    # "hsharp", not the formula name, which happens to match here but
    # isn't guaranteed to in general, hence spelling it out explicitly
    # rather than relying on `bin/name`.
    assert_match version.to_s, shell_output("#{bin}/hsharp --version")
  end
end
