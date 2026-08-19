Name:           hsharp
Version:        0.9.0
Release:        1%{?dist}
Summary:        H# programming language compiler and interpreter

License:        MPL-2.0
URL:            https://github.com/HackerOS-Linux-System/H-Sharp
# This spec expects the release binary to already be built by the CI
# workflow (`cargo build --release`) and staged at %%{_sourcedir}/hsharp —
# it deliberately does NOT run `cargo build` itself inside %build, unlike
# a typical Fedora Rust package. Rationale: this workspace needs LLVM 21
# from apt.llvm.org's unstable channel, which has no Fedora/COPR
# equivalent Fedora's own build infra (mock/koji) could pull from without
# a lot of extra plumbing — see .github/workflows/build.yml's `fedora`
# job for how the binary actually gets built (a container with LLVM 21
# installed via the official LLVM apt-getter... adapted for dnf, see that
# job) before this spec ever runs. This keeps the spec itself simple and
# fast (seconds, not a full compiler build) for local `rpmbuild -bb`
# iteration against an already-built binary.
Source0:        hsharp
Source1:        LICENSE

Requires:       glibc >= 2.34
# LLVM 21's shared runtime libs the compiled binary itself links against
# (not build-time — this is what a `dnf install hsharp` pulls in so the
# LLVM codegen backend actually works at runtime, not just the
# interpreter). Adjust the exact package name if Fedora's LLVM 21
# sub-package naming differs by release (see build.yml's fedora job,
# which installs the matching -devel package to build against).
Requires:       llvm21-libs

%description
H# (h-sharp) is a compiled/interpreted programming language with an
LLVM 21 backend for release builds and a tree-walking interpreter for
`h# preview`/REPL use. This package installs the `hsharp` binary (also
available as `h#`), providing compile, preview, check, fmt, repl, lsp,
and new subcommands.

%prep
# No source to unpack/patch — see the Source0 comment above.

%build
# No build step — see the Source0 comment above.

%install
rm -rf %{buildroot}
install -D -m 755 %{SOURCE0} %{buildroot}%{_bindir}/hsharp
ln -sf hsharp %{buildroot}%{_bindir}/h#
install -D -m 644 %{SOURCE1} %{buildroot}%{_licensedir}/%{name}/LICENSE

%files
%{_bindir}/hsharp
%{_bindir}/h#
%license %{_licensedir}/%{name}/LICENSE

%changelog
* Mon Jan 01 2024 HackerOS Team <hackeros068@gmail.com> - 0.9.0-1
- See https://github.com/HackerOS-Linux-System/H-Sharp/releases for the
  real per-version changelog; this spec's %changelog is intentionally
  minimal since release notes already live there and duplicating them
  here would just be another place for them to drift out of sync.
