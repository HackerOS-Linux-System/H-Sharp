Name:           hsharp
Version:        0.9.0
Release:        0
Summary:        H# programming language compiler and interpreter
License:        MPL-2.0
Group:          Development/Languages/Other
URL:            https://github.com/HackerOS-Linux-System/H-Sharp
# Same "binary already built by CI" approach as config/packaging/fedora/
# hsharp.spec — see that file's Source0 comment for the full rationale
# (LLVM 21 from apt.llvm.org has no openSUSE/OBS equivalent an OBS build
# service worker could pull from without extra repo plumbing). Kept as
# its own file rather than shared with Fedora's spec because openSUSE's
# rpm conventions differ enough (no %%dist tag, %%license vs
# %%{_licensedir} handling varies by SUSE version, Group: is still
# expected on openSUSE where Fedora dropped it) that a single shared
# spec would need constant `%%if 0%%{?suse_version}` branching for little
# real benefit over two small, readable files.
Source0:        hsharp
Source1:        LICENSE
Requires:       glibc >= 2.31
BuildRoot:      %{_tmppath}/%{name}-%{version}-build

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
install -D -m 644 %{SOURCE1} %{buildroot}%{_defaultdocdir}/%{name}/LICENSE

%files
%{_bindir}/hsharp
%{_bindir}/h#
%doc %{_defaultdocdir}/%{name}/LICENSE

%changelog
* Mon Jan 01 2024 HackerOS Team <hackeros068@gmail.com> - 0.9.0-0
- See https://github.com/HackerOS-Linux-System/H-Sharp/releases for the
  real per-version changelog (same note as the Fedora spec).
