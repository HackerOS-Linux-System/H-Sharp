#!/bin/bash
# Builds a .deb package for H# on Ubuntu — mechanically identical to
# config/packaging/debian/build.sh (Ubuntu is deb-based and dpkg-deb
# doesn't care about the distro it's running on), kept as a *separate*
# copy rather than a shared script because Ubuntu and Debian's own
# libc6/base dependency versions in `control.in` diverge across their
# release cycles (e.g. Ubuntu 24.04 vs. Debian 12 ship different glibc
# versions) — this is the file to edit for an Ubuntu-only dependency
# bump without touching the Debian package.
#
# Usage: config/packaging/debian/build.sh <path-to-built-hsharp-binary> <version> <arch>
#   e.g. config/packaging/debian/build.sh target/release/hsharp 0.9.0 amd64
#
# Expects the `hsharp` binary to already be built (this script only
# packages it — see .github/workflows/build.yml for the `cargo build
# --release` step that runs first).
set -euo pipefail

BIN_PATH="${1:?usage: build.sh <path-to-hsharp-binary> <version> <arch>}"
VERSION="${2:?usage: build.sh <path-to-hsharp-binary> <version> <arch>}"
ARCH="${3:?usage: build.sh <path-to-hsharp-binary> <version> <arch>}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

PKG_ROOT="$WORK_DIR/hsharp_${VERSION}_${ARCH}"
mkdir -p "$PKG_ROOT/DEBIAN" "$PKG_ROOT/usr/bin" "$PKG_ROOT/usr/share/doc/hsharp"

# The binary ships as `hsharp` on disk; the `h#` name is a symlink (not a
# copy) so `file`/`ldd`/package tooling that expects a "normal" filename
# still works, while `h#` on PATH resolves to the exact same inode.
install -m 755 "$BIN_PATH" "$PKG_ROOT/usr/bin/hsharp"
ln -s hsharp "$PKG_ROOT/usr/bin/h#"

# control file is templated (version/arch substituted) rather than a
# static copy of control.in, so this script is the single source of
# truth for what ends up in the .deb — see control.in for the fields
# that stay fixed across versions/architectures.
sed -e "s/@VERSION@/${VERSION}/" -e "s/@ARCH@/${ARCH}/" \
    "$SCRIPT_DIR/control.in" > "$PKG_ROOT/DEBIAN/control"
install -m 755 "$SCRIPT_DIR/postinst" "$PKG_ROOT/DEBIAN/postinst"
install -m 755 "$SCRIPT_DIR/prerm" "$PKG_ROOT/DEBIAN/prerm"
cp "$SCRIPT_DIR/copyright" "$PKG_ROOT/usr/share/doc/hsharp/copyright"

OUT="hsharp_${VERSION}_${ARCH}.deb"
dpkg-deb --build --root-owner-group "$PKG_ROOT" "$OUT"
echo "Built: $OUT"
dpkg-deb --info "$OUT"
dpkg-deb --contents "$OUT"
