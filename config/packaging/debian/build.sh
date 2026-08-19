#!/bin/bash
# Builds a .deb package for H# on Debian, using dpkg-deb directly (no
# debuild/dpkg-buildpackage dependency chain — this repo isn't a "native"
# Debian source package, just a Rust workspace, so a hand-built binary
# .deb via dpkg-deb -b is the simplest thing that's both correct and easy
# to test locally: `dpkg-deb --build --root-owner-group <dir> out.deb`
# needs nothing beyond dpkg-dev, which is preinstalled on every Debian/
# Ubuntu image including GitHub's own `ubuntu-*` runners.
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
