#!/usr/bin/env bash
# Buduje kompilator H# (samodzielny, napisany w H#) z katalogu repozytorium za pomocą `bit`.
#
#   .github/scripts/build-hsharp.sh <plik-wyjściowy> [opcje bit build]
#
# Wymaga: `h#` (kompilator stage0), `bit` i g++ w PATH oraz std w /usr/lib/HackerOS/H#/std
# (robi to akcja ./.github/actions/setup-hsharp).
#
# HSHARP_STAGES=1  (domyślnie) -> stage0 buduje źródła                          => stage1
# HSHARP_STAGES=2              -> stage1 buduje te same źródła jeszcze raz       => stage2
#                                 (test samodzielności: kompilator buduje sam siebie)
set -euo pipefail

OUT="${1:?użycie: build-hsharp.sh <plik-wyjściowy> [opcje bit build]}"
shift || true
STAGES="${HSHARP_STAGES:-1}"
ENTRY="source-code/cli/src/main.h#"
SUDO=""; [ "$(id -u)" -ne 0 ] && SUDO="sudo"

# Znajduje binarkę kompilatora wyprodukowaną przez `bit build --release`.
find_binary() {
  local d="cache/build/release" n
  for n in hsharp "h#" cli; do
    if [ -f "$d/$n" ] && [ -x "$d/$n" ]; then echo "$d/$n"; return 0; fi
  done
  # awaryjnie: jedyny plik wykonywalny w katalogu wynikowym
  local found
  found="$(find "$d" -maxdepth 2 -type f -perm -u+x ! -name '*.so' ! -name '*.a' ! -name '*.o' ! -name '*.sh' 2>/dev/null | head -n 1 || true)"
  if [ -n "$found" ]; then echo "$found"; return 0; fi
  return 1
}

build_stage() {  # $1 = numer etapu, $2 = plik wyjściowy
  echo "::group::H# stage$1 — bit install"
  "h#" --version || true
  rm -rf cache
  bit install
  echo "::endgroup::"

  echo "::group::H# stage$1 — h# check $ENTRY"
  "h#" check "$ENTRY"
  echo "::endgroup::"

  echo "::group::H# stage$1 — bit build --release"
  bit build --release "$@"
  echo "::endgroup::"

  local bin
  if ! bin="$(find_binary)"; then
    echo "::error::bit build zakończony, ale w cache/build/release nie ma binarki kompilatora"
    ls -la cache/build/release 2>/dev/null || true
    return 1
  fi
  mkdir -p "$(dirname "$2")"
  install -m 0755 "$bin" "$2"
  echo "stage$1 -> $2 ($bin)"
  "$2" --version
}

mkdir -p "$(dirname "$OUT")"
STAGE1="$OUT"
[ "$STAGES" -ge 2 ] && STAGE1="${OUT}.stage1"

build_stage 1 "$STAGE1" "$@"

if [ "$STAGES" -ge 2 ]; then
  # stage1 (zbudowany z tych źródeł) zastępuje stage0 na PATH i buduje źródła ponownie
  $SUDO install -m 0755 "$STAGE1" /usr/local/bin/hsharp
  $SUDO ln -sf /usr/local/bin/hsharp "/usr/local/bin/h#"
  hash -r
  build_stage 2 "$OUT" "$@"
  V1="$("$STAGE1" --version)"; V2="$("$OUT" --version)"
  if [ "$V1" != "$V2" ]; then
    echo "::error::stage1 i stage2 raportują różne wersje: '$V1' vs '$V2'"; exit 1
  fi
  rm -f "$STAGE1"
fi
