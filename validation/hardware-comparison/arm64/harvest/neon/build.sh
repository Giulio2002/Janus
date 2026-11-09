#!/usr/bin/env bash
# Janus NEON harvest corpus builder.
# The *.c files next to this script are plain C11 loop idioms (no intrinsics)
# chosen so that the gcc/clang auto-vectorisers emit a broad range of AdvSIMD
# instructions; the objects are used to rank NEON instruction classes by how
# many compiled functions use them and to harvest real NEON words for the
# differential oracle.  Usage: build.sh [OUTDIR]  (default: fresh mktemp -d).
# Writes one subdirectory per config (gcc-O0 ... clang-O3) and prints OUTDIR;
# never writes inside the source tree.
set -euo pipefail

SRC="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT="${1:-$(mktemp -d)}"
mkdir -p "$OUT"
OUT="$(cd "$OUT" && pwd)"
case "$OUT/" in
  "$SRC"/*) echo "build.sh: refusing to write inside source tree $SRC" >&2; exit 1 ;;
esac

GCC=(aarch64-linux-gnu-gcc)
CLANG=(clang --target=aarch64-linux-gnu)
COMMON=(-c -fPIC -pthread -g)

shopt -s nullglob
srcs=("$SRC"/*.c)
[ ${#srcs[@]} -gt 0 ] || { echo "build.sh: no .c files in $SRC" >&2; exit 1; }

for comp in gcc clang; do
  if [ "$comp" = gcc ]; then CC=("${GCC[@]}"); else CC=("${CLANG[@]}"); fi
  for lvl in O0 O2 O3; do
    d="$OUT/$comp-$lvl"
    mkdir -p "$d"
    for f in "${srcs[@]}"; do
      b="$(basename "$f" .c)"
      "${CC[@]}" "${COMMON[@]}" "-$lvl" "$f" -o "$d/$b.o"
    done
  done
done
echo "$OUT"
