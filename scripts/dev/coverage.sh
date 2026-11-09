#!/usr/bin/env bash
# Regenerates the numbers of docs/COVERAGE.md: how much of single-threaded Go Janus can model today.
#
#   scripts/coverage.sh [all]     build + insn + runtime + cc (default)
#   scripts/coverage.sh build     `go test -c` every std package with tests, for linux/arm64,
#                                 linux/amd64 GOAMD64=v1 and linux/amd64 GOAMD64=v3
#   scripts/coverage.sh insn      criterion 1: run the trusted Lean decoders over every function
#                                 of those binaries (janus-decode on arm64 words, janus-oracle-amd64
#                                 on x86asm-swept amd64 instructions); Go-compiled vs assembly
#   scripts/coverage.sh runtime   criterion 2: the runtime entry points the compiler can call
#                                 (typecheck/_builtin/runtime.go + ssagen/walk lookups) against
#                                 the contracts on main and the unmerged branches
#   scripts/coverage.sh asmcalls  criterion 4: which assembly functions Go-compiled std code
#                                 calls directly, and whether they decode (written by insn)
#   scripts/coverage.sh cc        criterion 5: a C corpus compiled by gcc and clang at -O0/-O2/-O3
#                                 the way cgo does, both architectures, decoded per function
#
# Environment:
#   OUT       results (default artifacts/coverage): insn-<cfg>.txt/json, runtime.tsv, asmcalls-<cfg>.txt
#   WORK      where the std test binaries go (default: a fresh mktemp -d under /var/tmp, removed
#             at the end unless KEEP=1). The three configurations take about 6 GB.
#   CONFIGS   default "arm64 amd64-v1 amd64-v3"
#   BRANCHES  branches whose contracts count for criterion 2 (default
#             "main agent/alloc agent/maps agent/ffi agent/iface-alloc"; read with git show)
#   JOBS      parallel go builds / decoder processes (default from MemAvailable, at most 8)
#
# Host rules: at most two heavy jobs at once (this script is one: builds run one configuration
# at a time; the decoders run after the builds), and it waits while MemAvailable < 40 GiB.
set -euo pipefail
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$PATH:/usr/local/go/bin:$HOME/.elan/bin"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
mode="${1:-all}"
OUT="${OUT:-$root/artifacts/coverage}"
CONFIGS="${CONFIGS:-arm64 amd64-v1 amd64-v3}"
BRANCHES="${BRANCHES:-main agent/alloc agent/maps agent/ffi agent/iface-alloc}"
mkdir -p "$OUT"

mem_avail_gib() { awk '/^MemAvailable:/ { print int($2 / 1048576) }' /proc/meminfo; }
wait_mem() {
  while [ "$(mem_avail_gib)" -lt 40 ]; do
    echo "coverage: MemAvailable $(mem_avail_gib) GiB < 40 GiB, waiting" >&2
    sleep 30
  done
}
if [ -z "${JOBS:-}" ]; then
  JOBS=$(( ($(mem_avail_gib) - 40) / 4 ))
  [ "$JOBS" -gt 8 ] && JOBS=8
  [ "$JOBS" -lt 1 ] && JOBS=1
fi

created_work=0
if [ -z "${WORK:-}" ]; then
  WORK="$(mktemp -d -p /var/tmp janus-coverage-std.XXXXXX)"
  created_work=1
fi
cleanup() {
  if [ "$created_work" = 1 ] && [ "${KEEP:-0}" != 1 ]; then rm -rf "$WORK"; fi
}
trap cleanup EXIT

goroot="$(go env GOROOT)"
tool="$WORK/janus-coverage-tool"

build_tool() {
  [ -x "$tool" ] && return
  (cd "$root/scripts/coverage" && GOWORK=off go build -o "$tool" .)
}

cfg_env() { # cfg -> GOARCH/GOAMD64 assignments
  case "$1" in
    arm64) echo "GOARCH=arm64" ;;
    amd64-v1) echo "GOARCH=amd64 GOAMD64=v1" ;;
    amd64-v3) echo "GOARCH=amd64 GOAMD64=v3" ;;
    *) echo "unknown configuration $1" >&2; return 1 ;;
  esac
}

stage_build() {
  local pkgs cfg dir
  # Every std package that has test files (packages without tests are still measured as
  # dependencies of the others).
  pkgs="$(cd "$WORK" && go list -f '{{if or .TestGoFiles .XTestGoFiles}}{{.ImportPath}}{{end}}' std)"
  echo "$pkgs" > "$OUT/std-test-packages.txt"
  for cfg in $CONFIGS; do
    dir="$WORK/$cfg"; mkdir -p "$dir"
    wait_mem
    echo "== build $cfg ($(echo "$pkgs" | wc -l) packages, -p $JOBS)"
    # One package per go invocation (`go test -c -o DIR/` refuses packages sharing a base name);
    # the build cache is shared, so the dependencies are compiled once.
    # shellcheck disable=SC2046
    echo "$pkgs" | (cd "$WORK" && env CGO_ENABLED=0 GOOS=linux $(cfg_env "$cfg") GOFLAGS=-trimpath \
      xargs -P "$JOBS" -I{} sh -c 'go test -c -p 4 -o "$0/$(echo {} | tr / _).test" {} 2>>"$0/build-errors.log" || echo "build failed: {}" >>"$0/build-errors.log"' "$dir")
    # The packages that need cgo (runtime/cgo, internal/runtime/cgobench), with cgo on: their C
    # code (gcc_*.c, compiled by gcc with cgo's default -O2 -g) is measured as kind "c".
    local cc=gcc
    [ "${cfg%%-*}" = arm64 ] && cc=aarch64-linux-gnu-gcc
    for p in runtime/cgo internal/runtime/cgobench; do
      # shellcheck disable=SC2046
      (cd "$WORK" && env CGO_ENABLED=1 CC="$cc" GOOS=linux $(cfg_env "$cfg") GOFLAGS=-trimpath \
        go test -c -o "$dir/cgo_$(echo $p | tr / _).test" "$p" 2>>"$dir/build-errors.log") || echo "cgo build failed: $p" >>"$dir/build-errors.log"
    done
    echo "   $(ls "$dir"/*.test | wc -l) test binaries, $(du -sh "$dir" | cut -f1)"
  done
}

# Criterion 5: a C corpus (scripts/coverage/ccorpus/*.c, plus agent/ffi's examples/cgo/ccover.c
# and cfuncs.c when that branch exists) compiled the way cgo invokes the C compiler
# (-fPIC -pthread -g, CGO_CFLAGS default -O2; also -O0 and -O3), by gcc and clang, for both
# architectures, plus -O3 -march=x86-64-v3 on amd64. Object files are decoded function by function.
cc_configs() {
  cat <<'CFG'
amd64 gcc-O0 gcc -O0
amd64 gcc-O2 gcc -O2
amd64 gcc-O3 gcc -O3
amd64 gcc-O3-v3 gcc -O3 -march=x86-64-v3
amd64 clang-O0 clang -O0
amd64 clang-O2 clang -O2
amd64 clang-O3 clang -O3
amd64 clang-O3-v3 clang -O3 -march=x86-64-v3
arm64 gcc-O0 aarch64-linux-gnu-gcc -O0
arm64 gcc-O2 aarch64-linux-gnu-gcc -O2
arm64 gcc-O3 aarch64-linux-gnu-gcc -O3
arm64 clang-O0 clang --target=aarch64-linux-gnu -O0
arm64 clang-O2 clang --target=aarch64-linux-gnu -O2
arm64 clang-O3 clang --target=aarch64-linux-gnu -O3
CFG
}

stage_cc() {
  build_tool
  (cd "$root" && memguard_lake build janus-decode janus-oracle-amd64 >/dev/null)
  local src="$WORK/ccorpus" arch name cc rest f
  mkdir -p "$src"
  cp "$root"/scripts/coverage/ccorpus/*.c "$src/"
  if git -C "$root" rev-parse -q --verify agent/ffi >/dev/null; then
    git -C "$root" show agent/ffi:examples/cgo/ccover.c > "$src/ccover.c"
    git -C "$root" show agent/ffi:examples/cgo/cfuncs.c > "$src/cfuncs.c"
    git -C "$root" show agent/ffi:examples/cgo/cfuncs.h > "$src/cfuncs.h"
  fi
  : > "$OUT/cc.txt"
  cc_configs | while read -r arch name cc rest; do
    local dir="$WORK/cc/$arch-$name"; mkdir -p "$dir"
    for f in "$src"/*.c; do
      # shellcheck disable=SC2086
      $cc $rest -c -fPIC -pthread -g -I"$src" -o "$dir/$(basename "$f" .c).o" "$f"
    done
    echo "== cc $arch $name ($cc $rest)" | tee -a "$OUT/cc.txt"
    "$tool" insn -c -arch "$arch" -j "$JOBS" -top 25 -cache "$(cache_for "$arch")" \
      -decode "$root/.lake/build/bin/janus-decode" -model "$root/.lake/build/bin/janus-oracle-amd64" \
      -json "$OUT/cc-$arch-$name.json" "$dir"/*.o | tee -a "$OUT/cc.txt"
  done
}

# Verdict cache per decoder executable (amd64 test binaries have ~6M distinct encodings).
cache_for() {
  local exe="$root/.lake/build/bin/janus-decode"
  [ "$1" = amd64 ] && exe="$root/.lake/build/bin/janus-oracle-amd64"
  echo "$WORK/verdicts-$1-$(sha256sum "$exe" | cut -c1-12).txt"
}

stage_insn() {
  local cfg arch
  build_tool
  (cd "$root" && memguard_lake build janus-decode janus-oracle-amd64 >/dev/null)
  for cfg in $CONFIGS; do
    wait_mem
    arch="${cfg%%-*}"
    echo "== insn $cfg"
    "$tool" insn -arch "$arch" -j "$JOBS" -cache "$(cache_for "$arch")" \
      -decode "$root/.lake/build/bin/janus-decode" -model "$root/.lake/build/bin/janus-oracle-amd64" \
      -json "$OUT/insn-$cfg.json" -calls "$OUT/asmcalls-$cfg.txt" "$WORK/$cfg"/*.test | tee "$OUT/insn-$cfg.txt"
  done
}

stage_runtime() {
  build_tool
  echo "== runtime entry points"
  "$tool" runtime -goroot "$goroot" -repo "$root" -branches "$BRANCHES" -o "$OUT/runtime.tsv" \
    -bins "arm64=$WORK/arm64/*.test,amd64=$WORK/amd64-v1/*.test" | tee "$OUT/runtime.txt"
}

case "$mode" in
  build) stage_build ;;
  insn) stage_insn ;;
  runtime) stage_runtime ;;
  asmcalls) stage_insn ;; # the asm-call table is written by the insn pass
  cc) stage_cc ;;
  all) stage_build; stage_insn; stage_runtime; stage_cc ;;
  *) echo "usage: $0 [all|build|insn|runtime|asmcalls|cc]" >&2; exit 2 ;;
esac
echo "results in $OUT"
