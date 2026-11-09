#!/usr/bin/env bash
# Row RT-PRINT: the Go 1.26 builtin print/println output (runtime/print.go, internal/strconv
# ftoa/Dragonbox/ctoa) against the Lean spec Janus.Spec.Print, byte for byte, on linux/amd64
# (native) and linux/arm64 (qemu-aarch64).
#
#   audit/rt-print/run.sh                   default: RTPRINT_N=200000 random float64 bit patterns
#   RTPRINT_N=50000 audit/rt-print/run.sh   (and as many float32; the other counts scale with it)
#   RTPRINT_SEED=7 ...                      another deterministic corpus
#
# Writes only to a mktemp directory (and the Go build cache). Exits 1 on any mismatch.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=../../scripts/lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
here="$root/audit/rt-print"
cd "$root" || exit 1
export PATH="$HOME/.elan/bin:/usr/local/go/bin:$PATH"
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
QEMU="${QEMU:-$(command -v qemu-aarch64 || echo /usr/bin/qemu-aarch64)}"
N="${RTPRINT_N:-200000}"
SEED="${RTPRINT_SEED:-1}"
W="$(mktemp -d "${TMPDIR:-/tmp}/rt-print.XXXXXX")"
trap 'rm -rf "$W"' EXIT
t0=$(date +%s)

echo "== build: Go generator (amd64, arm64), Lean spec + Diff (compiled to C, linked with leanc)"
(cd "$here/gen" && CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -o "$W/gen-amd64" . &&
  CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -o "$W/gen-arm64" .) || exit 1
mkdir -p "$W/olean/Janus/Spec" "$W/c"
memguard_run -n rt-print-lean -- lean -R . -o "$W/olean/Janus/Spec/Print.olean" \
  -c "$W/c/Print.c" Janus/Spec/Print.lean || exit 1
LEAN_PATH="$W/olean" memguard_run -n rt-print-lean -- lean -R . -c "$W/c/Diff.c" \
  audit/rt-print/Diff.lean || exit 1
leanc -O2 -o "$W/diff" "$W/c/Print.c" "$W/c/Diff.c" || exit 1

# GOGC is off inside the generator; invalidptr=0 because pointer cases carry fabricated words.
export GODEBUG=invalidptr=0
echo "== run: Go runtime print (amd64 native, arm64 under qemu), Lean spec"
"$W/gen-amd64" -seed "$SEED" -n "$N" >"$W/cases-amd64.txt" 2>"$W/go-amd64.out" || exit 1
"$QEMU" "$W/gen-arm64" -seed "$SEED" -n "$N" >"$W/cases-arm64.txt" 2>"$W/go-arm64.out" || exit 1
if ! cmp -s "$W/cases-amd64.txt" "$W/cases-arm64.txt"; then
  echo "error: the amd64 and arm64 generators produced different case lists"; exit 1
fi
memguard_run -n rt-print-diff -- "$W/diff" "$W/cases-amd64.txt" >"$W/lean.out" || exit 1
cases=$(wc -l <"$W/cases-amd64.txt")

status=0
count() { # count GO_OUT -> number of differing lines (0 iff byte-identical)
  if cmp -s "$1" "$W/lean.out"; then echo 0; return; fi
  diff --text "$1" "$W/lean.out" | grep -c '^<' || true
}
report() { # report ISA GO_OUT
  echo "first mismatches ($1), '<' Go runtime, '>' Lean spec:"
  diff --text "$2" "$W/lean.out" | head -12
  echo "matching cases (case-file line = id + 1):"
  diff --text "$2" "$W/lean.out" | grep -a '^<' | head -6 | while read -r _ i _; do
    sed -n "$((i + 1))p" "$W/cases-amd64.txt"
  done
}
ma=$(count "$W/go-amd64.out"); mr=$(count "$W/go-arm64.out")
[ "$ma" = 0 ] || { status=1; report amd64 "$W/go-amd64.out"; }
[ "$mr" = 0 ] || { status=1; report arm64 "$W/go-arm64.out"; }
echo "print-diff: $cases cases, $ma mismatches (amd64), $mr mismatches (arm64) [$(($(date +%s) - t0))s]"
exit $status
