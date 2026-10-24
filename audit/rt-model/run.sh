#!/usr/bin/env bash
# rt-model red-team rows (docs/AUDIT-MODEL.md). Three axes:
#   SEQ    multi-instruction straight-line blocks on amd64 (host) and arm64 (qemu), full final
#          state compared (axis 2) — the state-threading the single-step oracle cannot reach;
#   CORNER flag/partial-register/shift corners on amd64: ADC/SBB chains, AH/BH partial writes,
#          shifts by 0 or >= width (axis 1, multi-instruction);
#   EX1    the extractor reads `.text`/`.rodata` by *section header*, the kernel loads by
#          *program header*; a tampered `.text` section header runs the real code but is read
#          differently by Janus. validateSegments must reject it (axis 3).
#
# Every SEQ/CORNER batch must report MISMATCH=0; EX1 must reject the tampered binary and accept
# the untampered one. Env: N (amd64 seq per seed, default 5000), AN (arm64 seq, default 5000),
# CN (corner per class, default 5000), SEEDS (default "1 2"). A full sweep: N=40000 AN=40000.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
export PATH="$PATH:/usr/local/go/bin"
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
here="$root/audit/rt-model"
N="${N:-5000}"; AN="${AN:-5000}"; CN="${CN:-5000}"; SEEDS="${SEEDS:-1 2}"
work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
fail=0

echo "== build janus + oracle drivers + Lean models"
go build -o "$work/janus" ./cmd/janus
(cd oracle-amd64 && CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -buildmode=pie -o bin/runner ./cmd/runner && CGO_ENABLED=0 go build -o bin/oracle ./cmd/oracle)
(cd oracle       && CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -o bin/runner ./cmd/runner && CGO_ENABLED=0 go build -o bin/oracle ./cmd/oracle)
lake build janus-oracle janus-oracle-amd64 >/dev/null
MDL64="$root/.lake/build/bin/janus-oracle-amd64"
MDLA64="$root/.lake/build/bin/janus-oracle"

run_amd64 () { # name casesfile
  GODEBUG=asyncpreemptoff=1 ./oracle-amd64/bin/runner < "$2" > "$work/$1.hw" 2>"$work/$1.err" || true
  "$MDL64" < "$2" > "$work/$1.md"
  local line; line=$(python3 "$here/cmp.py" "$work/$1.hw" "$work/$1.md" "$2" | head -1)
  echo "  $1: $line"
  echo "$line" | grep -q 'MISMATCH=0' || { echo "  FAIL ($1)"; python3 "$here/cmp.py" "$work/$1.hw" "$work/$1.md" "$2" | head -8; fail=1; }
}

echo "== SEQ amd64 (straight-line blocks, full-state compare)"
for s in $SEEDS; do
  python3 "$here/seqgen.py" "$N" "$s" "$work/seq$s.jsonl"
  run_amd64 "amd64-seq$s" "$work/seq$s.jsonl"
done

echo "== CORNER amd64 (adc/sbb chains, AH/BH partials, shift-by-0/>=width)"
for m in adc partial shiftzero; do
  python3 "$here/corner.py" "$m" "$CN" 7 "$work/c_$m.jsonl"
  run_amd64 "amd64-$m" "$work/c_$m.jsonl"
done

echo "== SEQ arm64 (qemu; straight-line blocks incl. FP/SIMD)"
if command -v qemu-aarch64 >/dev/null 2>&1; then
  dczid=$(GODEBUG=asyncpreemptoff=1 qemu-aarch64 ./oracle/bin/runner -dczid)
  for s in $SEEDS; do
    python3 "$here/a64seq.py" "$AN" "$s" "$work/a64-$s.jsonl" "$dczid"
    GODEBUG=asyncpreemptoff=1 qemu-aarch64 ./oracle/bin/runner < "$work/a64-$s.jsonl" > "$work/a64-$s.hw" 2>"$work/a64-$s.err" || true
    "$MDLA64" < "$work/a64-$s.jsonl" > "$work/a64-$s.md"
    line=$(python3 "$here/a64cmp.py" "$work/a64-$s.hw" "$work/a64-$s.md" "$work/a64-$s.jsonl" | head -1)
    echo "  arm64-seq$s: $line"
    echo "$line" | grep -q 'MISMATCH=0' || { echo "  FAIL (arm64-seq$s)"; python3 "$here/a64cmp.py" "$work/a64-$s.hw" "$work/a64-$s.md" "$work/a64-$s.jsonl" | head -8; fail=1; }
  done
  # arm64 FP-threading batch (fpsr cumulative flags + V registers across steps)
  python3 "$here/a64seq.py" "$AN" 9 "$work/a64fp.jsonl" "$dczid" fp
  GODEBUG=asyncpreemptoff=1 qemu-aarch64 ./oracle/bin/runner < "$work/a64fp.jsonl" > "$work/a64fp.hw" 2>/dev/null || true
  "$MDLA64" < "$work/a64fp.jsonl" > "$work/a64fp.md"
  line=$(python3 "$here/a64cmp.py" "$work/a64fp.hw" "$work/a64fp.md" "$work/a64fp.jsonl" | head -1)
  echo "  arm64-fp: $line"
  echo "$line" | grep -q 'MISMATCH=0' || { echo "  FAIL (arm64-fp)"; fail=1; }
else
  echo "  (qemu-aarch64 not found; skipping arm64 SEQ)"
fi

echo "== EX1 section/segment disagreement (extractor must reject)"
gen="$work/ex1src"; mkdir -p "$gen"
cat > "$gen/prog.go" <<'EOF'
package main
import "os"
//go:noinline
func Add(x, y uint64) uint64 { return x + y }
var Sink uint64
func main(){ Sink = Add(uint64(len(os.Args)), 2); os.Exit(int(Sink & 1)) }
EOF
cat > "$gen/go.mod" <<'EOF'
module ex
go 1.26
EOF
(cd "$gen" && CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -o "$work/ex1" .)
python3 "$here/ex1_tamper.py" "$work/ex1" "$work/ex1_tamper" 0x40 >/dev/null
# the tampered binary still runs the real code
if "$work/ex1_tamper"; then :; fi
if "$work/janus" extract "$work/ex1" "main.Add" "$work/ex1_ok" >/dev/null 2>&1; then
  echo "  untampered: accepted (OK)"
else
  echo "  FAIL: untampered binary rejected"; fail=1
fi
if "$work/janus" extract "$work/ex1_tamper" "main.Add" "$work/ex1_bad" >/dev/null 2>&1; then
  echo "  FAIL: tampered binary accepted (EX1 not fixed)"; fail=1
else
  echo "  tampered: rejected (OK)"
fi

[ "$fail" = 0 ] && echo "rt-model rows: ALL PASS" || { echo "rt-model rows: FAIL"; exit 1; }
