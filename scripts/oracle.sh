#!/usr/bin/env bash
# Differential test of the Lean AArch64 model (Janus.Arm64.step) against native execution
# under qemu-aarch64. See docs/ORACLE.md.
#
#   scripts/oracle.sh selftest        build, then check the native harness on known answers
#   scripts/oracle.sh quick           ~60k generated cases
#   scripts/oracle.sh full            generated + harvested from real Go arm64 binaries (default)
#   scripts/oracle.sh fp              scalar floating point only: generated fp.* classes (FP_K
#                                     states per word) + harvested fp.* words (FP_HARVEST_K states)
#
# Environment: OUT (default artifacts/oracle), JOBS (default nproc), N (words per generated
# class, default 4000 for full / 1500 for quick), K (states per harvested word, default 3),
# PER_CLASS (harvested distinct words per class, default 8000), SEED (default 1), FP_K (states
# per generated fp.* word, default 4), FP_HARVEST_K (states per harvested fp.* word in fp mode, 40),
# QEMU (default /usr/bin/qemu-aarch64; set QEMU= to run natively on an arm64 Linux host).
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mode="${1:-full}"
export PATH="$PATH:/usr/local/go/bin"
OUT="${OUT:-$root/artifacts/oracle}"
JOBS="${JOBS:-$(nproc)}"
SEED="${SEED:-1}"
K="${K:-3}"
PER_CLASS="${PER_CLASS:-8000}"
QEMU="${QEMU-/usr/bin/qemu-aarch64}"
bin="$root/oracle/bin"

echo "== build"
(cd "$root/oracle" &&
  CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -o "$bin/runner" ./cmd/runner &&
  go build -o "$bin/oracle" ./cmd/oracle)
(cd "$root" && lake build janus-oracle)
common=(-qemu "$QEMU" -runner "$bin/runner")
# DCZID_EL0 is IMPLEMENTATION DEFINED: every case carries the reference CPU's own value (the
# Lean side uses it as State.dczid; the runner refuses a case with a different one).
DCZID="$(GODEBUG=asyncpreemptoff=1 ${QEMU:+"$QEMU"} "$bin/runner" -dczid)"
echo "== reference DCZID_EL0 = $DCZID"

echo "== harness self-test"
"$bin/oracle" selftest "${common[@]}" -dczid "$DCZID" > "$bin/selftest.log" || { cat "$bin/selftest.log"; exit 1; }
tail -1 "$bin/selftest.log"
[ "$mode" = selftest ] && exit 0

mkdir -p "$OUT"
cases=()
case "$mode" in
  quick) N="${N:-1500}" ;;
  full)  N="${N:-4000}" ;;
  fp)    N="${N:-20000}" ;;
  *) echo "usage: $0 selftest|quick|full|fp" >&2; exit 2 ;;
esac
FP_K="${FP_K:-4}"
echo "== generate ($N words per class)"
if [ "$mode" = fp ]; then
  "$bin/oracle" gen -dczid "$DCZID" -n "$N" -only '^fp\.' -fp-k "$FP_K" -seed "$SEED" -o "$OUT/gen.jsonl"
else
  "$bin/oracle" gen -dczid "$DCZID" -n "$N" -group "$((N * 2))" -seed "$SEED" -o "$OUT/gen.jsonl"
fi
cases+=("$OUT/gen.jsonl")

if [ "$mode" = full ] || [ "$mode" = fp ]; then
  echo "== harvest corpus (real Go arm64 code)"
  corpus="$bin/corpus"
  mkdir -p "$corpus"
  (cd "$root/oracle" &&
    CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -o "$corpus/bigprog" ./harvest/bigprog &&
    for p in math math/big strconv sort crypto/sha256 bytes strings sync/atomic runtime; do
      CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go test -c -o "$corpus/${p//\//_}.test" "$p"
    done)
  extra=()
  for f in "$root"/artifacts/*-arm64; do [ -f "$f" ] && extra+=("$f"); done
  hargs=()
  [ "$mode" = fp ] && hargs=(-only '^fp\.' -per-class 0 -fp-k "${FP_HARVEST_K:-40}")
  "$bin/oracle" harvest -dczid "$DCZID" -k "$K" -per-class "$PER_CLASS" "${hargs[@]}" -seed "$((SEED + 1))" -o "$OUT/harvest.jsonl" "$corpus"/* "${extra[@]}"
  cases+=("$OUT/harvest.jsonl")
fi

echo "== run (native under ${QEMU:-native} vs janus-oracle)"
IFS=, eval 'list="${cases[*]}"'
"$bin/oracle" run "${common[@]}" -model "$root/.lake/build/bin/janus-oracle" -j "$JOBS" -cases "$list" -out "$OUT" > /dev/null
if grep -q '"verdict":"MISMATCH"' "$OUT/verdicts.jsonl"; then
  echo "== minimize mismatches"
  "$bin/oracle" minimize "${common[@]}" -model "$root/.lake/build/bin/janus-oracle" -out "$OUT" -max 200 > /dev/null
  echo "minimal reproductions: $OUT/repro.md"
fi
sed -n '1,6p' "$OUT/summary.md"
echo "report: $OUT/summary.md  (per-case verdicts: $OUT/verdicts.jsonl)"
if grep -q '"verdict":"MISMATCH"' "$OUT/verdicts.jsonl"; then
  echo "FAIL: model disagrees with hardware (see $OUT/repro.md)" >&2
  exit 1
fi
