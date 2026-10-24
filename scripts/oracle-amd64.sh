#!/usr/bin/env bash
# Differential test of the Lean x86-64 model (Janus.Amd64.step) against native execution on
# the x86-64 host (single-stepped, see oracle-amd64/cmd/runner). See docs/ORACLE-AMD64.md.
#
#   scripts/oracle-amd64.sh selftest   build, then check the native harness on known answers
#   scripts/oracle-amd64.sh quick      generated cases only (~100k)
#   scripts/oracle-amd64.sh full       generated + harvested from real Go amd64 binaries (default)
#
# Environment: OUT (default artifacts/oracle-amd64), JOBS (default 16, at most 24), N
# (encodings per targeted spec, default 600 full / 250 quick), GROUP (random byte strings,
# default 40000 full / 15000 quick), K (states per harvested instruction, default 3),
# PER_CLASS (harvested distinct instructions per modeled class, default 4000), SEED (default 1),
# MODEL (default .lake/build/bin/janus-oracle-amd64; e.g. MODEL=oracle-amd64/bin/fakemodel
# to exercise the pipeline without the Lean model).
set -euo pipefail
# Example binaries (and so every address a proof depends on) are built with exactly this Go
# release, whatever Go is installed; the go command downloads it on first use.
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
mode="${1:-full}"
export PATH="$PATH:/usr/local/go/bin"
OUT="${OUT:-$root/artifacts/oracle-amd64}"
JOBS="${JOBS:-16}"
[ "$JOBS" -gt 24 ] && JOBS=24
SEED="${SEED:-1}"
K="${K:-3}"
PER_CLASS="${PER_CLASS:-4000}"
MODEL="${MODEL:-$root/.lake/build/bin/janus-oracle-amd64}"
bin="$root/oracle-amd64/bin"

echo "== build"
(cd "$root/oracle-amd64" &&
  CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -buildmode=pie -o "$bin/runner" ./cmd/runner &&
  CGO_ENABLED=0 go build -o "$bin/oracle" ./cmd/oracle &&
  go build -o "$bin/fakemodel" ./cmd/fakemodel)
if [ "$MODEL" = "$root/.lake/build/bin/janus-oracle-amd64" ]; then
  (cd "$root" && memguard_lake build janus-oracle-amd64)
fi

echo "== harness self-test"
"$bin/oracle" selftest -runner "$bin/runner" > "$bin/selftest.log" || { cat "$bin/selftest.log"; exit 1; }
tail -1 "$bin/selftest.log"
[ "$mode" = selftest ] && exit 0

mkdir -p "$OUT"
cases=()
case "$mode" in
  quick) N="${N:-250}"; GROUP="${GROUP:-15000}" ;;
  full)  N="${N:-600}"; GROUP="${GROUP:-40000}" ;;
  *) echo "usage: $0 selftest|quick|full" >&2; exit 2 ;;
esac
echo "== generate ($N encodings per targeted spec, $GROUP random)"
"$bin/oracle" gen -n "$N" -group "$GROUP" -seed "$SEED" -o "$OUT/gen.jsonl"
cases+=("$OUT/gen.jsonl")

if [ "$mode" = full ]; then
  echo "== harvest corpus (real Go amd64 code)"
  corpus="$bin/corpus"
  mkdir -p "$corpus"
  (cd "$root/oracle-amd64" &&
    CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v1 go build -o "$corpus/bigprog" ./harvest/bigprog &&
    for p in math/big strconv sort crypto/sha256 bytes strings math/bits encoding/binary sync/atomic; do
      CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v1 go test -c -o "$corpus/${p//\//_}.test" "$p"
    done)
  if [ ! -f "$root/artifacts/examples-amd64" ]; then
    (cd "$root/examples/basic" && CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -trimpath -o "$root/artifacts/examples-amd64" ./cmd)
  fi
  "$bin/oracle" harvest -k "$K" -per-class "$PER_CLASS" -seed "$((SEED + 1))" -o "$OUT/harvest.jsonl" \
    "$corpus"/* "$root/artifacts/examples-amd64"
  cases+=("$OUT/harvest.jsonl")
fi

echo "== run (native vs $(basename "$MODEL"))"
IFS=, eval 'list="${cases[*]}"'
"$bin/oracle" run -runner "$bin/runner" -model "$MODEL" -j "$JOBS" -cases "$list" -out "$OUT" > /dev/null
if grep -q '"verdict":"MISMATCH"' "$OUT/verdicts.jsonl"; then
  echo "== minimize mismatches"
  "$bin/oracle" minimize -runner "$bin/runner" -model "$MODEL" -out "$OUT" -max 200 > /dev/null
  echo "minimal reproductions: $OUT/repro.md"
fi
sed -n '1,6p' "$OUT/summary.md"
echo "report: $OUT/summary.md  (per-case verdicts: $OUT/verdicts.jsonl)"
if grep -q '"verdict":"MISMATCH"' "$OUT/verdicts.jsonl"; then
  echo "FAIL: model disagrees with hardware (see $OUT/repro.md)" >&2
  exit 1
fi
