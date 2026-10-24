#!/usr/bin/env bash
# Build the example binary, extract every example function into artifacts/<Name>/ and verify
# examples/proofs/<Name>.lean against it with `janus verify` (kernel check, axiom audit,
# leanchecker). Then run the "WrongAdd" demonstration (scripts/break-demo.sh), which checks
# that the Add proof is rejected on a binary where `+` was changed to `-`, and verifies the
# counterexample theorem examples/proofs/WrongAdd.lean on that binary.
#
# Usage: scripts/verify-examples.sh [-j N] [Name ...]     (default: all examples)
#   -j N   verify up to N proofs at once (default: $JANUS_JOBS, else the number of cores capped
#          by memory, see scripts/lib/parallel.sh); -j 1 verifies them one after the other.
# Set JANUS_ROOT to verify against another checkout of the Janus Lean library.
# Writes artifacts/<Name>/verified.json for each verified proof and a summary table to
# artifacts/verify-examples.txt.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
par_init "$@"
set -- ${PAR_ARGS[@]+"${PAR_ARGS[@]}"}

all=(Add Max Add128 Mul64 Add256 Div Get AddThree Sum SetOne256 HexDigit AddLimbs CopyWords SumSquares
     AtomicAdd AtomicMax CopyBlock ClearWords A64Equal64 A64IndexByte A64Crc32
     HashWith HashTwice MapSum DeferAdd AddF64 Dot3 F64ToU64 Abs
     NewPair MakeSlice AppendOne SetNext MallocFast
     Lookup Insert InsertGet Delete SumValues CountKeys LookupKey16 NewMap ClearMap MapAccess1Small)
names=("$@")
[ ${#names[@]} -eq 0 ] && names=("${all[@]}" WrongAdd)

# JANUS_EXAMPLES_PREBUILT=1 (scripts/verify-all-examples.sh): bin/janus and the examples binary
# are already built.
if [ "${JANUS_EXAMPLES_PREBUILT:-}" != 1 ]; then
  go build -o bin/janus ./cmd/janus
  scripts/build-examples.sh >/dev/null
fi
# The verifier builds the framework it uses itself (the embedded one in the cache, or the
# JANUS_ROOT checkout in place) under its lock; build a JANUS_ROOT checkout first only so that
# its build errors show up before any proof runs.
[ -n "${JANUS_ROOT:-}" ] && [ "${JANUS_EXAMPLES_PREBUILT:-}" != 1 ] && (cd "$JANUS_ROOT" && memguard_lake build Janus >/dev/null)

extra=()
[ -n "${JANUS_ROOT:-}" ] && extra=(--janus-root "$JANUS_ROOT")

. scripts/example-contracts.sh
summary="${JANUS_EXAMPLES_SUMMARY:-$root/artifacts/verify-examples.txt}"
: > "$summary"
lines="$(mktemp -d)"
broken=()

# verify_one NAME: verify one example (or the WrongAdd demonstration); prints its summary line
# (also kept in $lines/NAME for the summary file) and records a failure in `broken`.
verify_one() {
  local n=$1 out t start
  if [ "$n" = WrongAdd ]; then
    if scripts/break-demo.sh > "$lines/WrongAdd.log" 2>&1; then
      echo "WrongAdd  ok  (see scripts/break-demo.sh output)" | tee "$lines/$n"
    else
      echo "WrongAdd  FAILED" | tee "$lines/$n"; cat "$lines/WrongAdd.log"; broken+=("$n")
    fi
    return 0
  fi
  out="artifacts/$n"
  mapfile -t extract_args < <(scripts/example-targets.sh "$n")
  bin/janus extract artifacts/examples-arm64 "$(example_symbol "$n")" "$out" "${extract_args[@]}" >/dev/null
  start=$(date +%s.%N)
  if bin/janus verify "$out" --proof "examples/proofs/$n.lean" ${extra[@]+"${extra[@]}"} > "$out/verify.log" 2>&1; then
    t=$(echo "$(date +%s.%N) - $start" | bc)
    printf '%-9s ok  %6.1fs\n' "$n" "$t" | tee "$lines/$n"
    # further theorems of the same proof file (F64ToU64's `exact` and `saturation`, ...)
    local thm
    for thm in $(grep -oE '^theorem (exact|saturation)' "examples/proofs/$n.lean" | awk '{print $2}'); do
      if bin/janus verify "$out" --proof "examples/proofs/$n.lean" --theorem "Proof.$thm" \
          ${extra[@]+"${extra[@]}"} >> "$out/verify.log" 2>&1; then
        printf '%-9s ok  (Proof.%s)\n' "$n" "$thm" | tee -a "$lines/$n"
      else
        printf '%-9s FAILED Proof.%s (see %s/verify.log)\n' "$n" "$thm" "$out" | tee -a "$lines/$n"
        broken+=("$n")
      fi
    done
  else
    printf '%-9s FAILED (see %s/verify.log)\n' "$n" "$out" | tee "$lines/$n"
    tail -30 "$out/verify.log"
    broken+=("$n")
  fi
}

wall=$(date +%s.%N)
for n in "${names[@]}"; do
  par_run 'verify_one "$n"'
done
par_wait
for n in "${names[@]}"; do
  if [ -f "$lines/$n" ]; then cat "$lines/$n" >> "$summary"; else echo "$n  FAILED (no result)" >> "$summary"; broken+=("$n"); fi
done
rm -rf "$lines"
printf 'total     %s  %6.1fs wall (-j %s)\n' "$([ ${#broken[@]} -eq 0 ] && echo ok || echo FAILED)" \
  "$(echo "$(date +%s.%N) - $wall" | bc)" "$PAR_JOBS" >> "$summary"
echo
cat "$summary"
[ ${#broken[@]} -eq 0 ]
