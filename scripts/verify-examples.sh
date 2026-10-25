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
     AtomicAdd AtomicMax CopyBlock ClearWords A64Equal64 A64IndexByte A64Crc32 A64CountByte
     HashWith HashTwice MapSum DeferAdd AddF64 Dot3 F64ToU64 Abs
     NewPair MakeSlice AppendOne SetNext MallocFast
     Lookup Insert InsertGet Delete SumValues CountKeys LookupKey16 NewMap ClearMap MapAccess1Small
     LookupS InsertS DeleteS LookupK24 InsertK24 Has32 Set32 InsertPtr LookupPtr MakeHint
     Triangle GotoSum Find2D RowsWith Log2 TotalMeters TotalFeet Fact SumBelow ReverseArray DivMod10
     SwapBig Compose DotBoth BitMerge Shifts MinMax ClearArray IterSum Sum3 AlignUp Slice3
     Slice2 Mod IncTwice Bump GlobalTable Table MakeAdder
     Box AsHasher Classify Equal
     Eq32 StrEq F64Eq CopyTrees ClearTrees LookupStr HashFKey EqFKey
     I64ToF64 F64ToI64 U64ToF64 F64ToF32 F32ToF64 LoadThird SpanSum MinF64 MaxF64 MinStr)
. scripts/example-contracts.sh
# the runtime's equality, hashing and typed-memory functions verified from their code
all+=($runtime_examples $runtime_examples_arm64_only)
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
. scripts/lib/theorems.sh
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
  # The theorems of the proof file: correctness, further theorems (F64ToU64's `exact` and
  # `saturation`, ...) and the non-vacuity witnesses (Proof.Witness.nonvacuous / .returns: the
  # theorem's hypotheses hold together for a model of the runtime, and its conclusion is
  # reached); up to two verified at once (scripts/lib/theorems.sh).
  local -a thms=(Proof.correctness)
  local thm i st
  for thm in $(grep -oE '^theorem (exact|saturation|faults)' "examples/proofs/$n.lean" | awk '{print $2}' || true); do thms+=("Proof.$thm"); done
  if grep -q '^namespace Witness' "examples/proofs/$n.lean"; then thms+=(Proof.Witness.nonvacuous Proof.Witness.returns); fi
  st="$(mktemp -d)"
  start=$(date +%s.%N)
  verify_theorems "$out" "examples/proofs/$n.lean" "$st" "${thms[@]}" -- ${extra[@]+"${extra[@]}"}
  t=$(echo "$(date +%s.%N) - $start" | bc)
  cat "$st"/*.log > "$out/verify.log" 2>/dev/null || true
  if [ "$(cat "$st/0.rc")" = 0 ]; then
    printf '%-9s ok  %6.1fs\n' "$n" "$t" | tee "$lines/$n"
    for ((i = 1; i < ${#thms[@]}; i++)); do
      if [ "$(cat "$st/$i.rc")" = 0 ]; then
        printf '%-9s ok  (%s)\n' "$n" "${thms[$i]}" | tee -a "$lines/$n"
      else
        printf '%-9s FAILED %s (see %s/verify.log)\n' "$n" "${thms[$i]}" "$out" | tee -a "$lines/$n"
        broken+=("$n")
      fi
    done
    rm -rf "$st"
  else
    printf '%-9s FAILED (see %s/verify.log)\n' "$n" "$out" | tee "$lines/$n"
    tail -30 "$st/0.log"
    rm -rf "$st"
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
