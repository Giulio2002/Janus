#!/usr/bin/env bash
# Build the example binary, extract every example function into artifacts/<Name>/ and verify
# examples/proofs/<Name>.lean against it with `janus verify` (kernel check, axiom audit,
# leanchecker). Then run the "WrongAdd" demonstration (scripts/break-demo.sh), which checks
# that the Add proof is rejected on a binary where `+` was changed to `-`, and verifies the
# counterexample theorem examples/proofs/WrongAdd.lean on that binary.
#
# Usage: scripts/verify-examples.sh [Name ...]     (default: all examples)
# Set JANUS_ROOT to verify against another checkout of the Janus Lean library.
# Writes artifacts/<Name>/verified.json for each verified proof and a summary table to
# artifacts/verify-examples.txt.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH

all=(Add Max Add128 Mul64 Add256 Div Get AddThree Sum SetOne256 HexDigit AddLimbs CopyWords SumSquares
     AtomicAdd AtomicMax CopyBlock ClearWords A64Equal64 A64IndexByte
     NewPair MakeSlice AppendOne SetNext)
names=("$@")
[ ${#names[@]} -eq 0 ] && names=("${all[@]}" WrongAdd)

go build -o bin/janus ./cmd/janus
scripts/build-examples.sh >/dev/null
(cd "${JANUS_ROOT:-$root}" && lake build Janus >/dev/null)

extra=()
[ -n "${JANUS_ROOT:-}" ] && extra=(--janus-root "$JANUS_ROOT")

. scripts/example-contracts.sh
summary="$root/artifacts/verify-examples.txt"
: > "$summary"
fail=0
for n in "${names[@]}"; do
  if [ "$n" = WrongAdd ]; then
    if scripts/break-demo.sh; then
      echo "WrongAdd  ok  (see scripts/break-demo.sh output)" >> "$summary"
    else
      echo "WrongAdd  FAILED" >> "$summary"; fail=1
    fi
    continue
  fi
  out="artifacts/$n"
  # shellcheck disable=SC2046
  bin/janus extract artifacts/examples-arm64 "$(example_symbol "$n")" "$out" $(example_contracts "$n") >/dev/null
  start=$(date +%s.%N)
  if bin/janus verify "$out" --proof "examples/proofs/$n.lean" "${extra[@]}" > "$out/verify.log" 2>&1; then
    t=$(echo "$(date +%s.%N) - $start" | bc)
    printf '%-9s ok  %6.1fs\n' "$n" "$t" | tee -a "$summary"
  else
    printf '%-9s FAILED (see %s/verify.log)\n' "$n" "$out" | tee -a "$summary"
    tail -30 "$out/verify.log"
    fail=1
  fi
done
cat "$summary"
exit $fail
