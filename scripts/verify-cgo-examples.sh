#!/usr/bin/env bash
# Build the cgo examples (scripts/build-examples-cgo.sh: Go 1.26.0 and gcc 15.2.0 pinned there),
# extract every proved C and Go function on both ISAs into artifacts/cgo/<isa>/<Name>/, and verify
# examples/proofs-cgo/<isa>/<Name>.lean against it with `janus verify` (kernel check, axiom audit,
# leanchecker replay).
#
#   C functions (CEnsures, the C calling convention):   CAdd CSum CStore, CCount (arm64: the
#                                                       gcc -O2 auto-vectorised byte count)
#   Go -> C -> Go, end to end (EnsuresC under the trusted
#   cgocall contract Janus.FFI.CgoCall):                 GoAdd GoSum, GoCount (arm64)
#
# Usage: scripts/verify-cgo-examples.sh [isa/Name ...]   (default: all, e.g. arm64/GoAdd)
# Writes artifacts/cgo/<isa>/<Name>/verified.json and a summary to artifacts/verify-cgo-examples.txt.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH

declare -A sym=(
  [CAdd]=c_add [CSum]=c_sum [CStore]=c_store [CCount]=c_count [GoCount]=example.com/cgo.Count
  [GoAdd]=example.com/cgo.Add [GoSum]=example.com/cgo.Sum
)
names=("$@")
if [ ${#names[@]} -eq 0 ]; then
  for isa in arm64 amd64; do
    for n in CAdd CSum CStore GoAdd GoSum; do names+=("$isa/$n"); done
    [ "$isa" = arm64 ] && names+=("$isa/CCount" "$isa/GoCount")
  done
fi

go build -o bin/janus ./cmd/janus
scripts/build-examples-cgo.sh >/dev/null
lake build Janus >/dev/null

summary="$root/artifacts/verify-cgo-examples.txt"
: > "$summary"
fail=0
for target in "${names[@]}"; do
  isa="${target%%/*}"; n="${target#*/}"
  out="artifacts/cgo/$isa/$n"
  # `runtime.convT64` is only called on the dead `if _Cgo_always_false` branch of the cgo
  # wrappers: a contract (not extracted; the proofs show the branch is never taken)
  bin/janus extract "artifacts/examples-cgo-$isa" "${sym[$n]}" "$out" --contract runtime.convT64 >/dev/null 2>&1
  start=$(date +%s.%N)
  if bin/janus verify "$out" --proof "examples/proofs-cgo/$isa/$n.lean" --janus-root . > "$out/verify.log" 2>&1; then
    t=$(echo "$(date +%s.%N) - $start" | bc)
    printf '%-12s ok  %6.1fs\n' "$isa/$n" "$t" | tee -a "$summary"
  else
    printf '%-12s FAILED (see %s/verify.log)\n' "$isa/$n" "$out" | tee -a "$summary"
    tail -30 "$out/verify.log"
    fail=1
  fi
done
cat "$summary"
exit $fail
