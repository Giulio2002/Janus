#!/usr/bin/env bash
# Build the cgo examples (scripts/build-examples-cgo.sh: Go 1.26.0 and gcc 15.2.0 pinned there),
# extract every proved C and Go function on both ISAs into artifacts/cgo/<isa>/<Name>/, and verify
# examples/proofs-cgo/<isa>/<Name>.lean against it with `janus verify` (kernel check, axiom audit,
# leanchecker replay).
#
#   C functions (CEnsures, the C calling convention):   CAdd CSum CStore, CCount (arm64: the
#                                                       gcc -O2 auto-vectorised byte count)
#   C functions under the classified C ABI (CEnsuresR):  KStack10 KFP KPMix KBig KVSum
#   Go -> C -> Go, end to end (EnsuresC under the trusted
#   cgocall contract Janus.FFI.CgoCall):                 GoAdd GoSum, GoCount (arm64)
#                                                        GoStack10 GoFP GoPMix GoBig GoVSum8
#   amd64 only, C compiled by clang -O2 (SSE2-vectorised,
#   artifacts/examples-cgo-clang-amd64):                 CSum32 GoSum32
#
# Usage: scripts/verify-cgo-examples.sh [isa/Name ...]   (default: all, e.g. arm64/GoAdd)
# Writes artifacts/cgo/<isa>/<Name>/verified.json and a summary to artifacts/verify-cgo-examples.txt.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH

declare -A sym=(
  [CAdd]=c_add [CSum]=c_sum [CStore]=c_store [CCount]=c_count [GoCount]=example.com/cgo/neon.Count
  [GoAdd]=example.com/cgo.Add [GoSum]=example.com/cgo.Sum
  [KStack10]=k_stack10 [KFP]=k_fp [KPMix]=k_pmix [KBig]=k_big [KVSum]=k_vsum
  [GoStack10]=example.com/cgo/cabi.Stack10 [GoFP]=example.com/cgo/cabi.FP
  [GoPMix]=example.com/cgo/cabi.PMix [GoBig]=example.com/cgo/cabi.Big
  [GoVSum8]=example.com/cgo/cabi.VSum8
  [CSum32]=c_sum32 [GoSum32]=example.com/cgo/vec.Sum32
)
all=(CAdd CSum CStore GoAdd GoSum KStack10 KFP KPMix KBig KVSum GoStack10 GoFP GoPMix GoBig GoVSum8)
# the examples whose binary is the clang-built one
declare -A clang=([CSum32]=1 [GoSum32]=1)
names=("$@")
if [ ${#names[@]} -eq 0 ]; then
  for isa in arm64 amd64; do
    for n in "${all[@]}"; do names+=("$isa/$n"); done
    [ "$isa" = arm64 ] && names+=("$isa/CCount" "$isa/GoCount")
  done
  names+=(amd64/CSum32 amd64/GoSum32)
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
  # `runtime.convT64`, `convT32` and `convTnoptr` are only called on the dead
  # `if _Cgo_always_false` branch of the cgo wrappers: contracts (not extracted; the proofs show
  # the branch is never taken)
  binary="artifacts/examples-cgo-$isa"
  [ -n "${clang[$n]:-}" ] && binary="artifacts/examples-cgo-clang-$isa"
  bin/janus extract "$binary" "${sym[$n]}" "$out" --contract runtime.convT64 \
    --contract runtime.convT32 --contract runtime.convTnoptr >/dev/null 2>&1
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
