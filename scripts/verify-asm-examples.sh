#!/usr/bin/env bash
# Build the Go assembly examples (scripts/build-examples-asm.sh: examples/asm, Go 1.26.0 pinned
# there), extract every proved function on both ISAs into artifacts/asm/<isa>/<Name>/, and verify
# examples/asm/proofs/<isa>/<Name>.lean against it with `janus verify` (kernel check, axiom audit,
# leanchecker replay). docs/ABI0.md describes the examples.
#
#   Go assembly, ABI0 (Ensures0):                          AddAsm XorSlice Twice
#   Go calling assembly with a direct ABI0 call (Ensures): CallXor
#   the ABIInternal -> ABI0 wrapper (Ensures):            XorWrapper
#   (Twice also goes through the ABI0 -> ABIInternal wrapper double.abi0 into Go.)
#
# Usage: scripts/verify-asm-examples.sh [-j N] [isa/Name ...]   (default: all, e.g. amd64/Twice)
# A verification also fails if `janus verify` warns that the statement uses the other calling
# convention than the entry. Writes artifacts/asm/<isa>/<Name>/verified.json and a summary to
# artifacts/verify-asm-examples.txt (unless JANUS_EXAMPLES_SUMMARY names another file).
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

declare -A sym=(
  [AddAsm]=example.com/asm.AddAsm.abi0 [XorSlice]=example.com/asm.XorSlice.abi0
  [Twice]=example.com/asm.Twice.abi0 [CallXor]=example.com/asm.CallXor
  [XorWrapper]=example.com/asm.XorSlice
)
names=("$@")
if [ ${#names[@]} -eq 0 ]; then
  for isa in arm64 amd64; do
    for n in AddAsm XorSlice Twice CallXor XorWrapper; do names+=("$isa/$n"); done
  done
fi

# JANUS_EXAMPLES_PREBUILT=1 (scripts/verify-all-examples.sh): bin/janus and the binaries exist.
if [ "${JANUS_EXAMPLES_PREBUILT:-}" != 1 ]; then
  go build -o bin/janus ./cmd/janus
  scripts/build-examples-asm.sh >/dev/null
fi

summary="${JANUS_EXAMPLES_SUMMARY:-$root/artifacts/verify-asm-examples.txt}"
: > "$summary"
lines="$(mktemp -d)"
broken=()

verify_one() {
  local target=$1 isa n out start t
  isa="${target%%/*}"; n="${target#*/}"
  out="artifacts/asm/$isa/$n"
  bin/janus extract "artifacts/examples-asm-$isa" "${sym[$n]}" "$out" >/dev/null
  start=$(date +%s.%N)
  if bin/janus verify "$out" --proof "examples/asm/proofs/$isa/$n.lean" --janus-root . > "$out/verify.log" 2>&1 &&
      ! grep -q '^Warning: the entry function follows' "$out/verify.log"; then
    t=$(echo "$(date +%s.%N) - $start" | bc)
    printf '%-17s ok  %6.1fs  %s\n' "$isa/$n" "$t" "$(grep -m1 '  Entry:' "$out/verify.log" | sed 's/^ *Entry: //')" | tee "$lines/${isa}_$n"
  else
    printf '%-17s FAILED (see %s/verify.log)\n' "$isa/$n" "$out" | tee "$lines/${isa}_$n"
    tail -30 "$out/verify.log"
    broken+=("$target")
  fi
}

for target in "${names[@]}"; do
  par_run 'verify_one "$target"'
done
par_wait
for target in "${names[@]}"; do
  f="$lines/${target%%/*}_${target#*/}"
  if [ -f "$f" ]; then cat "$f" >> "$summary"; else echo "$target  FAILED (no result)" >> "$summary"; broken+=("$target"); fi
done
rm -rf "$lines"
echo
cat "$summary"
# (failures inside par_run jobs are only visible in their summary lines)
[ ${#broken[@]} -eq 0 ] && ! grep -q FAILED "$summary"
