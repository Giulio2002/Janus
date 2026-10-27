#!/usr/bin/env bash
# Build the print/println examples (scripts/build-examples-print.sh), extract every proved function
# on both ISAs into artifacts/print/<isa>/<Name>/, and verify examples/proofs-print/<isa>/<Name>.lean
# against it with `janus verify` (kernel check, axiom audit, leanchecker replay). R8: the print
# path is executed from the binary on top of the kernel model (Janus.Kernel.EnsuresK, fd 2); the
# runtime contracts are runtime.lock2/unlock2/memmove (Janus/Contracts/Print*.lean).
#
#   PrintX     println("x =", x) for a uint64 x: "x = " ++ decimal(x) ++ "\n"
#   PrintBool  println(b): "true"/"false" ++ "\n"
#   PrintNeg   print(-17): "-17"
#   PrintStr   println(s): the bytes of s ++ "\n"
#
# The proofs are a consumer package (examples/proofs-print, docs/CONSUMERS.md): per-function lemma
# modules (PrintProofs.<Isa>.Fn*: printlock, recordForPanic, gwrite, printstring, formatBase10, ...)
# that every example imports, and one module per example. `janus verify --proof-root` builds the
# modules once per extraction and the four theorems of an example share that build (and the kernel
# replay). Every example proves `correctness`, `full_output`, `Witness.nonvacuous` (all hypotheses
# satisfiable together, with witness code at the contract addresses) and `Witness.returns`.
# Usage: scripts/verify-print-examples.sh [isa/Name ...]   (default: all, e.g. arm64/PrintX)
# Writes artifacts/print/<isa>/<Name>/verified.json and a summary to
# artifacts/verify-print-examples.txt.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH

all=(PrintX PrintBool PrintNeg PrintStr)
names=("$@")
if [ ${#names[@]} -eq 0 ]; then
  for isa in arm64 amd64; do
    for n in "${all[@]}"; do
      [ -f "examples/proofs-print/PrintProofs/${isa^}/$n.lean" ] && names+=("$isa/$n")
    done
  done
fi

if [ "${JANUS_EXAMPLES_PREBUILT:-}" != 1 ]; then
  go build -o bin/janus ./cmd/janus
  scripts/build-examples-print.sh >/dev/null
fi
# PrintProofs/<Isa>/Code.lean is the code of the binary, and the example modules are generated from
# the Main modules (a stale file fails the run)
python3 -I scripts/gen-print-code.py --check
for i in arm64 amd64; do python3 -I scripts/gen-print-examples.py --check $i; done
extra=()
[ -n "${JANUS_ROOT:-}" ] && extra=(--janus-root "$JANUS_ROOT")

# verify a snapshot of the proof package (a sibling of examples/proofs-print, so that its path
# dependency on the framework resolves the same way): editing the sources while a run is in
# progress does not make it fail with "sources changed during verification"
snap="$(mktemp -d "$root/examples/.print-proofs.XXXXXX")"
trap 'rm -rf "$snap"' EXIT
cp -r examples/proofs-print/. "$snap"/
summary="${JANUS_EXAMPLES_SUMMARY:-$root/artifacts/verify-print-examples.txt}"
: > "$summary"
fail=0
for target in "${names[@]}"; do
  isa="${target%%/*}"; n="${target#*/}"
  out="artifacts/print/$isa/$n"
  mkdir -p "$out"
  # the other examples' entry points as --targets: every extraction holds the code of all four
  # (PrintProofs.<Isa>.Code), each example's own function first
  others=""
  for m in "${all[@]}"; do [ "$m" = "$n" ] || others="${others:+$others,}example.com/print.$m"; done
  bin/janus extract "artifacts/examples-print-$isa" "example.com/print.$n" "$out" --targets "$others" \
    --contract runtime.lock2 --contract runtime.unlock2 --contract runtime.memmove >/dev/null 2>&1
  : > "$out/verify.log"
  start=$(date +%s.%N)
  ok=1
  for thm in correctness full_output Witness.nonvacuous Witness.returns; do
    if ! bin/janus verify "$out" --proof "$snap/PrintProofs/${isa^}/$n.lean" --proof-root "$snap" \
        --theorem "Proof.$thm" \
        ${extra[@]+"${extra[@]}"} >> "$out/verify.log" 2>&1; then
      ok=0; echo "  $isa/$n: Proof.$thm FAILED"
    fi
  done
  t=$(echo "$(date +%s.%N) - $start" | bc)
  if [ $ok = 1 ]; then
    printf '%-18s ok  %6.1fs\n' "$isa/$n" "$t" | tee -a "$summary"
  else
    printf '%-18s FAILED (see %s/verify.log)\n' "$isa/$n" "$out" | tee -a "$summary"
    tail -30 "$out/verify.log"
    fail=1
  fi
done
cat "$summary"
exit $fail
