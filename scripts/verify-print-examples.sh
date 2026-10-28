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
# Usage: scripts/verify-print-examples.sh [-j N] [--list] [isa/Name ...]   (default: all, e.g. arm64/PrintX)
#   -j N     rows at once (default: $JANUS_JOBS, else see scripts/lib/parallel.sh)
#   --list   print the default rows, one per line, and exit (scripts/verify-all-examples.sh queues them).
# Writes artifacts/print/<isa>/<Name>/verified.json and a summary to
# artifacts/verify-print-examples.txt.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
. "$root/scripts/lib/itemtimeout.sh"
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"

all=(PrintX PrintBool PrintNeg PrintStr)
default_rows() {
  local isa n
  for isa in arm64 amd64; do
    for n in "${all[@]}"; do
      [ ! -f "examples/proofs-print/PrintProofs/${isa^}/$n.lean" ] || echo "$isa/$n"
    done
  done
}
if [ "${1:-}" = --list ]; then default_rows; exit 0; fi
memguard_self "$@"
par_init "$@"
set -- ${PAR_ARGS[@]+"${PAR_ARGS[@]}"}
names=("$@")
[ ${#names[@]} -gt 0 ] || mapfile -t names < <(default_rows)

if [ "${JANUS_EXAMPLES_PREBUILT:-}" != 1 ]; then
  CGO_ENABLED=0 go build -o bin/janus ./cmd/janus
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
# (JANUS_PRINT_SNAPSHOT=DIR: scripts/verify-all-examples.sh made one snapshot for all its print items,
# so that they share the consumer workspace and the lemma modules built in it)
if [ -n "${JANUS_PRINT_SNAPSHOT:-}" ] && [ -d "$JANUS_PRINT_SNAPSHOT/PrintProofs" ]; then
  snap="$JANUS_PRINT_SNAPSHOT"
else
  snap="$(mktemp -d "$root/examples/.print-proofs.XXXXXX")"
  trap 'rm -rf "$snap"' EXIT
  cp -r examples/proofs-print/. "$snap"/
fi
. scripts/lib/incr.sh
summary="${JANUS_EXAMPLES_SUMMARY:-$root/artifacts/verify-print-examples.txt}"
: > "$summary"
lines="$(mktemp -d)"
broken=()
verify_one() {
  local target=$1 isa n out others m start t ok thm
  isa="${target%%/*}"; n="${target#*/}"
  out="artifacts/print/$isa/$n"
  mkdir -p "$out"
  # the other examples' entry points as --targets: every extraction holds the code of all four
  # (PrintProofs.<Isa>.Code), each example's own function first
  others=""
  for m in "${all[@]}"; do [ "$m" = "$n" ] || others="${others:+$others,}example.com/print.$m"; done
  bin/janus extract "artifacts/examples-print-$isa" "example.com/print.$n" "$out" --targets "$others" \
    --contract runtime.lock2 --contract runtime.unlock2 --contract runtime.memmove >/dev/null 2>&1
  # the incremental gate (scripts/lib/incr.sh): skipped only on the record of a PASS with identical inputs.
  # The package is the consumer workspace of the proof: its sources (the live tree: the snapshot is a copy
  # of it), checked against the embedded framework and the checkout its lakefile depends on.
  local -a ispec=(--fw embedded --fw dir:. --pkg examples/proofs-print --proof "examples/proofs-print/PrintProofs/${isa^}/$n.lean"
    --art "$out" --arg "sym:example.com/print.$n" --arg "targets:$others" --arg thm:correctness --arg thm:full_output
    --arg thm:Witness.nonvacuous --arg thm:Witness.returns)
  [ -z "${JANUS_ROOT:-}" ] || ispec+=(--arg "janus-root:$JANUS_ROOT")
  if incr_begin "print:$target" print "${ispec[@]}"; then echo "$INCR_MSG" | tee "$lines/${isa}_$n"; return 0; fi
  : > "$out/verify.log"
  start=$(date +%s.%N)
  ok=1
  for thm in correctness full_output Witness.nonvacuous Witness.returns; do
    if ! jv "$out" --proof "$snap/PrintProofs/${isa^}/$n.lean" --proof-root "$snap" \
        --theorem "Proof.$thm" \
        ${extra[@]+"${extra[@]}"} >> "$out/verify.log" 2>&1; then
      ok=0; echo "  $target: Proof.$thm FAILED"
    fi
  done
  t=$(echo "$(date +%s.%N) - $start" | bc)
  if [ $ok = 1 ]; then
    printf '%-18s ok  %6.1fs\n' "$target" "$t" | tee "$lines/${isa}_$n"
  else
    printf '%-18s FAILED (see %s/verify.log)\n' "$target" "$out" | tee "$lines/${isa}_$n"
    tail -30 "$out/verify.log"
    broken+=("print:$target")
  fi
  incr_end "print:$target" print "$((1 - ok))" "$t" "${ispec[@]}"
  return 0
}
for target in "${names[@]}"; do
  par_run 'verify_one "$target"'
done
par_wait
for target in "${names[@]}"; do
  f="$lines/${target%%/*}_${target#*/}"
  if [ -f "$f" ]; then cat "$f" >> "$summary"; else echo "$target  FAILED (no result)" >> "$summary"; broken+=("print:$target"); fi
done
rm -rf "$lines"
cat "$summary"
[ ${#broken[@]} -eq 0 ] && ! grep -q FAILED "$summary"
