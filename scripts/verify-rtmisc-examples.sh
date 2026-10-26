#!/usr/bin/env bash
# Build the remaining-runtime examples (scripts/build-examples-rtmisc.sh: examples/rtmisc, Go
# 1.26.0 pinned there), extract every proved function on both ISAs into
# artifacts/rtmisc/<isa>/<Name>/, and verify examples/rtmisc/proofs/<isa>/<Name>.lean against it
# with `janus verify` (kernel check, axiom audit, leanchecker replay), and its non-vacuity
# witnesses (Proof.Witness.nonvacuous, Proof.Witness.returns) where it has them.
# docs/RUNTIME-CONTRACTS.md ("Remaining runtime") describes the examples.
#
# Usage: scripts/verify-rtmisc-examples.sh [-j N] [isa/Name ...]   (default: all, e.g. amd64/Pop)
# Writes artifacts/rtmisc/<isa>/<Name>/verified.json and a summary to
# artifacts/verify-rtmisc-examples.txt (unless JANUS_EXAMPLES_SUMMARY names another file).
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

# Name -> symbol, binary suffix, extraction arguments.
sym() {
  case "$1" in
    Clamp) echo example.com/rtmisc/cover.Clamp ;;
    Widen) echo example.com/rtmisc/soft.Widen ;;
    CheckWord) echo example.com/rtmisc/checkptr.Word ;;
    NewPairSC) echo example.com/rtmisc/sc.NewPair ;;
    SoftAdd|SoftMul|SoftDiv) echo "example.com/rtmisc/softf.${1#Soft}" ;;
    KeepAlive) echo runtime.KeepAlive ;;
    *) echo "example.com/rtmisc.$1" ;;
  esac
}
bin() {
  case "$2" in
    NewPairSC) echo "artifacts/examples-rtmisc-sc-$1" ;;
    SoftAdd|SoftMul|SoftDiv|KeepAlive) echo "artifacts/examples-rtmisc-softf-$1" ;;
    *) echo "artifacts/examples-rtmisc-$1" ;;
  esac
}
args() {
  case "$1" in
    CheckWord) printf '%s\n' --contract runtime.checkptrAlignment ;;
    NewPairSC) printf '%s\n' --contract 'runtime.mallocgcSmallNoScanSC*' ;;
    SoftAdd) printf '%s\n' --contract runtime.fadd64 ;;
    SoftMul) printf '%s\n' --contract runtime.fmul64 ;;
    SoftDiv) printf '%s\n' --contract runtime.fdiv64 ;;
    KeepAlive) printf '%s\n' --contract 'runtime.print*' ;;
  esac
}
names=("$@")
if [ ${#names[@]} -eq 0 ]; then
  for f in examples/rtmisc/proofs/*/*.lean; do names+=("$(basename "$(dirname "$f")")/$(basename "$f" .lean)"); done
fi

# JANUS_EXAMPLES_PREBUILT=1 (scripts/verify-all-examples.sh): bin/janus and the binaries exist.
if [ "${JANUS_EXAMPLES_PREBUILT:-}" != 1 ]; then
  go build -o bin/janus ./cmd/janus
  scripts/build-examples-rtmisc.sh >/dev/null
fi

summary="${JANUS_EXAMPLES_SUMMARY:-$root/artifacts/verify-rtmisc-examples.txt}"
: > "$summary"
lines="$(mktemp -d)"
broken=()

verify_one() {
  local target=$1 isa n out start t thm
  isa="${target%%/*}"; n="${target#*/}"
  out="artifacts/rtmisc/$isa/$n"
  mapfile -t xargs < <(args "$n")
  bin/janus extract "$(bin "$isa" "$n")" "$(sym "$n")" "$out" ${xargs[@]+"${xargs[@]}"} >/dev/null 2>&1
  start=$(date +%s.%N)
  if bin/janus verify "$out" --proof "examples/rtmisc/proofs/$isa/$n.lean" --janus-root . > "$out/verify.log" 2>&1; then
    t=$(echo "$(date +%s.%N) - $start" | bc)
    printf '%-18s ok  %6.1fs\n' "$isa/$n" "$t" | tee "$lines/${isa}_$n"
    if grep -q '^namespace Witness' "examples/rtmisc/proofs/$isa/$n.lean"; then
      for thm in Proof.Witness.nonvacuous Proof.Witness.returns; do
        if bin/janus verify "$out" --proof "examples/rtmisc/proofs/$isa/$n.lean" --theorem "$thm" --janus-root . >> "$out/verify.log" 2>&1; then
          printf '%-18s ok  (%s)\n' "$isa/$n" "$thm" | tee -a "$lines/${isa}_$n"
        else
          printf '%-18s FAILED %s (see %s/verify.log)\n' "$isa/$n" "$thm" "$out" | tee -a "$lines/${isa}_$n"
        fi
      done
    fi
  else
    printf '%-18s FAILED (see %s/verify.log)\n' "$isa/$n" "$out" | tee "$lines/${isa}_$n"
    tail -30 "$out/verify.log"
  fi
}

for target in "${names[@]}"; do
  par_run 'verify_one "$target"'
done
par_wait
for target in "${names[@]}"; do
  f="$lines/${target%%/*}_${target#*/}"
  if [ -f "$f" ]; then cat "$f" >> "$summary"; else echo "$target  FAILED (no result)" >> "$summary"; fi
done
rm -rf "$lines"
echo
cat "$summary"
! grep -q FAILED "$summary"
