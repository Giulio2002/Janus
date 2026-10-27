#!/usr/bin/env bash
# Build the kernel examples (scripts/build-examples-sys.sh), extract every proved function on both
# ISAs into artifacts/sys/<isa>/<Name>/, and verify examples/proofs-sys/<isa>/<Name>.lean against it
# with `janus verify` (kernel check, axiom audit, leanchecker replay). WP-C: the kernel is the
# environment of Janus.Kernel.EnsuresK (Janus/Contracts/Syscall.lean, SyscallAmd64.lean).
#
#   WriteOut     syscall.Write(1, p): the fd-1 output trace gains the bytes written (EnsuresK,
#                with the scheduler hooks and convT64 as runtime contracts)
#   NowNano      time.Now().UnixNano(): the wall-clock reading of the vDSO clock contract
#   Pid          syscall.Getpid(): a raw system call
#   MustNonNeg   a path that ends in a breakpoint trap (Kernel.Traps) and one that returns
#   AESField, SVEField  (arm64 only, N5) fields of ID_AA64ISAR0_EL1 / ID_AA64PFR0_EL1: the
#                feature-ID register read is an arbitrary 64-bit value (Kernel.Site.mrs .idreg)
#
# Usage: scripts/verify-sys-examples.sh [isa/Name ...]   (default: all, e.g. arm64/WriteOut)
# Writes artifacts/sys/<isa>/<Name>/verified.json and a summary to artifacts/verify-sys-examples.txt.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH

all=(WriteOut NowNano Pid MustNonNeg)
names=("$@")
if [ ${#names[@]} -eq 0 ]; then
  for isa in arm64 amd64; do
    for n in "${all[@]}"; do names+=("$isa/$n"); done
  done
  names+=(arm64/AESField arm64/SVEField)
fi

# the extraction arguments of an example: the runtime contracts it leaves out
sys_args() {
  case "$1" in
    WriteOut) printf '%s\n' --contract runtime.entersyscall --contract runtime.exitsyscall \
      --contract runtime.convT64 ;;
  esac
}

if [ "${JANUS_EXAMPLES_PREBUILT:-}" != 1 ]; then
  go build -o bin/janus ./cmd/janus
  scripts/build-examples-sys.sh >/dev/null
fi
extra=()
[ -n "${JANUS_ROOT:-}" ] && extra=(--janus-root "$JANUS_ROOT")

summary="${JANUS_EXAMPLES_SUMMARY:-$root/artifacts/verify-sys-examples.txt}"
: > "$summary"
fail=0
for target in "${names[@]}"; do
  isa="${target%%/*}"; n="${target#*/}"
  out="artifacts/sys/$isa/$n"
  mapfile -t args < <(sys_args "$n")
  mkdir -p "$out"
  b="artifacts/examples-sys-$isa"; case "$n" in AESField|SVEField) b="artifacts/examples-sys-idreg-$isa" ;; esac
  bin/janus extract "$b" "example.com/sys.$n" "$out" ${args[@]+"${args[@]}"} >/dev/null 2>&1
  : > "$out/verify.log"
  start=$(date +%s.%N)
  ok=1
  for thm in $(grep -oE '^theorem (correctness|traps|full_write)' "examples/proofs-sys/$isa/$n.lean" | awk '{print $2}'); do
    if ! bin/janus verify "$out" --proof "examples/proofs-sys/$isa/$n.lean" --theorem "Proof.$thm" \
        ${extra[@]+"${extra[@]}"} >> "$out/verify.log" 2>&1; then
      ok=0; echo "  $isa/$n: Proof.$thm FAILED"
    fi
  done
  # the non-vacuity witnesses (Proof.Witness.nonvacuous, Proof.Witness.returns) where there are some
  if grep -q '^namespace Witness' "examples/proofs-sys/$isa/$n.lean"; then
    for thm in Proof.Witness.nonvacuous Proof.Witness.returns; do
      if ! bin/janus verify "$out" --proof "examples/proofs-sys/$isa/$n.lean" --theorem "$thm" \
          ${extra[@]+"${extra[@]}"} >> "$out/verify.log" 2>&1; then
        ok=0; echo "  $isa/$n: $thm FAILED"
      fi
    done
  fi
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
