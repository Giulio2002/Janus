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
# Usage: scripts/verify-sys-examples.sh [-j N] [--list] [isa/Name ...]   (default: all, e.g. arm64/WriteOut)
#   -j N     rows at once (default: $JANUS_JOBS, else see scripts/lib/parallel.sh); the theorems of one
#            row run up to two at once (scripts/lib/theorems.sh).
#   --list   print the default rows, one per line, and exit (scripts/verify-all-examples.sh queues them).
# Writes artifacts/sys/<isa>/<Name>/verified.json and a summary to artifacts/verify-sys-examples.txt.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
. "$root/scripts/lib/itemtimeout.sh"
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"

all=(WriteOut NowNano Pid MustNonNeg)
default_rows() {
  local isa n
  for isa in arm64 amd64; do
    for n in "${all[@]}"; do echo "$isa/$n"; done
  done
  echo arm64/AESField; echo arm64/SVEField
}
if [ "${1:-}" = --list ]; then default_rows; exit 0; fi
memguard_self "$@"
par_init "$@"
set -- ${PAR_ARGS[@]+"${PAR_ARGS[@]}"}
names=("$@")
[ ${#names[@]} -gt 0 ] || mapfile -t names < <(default_rows)

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
. scripts/lib/theorems.sh

summary="${JANUS_EXAMPLES_SUMMARY:-$root/artifacts/verify-sys-examples.txt}"
: > "$summary"
lines="$(mktemp -d)"
broken=()

# verify_one ISA/NAME: extract the row, verify its theorems (the main ones, then the non-vacuity
# witnesses where there are some), up to two at once; prints its result line (kept in $lines).
verify_one() {
  local target=$1 isa n out b start t st i
  isa="${target%%/*}"; n="${target#*/}"
  out="artifacts/sys/$isa/$n"
  local -a args=() thms=()
  mapfile -t args < <(sys_args "$n")
  mkdir -p "$out"
  b="artifacts/examples-sys-$isa"; case "$n" in AESField|SVEField) b="artifacts/examples-sys-idreg-$isa" ;; esac
  bin/janus extract "$b" "example.com/sys.$n" "$out" ${args[@]+"${args[@]}"} >/dev/null 2>&1
  local thm
  for thm in $(grep -oE '^theorem (correctness|traps|full_write)' "examples/proofs-sys/$isa/$n.lean" | awk '{print $2}'); do thms+=("Proof.$thm"); done
  # the non-vacuity witnesses (Proof.Witness.nonvacuous, Proof.Witness.returns) where there are some
  if grep -q '^namespace Witness' "examples/proofs-sys/$isa/$n.lean"; then thms+=(Proof.Witness.nonvacuous Proof.Witness.returns); fi
  if [ ${#thms[@]} -eq 0 ]; then
    printf '%-18s FAILED (no theorem found in examples/proofs-sys/%s/%s.lean)\n' "$target" "$isa" "$n" | tee "$lines/${isa}_$n"
    broken+=("sys:$target"); return 0
  fi
  st="$(mktemp -d)"
  start=$(date +%s.%N)
  verify_theorems "$out" "examples/proofs-sys/$isa/$n.lean" "$st" "${thms[@]}" -- ${extra[@]+"${extra[@]}"} || true  # failures are in $st
  t=$(echo "$(date +%s.%N) - $start" | bc)
  cat "$st"/*.log > "$out/verify.log" 2>/dev/null || true
  local ok=1
  for ((i = 0; i < ${#thms[@]}; i++)); do
    if [ "$(cat "$st/$i.rc" 2>/dev/null)" != 0 ]; then ok=0; echo "  $target: ${thms[$i]} FAILED"; fi
  done
  if [ $ok = 1 ]; then
    printf '%-18s ok  %6.1fs\n' "$target" "$t" | tee "$lines/${isa}_$n"
  else
    printf '%-18s FAILED (see %s/verify.log)\n' "$target" "$out" | tee "$lines/${isa}_$n"
    tail -30 "$out/verify.log"
    broken+=("sys:$target")
  fi
  rm -rf "$st"
  return 0
}

for target in "${names[@]}"; do
  par_run 'verify_one "$target"'
done
par_wait
for target in "${names[@]}"; do
  f="$lines/${target%%/*}_${target#*/}"
  if [ -f "$f" ]; then cat "$f" >> "$summary"; else echo "$target  FAILED (no result)" >> "$summary"; broken+=("sys:$target"); fi
done
rm -rf "$lines"
echo
cat "$summary"
[ ${#broken[@]} -eq 0 ] && ! grep -q FAILED "$summary"
