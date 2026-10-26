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
#   amd64 only, C compiled by clang -O3 -march=x86-64-v3
#   (AVX2-vectorised, artifacts/examples-cgo-avx-amd64): CDot32 GoDot32
#   amd64 only (WP-J): a CET jump table (CSwitch), x87 long double (CLdMul), and
#   Go MulLD -> c_ldmul -> ld_mul end to end (GoLdMul)
#   The C environment (docs/FFI.md sections 2-4; binary artifacts/examples-cenv-<isa>):
#     EBump (a writable global through the GOT; amd64: the --no-relax build), ETLS (a __thread
#     variable, general dynamic as relaxed by the linker), ETLSIE (initial exec), EAtomic (an atomic
#     RMW: LSE / LOCK XADD), ELibc (strlen, malloc, __memcpy_chk, memcpy, free through the PLT),
#     ESetJmp (setjmp/longjmp), EArgMin (a call through a function pointer, CFuncIs), ECallGo
#     (C -> an //export Go function, end to end under CgoCallback), EAlloca (alloca, stack probes),
#     ECallBox (a callback whose Go code calls a Go function and allocates, newobject as a
#     contract), ECallLarge (a callback with a 4848-byte Go frame, an 8192-byte goroutine stack),
#     EEnv (environ through a GOT slot with a dynamic relocation, GotBound); EAtomic covers both
#     paths of the arm64 outline-atomics helper (LSE, and LL/SC under the progress hypothesis)
#   A proof with `namespace Witness` also has `Proof.Witness.nonvacuous` verified (its hypotheses
#   hold together).
#
# Every name maps to a symbol (sym) and, for the C environment, a binary (bin).
# Usage: scripts/verify-cgo-examples.sh [isa/Name ...]   (default: all, e.g. arm64/GoAdd)
# Writes artifacts/cgo/<isa>/<Name>/verified.json and a summary to artifacts/verify-cgo-examples.txt.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH

declare -A sym=(
  [CAdd]=c_add [CSum]=c_sum [CStore]=c_store [CCount]=c_count [GoCount]=example.com/cgo/neon.Count
  [GoAdd]=example.com/cgo.Add [GoSum]=example.com/cgo.Sum
  [CSwitch]=c_switch [CLdMul]=ld_mul [GoLdMul]=example.com/cgo.MulLD
  [KStack10]=k_stack10 [KFP]=k_fp [KPMix]=k_pmix [KBig]=k_big [KVSum]=k_vsum
  [GoStack10]=example.com/cgo/cabi.Stack10 [GoFP]=example.com/cgo/cabi.FP
  [GoPMix]=example.com/cgo/cabi.PMix [GoBig]=example.com/cgo/cabi.Big
  [GoVSum8]=example.com/cgo/cabi.VSum8
  [CSum32]=c_sum32 [GoSum32]=example.com/cgo/vec.Sum32
  [CDot32]=c_dot32 [GoDot32]=example.com/cgo/avx.Dot32
  [EBump]=e_bump [ETLS]=e_tls_add [ETLSIE]=e_tls_ie_add [EAtomic]=e_atomic_inc [ELibc]=e_libc
  [ESetJmp]=e_setjmp [EArgMin]=e_argmin_i64 [ECallGo]=e_callgo [EAlloca]=e_alloca
  [ECallBox]=e_callbox [ECallLarge]=e_calllarge [EEnv]=e_env_at
)
# binaries other than artifacts/examples-cgo-<isa> (key isa/Name, or Name for both ISAs)
declare -A bin=(
  [EBump]=examples-cenv [amd64/EBump]=examples-cenv-norelax
  [ETLS]=examples-cenv [ETLSIE]=examples-cenv [EAtomic]=examples-cenv [ELibc]=examples-cenv
  [ESetJmp]=examples-cenv [EArgMin]=examples-cenv [ECallGo]=examples-cenv [EAlloca]=examples-cenv
  [ECallBox]=examples-cenv [ECallLarge]=examples-cenv [EEnv]=examples-cenv
  [CSum32]=examples-cgo-clang [GoSum32]=examples-cgo-clang
  [CDot32]=examples-cgo-avx [GoDot32]=examples-cgo-avx
)
# extra extraction options (key isa/Name or Name): runtime functions taken as contracts
declare -A xargs=([ECallBox]="--contract runtime.newobject")
all=(CAdd CSum CStore GoAdd GoSum KStack10 KFP KPMix KBig KVSum GoStack10 GoFP GoPMix GoBig GoVSum8
  EBump ETLS ETLSIE EAtomic ELibc ESetJmp EArgMin ECallGo EAlloca ECallBox ECallLarge EEnv)
names=("$@")
if [ ${#names[@]} -eq 0 ]; then
  for isa in arm64 amd64; do
    for n in "${all[@]}"; do names+=("$isa/$n"); done
    [ "$isa" = arm64 ] && names+=("$isa/CCount" "$isa/GoCount")
  done
  names+=(amd64/CSum32 amd64/GoSum32 amd64/CDot32 amd64/GoDot32)
  for n in CSwitch CLdMul GoLdMul; do names+=("amd64/$n"); done
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
  b="${bin[$isa/$n]:-${bin[$n]:-examples-cgo}}"
  bin/janus extract "artifacts/$b-$isa" "${sym[$n]}" "$out" --contract runtime.convT64 \
    --contract runtime.convT32 --contract runtime.convTnoptr ${xargs[$isa/$n]:-${xargs[$n]:-}} >/dev/null 2>&1
  start=$(date +%s.%N)
  if bin/janus verify "$out" --proof "examples/proofs-cgo/$isa/$n.lean" --janus-root . > "$out/verify.log" 2>&1; then
    t=$(echo "$(date +%s.%N) - $start" | bc)
    printf '%-12s ok  %6.1fs\n' "$isa/$n" "$t" | tee -a "$summary"
    if grep -q '^namespace Witness' "examples/proofs-cgo/$isa/$n.lean"; then
      if bin/janus verify "$out" --proof "examples/proofs-cgo/$isa/$n.lean" --theorem Proof.Witness.nonvacuous \
          --janus-root . > "$out/verify-witness.log" 2>&1; then
        printf '%-12s ok  (Proof.Witness.nonvacuous)\n' "$isa/$n" | tee -a "$summary"
      else
        printf '%-12s FAILED Proof.Witness.nonvacuous (see %s/verify-witness.log)\n' "$isa/$n" "$out" | tee -a "$summary"
        tail -30 "$out/verify-witness.log"
        fail=1
      fi
    fi
  else
    printf '%-12s FAILED (see %s/verify.log)\n' "$isa/$n" "$out" | tee -a "$summary"
    tail -30 "$out/verify.log"
    fail=1
  fi
done
cat "$summary"
exit $fail
