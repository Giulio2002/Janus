#!/usr/bin/env bash
# Check and verify every amd64 example proof (examples/proofs-amd64/<Function>/Proof.lean)
# against its extraction in artifacts/amd64/<Function>, which scripts/build-examples-amd64.sh
# (run first) builds and extracts.
# Also verifies the extra `Proof.panics` theorems of Div and Get. Exits non-zero on any failure.
# Usage: scripts/verify-amd64-examples.sh [-j N] [Function ...]   (default: every function)
#   -j N   verify up to N functions at once (default: $JANUS_JOBS, else the number of cores
#          capped by memory, see scripts/lib/parallel.sh); -j 1 verifies them one by one. The
#          theorems of one function run up to two at once (scripts/lib/theorems.sh).
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$PATH:/usr/local/go/bin"
cd "$root"
# shellcheck source=lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
par_init "$@"
set -- ${PAR_ARGS[@]+"${PAR_ARGS[@]}"}
# JANUS_EXAMPLES_PREBUILT=1 (scripts/verify-all-examples.sh): already built and extracted.
if [ "${JANUS_EXAMPLES_PREBUILT:-}" != 1 ]; then
  [ -x bin/janus ] || CGO_ENABLED=0 go build -o bin/janus ./cmd/janus
  bash scripts/build-examples-amd64.sh
fi
broken=()
. scripts/lib/theorems.sh
. scripts/lib/incr.sh
# verify_function F: every theorem of examples/proofs-amd64/F (correctness, Div's and Get's
# `panics`, the non-vacuity witnesses: the hypotheses hold together and the conclusion is
# reached), up to two at once (scripts/lib/theorems.sh); printed in order.
verify_function() {
  local f=$1 st i
  local -a thms=(Proof.correctness)
  local thm
  for thm in panics exact outOfRange faults forAllValues; do
    if grep -q "^theorem $thm" "examples/proofs-amd64/$f/Proof.lean"; then thms+=("Proof.$thm"); fi
  done
  if grep -q '^namespace Witness' "examples/proofs-amd64/$f/Proof.lean"; then thms+=(Proof.Witness.nonvacuous Proof.Witness.returns); fi
  # corollaries stated as their own theorems (e.g. EncryptBlock's AES-128 and FIPS-197 vector)
  local c
  for c in $(grep -oE '^theorem corollary[A-Za-z0-9_]*' "examples/proofs-amd64/$f/Proof.lean" | awk '{print $2}'); do
    thms+=("Proof.$c")
  done
  # the incremental gate (scripts/lib/incr.sh): skipped only on the record of a PASS with identical inputs
  local -a ispec=($(incr_fw_embedded) --proof "examples/proofs-amd64/$f/Proof.lean" --art "artifacts/amd64/$f")
  local thm_a item_rc=0 t0
  for thm_a in "${thms[@]}"; do ispec+=(--arg "thm:$thm_a"); done
  if incr_begin "amd64:$f" amd64 "${ispec[@]}"; then
    printf '%s\n' "$INCR_MSG"; return 0
  fi
  t0=$(date +%s.%N)
  st="$(mktemp -d)"
  verify_theorems "artifacts/amd64/$f" "examples/proofs-amd64/$f/Proof.lean" "$st" "${thms[@]}" || true  # failures are in $st
  for ((i = 0; i < ${#thms[@]}; i++)); do
    if [ "$(cat "$st/$i.rc" 2>/dev/null)" = 0 ]; then
      printf '%-12s %-18s %s\n' "$f" "${thms[$i]}" "$(grep 'Axioms:' "$st/$i.log" | sed 's/^ *//')"
    else
      printf '%-12s %-18s FAILED\n%s\n' "$f" "${thms[$i]}" "$(cat "$st/$i.log" 2>/dev/null)"; broken+=("$f.${thms[$i]}"); item_rc=1
    fi
  done
  rm -rf "$st"
  incr_end "amd64:$f" amd64 "$item_rc" "$(echo "$(date +%s.%N) - $t0" | bc)" "${ispec[@]}"
  return 0
}
funcs=("$@")
if [ ${#funcs[@]} -eq 0 ]; then
  for d in examples/proofs-amd64/*/; do funcs+=("$(basename "$d")"); done
fi
for f in "${funcs[@]}"; do
  par_run 'verify_function "$f"'
done
par_wait
[ ${#broken[@]} -eq 0 ]
