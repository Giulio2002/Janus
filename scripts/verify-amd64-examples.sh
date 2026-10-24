#!/usr/bin/env bash
# Check and verify every amd64 example proof (examples/proofs-amd64/<Function>/Proof.lean)
# against its extraction in artifacts/amd64/<Function>, which scripts/build-examples-amd64.sh
# (run first) builds and extracts.
# Also verifies the extra `Proof.panics` theorems of Div and Get. Exits non-zero on any failure.
# Usage: scripts/verify-amd64-examples.sh [-j N] [Function ...]   (default: every function)
#   -j N   verify up to N functions at once (default: $JANUS_JOBS, else the number of cores
#          capped by memory, see scripts/lib/parallel.sh); -j 1 verifies them one by one. The
#          theorems of one function run one after the other (they share its verified.json).
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
  [ -x bin/janus ] || go build -o bin/janus ./cmd/janus
  bash scripts/build-examples-amd64.sh
fi
broken=()
verify() {
  local f=$1 thm=$2 out
  if out=$(bin/janus verify "artifacts/amd64/$f" --proof "examples/proofs-amd64/$f/Proof.lean" --theorem "$thm" 2>&1); then
    printf '%-12s %-18s %s\n' "$f" "$thm" "$(grep 'Axioms:' <<<"$out" | sed 's/^ *//')"
  else
    printf '%-12s %-18s FAILED\n%s\n' "$f" "$thm" "$out"; broken+=("$f.$thm")
  fi
}
# verify_function F: every theorem of examples/proofs-amd64/F, in order.
verify_function() {
  local f=$1
  verify "$f" Proof.correctness
  if grep -q '^theorem panics' "examples/proofs-amd64/$f/Proof.lean"; then verify "$f" Proof.panics; fi
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
