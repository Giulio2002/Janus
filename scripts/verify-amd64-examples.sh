#!/usr/bin/env bash
# Check and verify every amd64 example proof (examples/proofs-amd64/<Function>/Proof.lean)
# against its extraction in artifacts/amd64/<Function>, which scripts/build-examples-amd64.sh
# (run first) builds and extracts.
# Also verifies the extra `Proof.panics` theorems of Div and Get. Exits non-zero on any failure.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$PATH:/usr/local/go/bin"
cd "$root"
[ -x bin/janus ] || go build -o bin/janus ./cmd/janus
bash scripts/build-examples-amd64.sh
fail=0
verify() {
  local f=$1 thm=$2
  if out=$(bin/janus verify "artifacts/amd64/$f" --proof "examples/proofs-amd64/$f/Proof.lean" --theorem "$thm" 2>&1); then
    printf '%-12s %-18s %s\n' "$f" "$thm" "$(grep 'Axioms:' <<<"$out" | sed 's/^ *//')"
  else
    printf '%-12s %-18s FAILED\n%s\n' "$f" "$thm" "$out"; fail=1
  fi
}
for d in examples/proofs-amd64/*/; do
  f=$(basename "$d")
  verify "$f" Proof.correctness
  if grep -q '^theorem panics' "$d/Proof.lean"; then verify "$f" Proof.panics; fi
done
exit $fail
