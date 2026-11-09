#!/usr/bin/env bash
# Compile Extracted + Proof for the given amd64 examples into audit/round2/amd64/work/<E>/, then
# check audit/round2/amd64/controls/<E>_witness.lean against them.
# Needs artifacts/amd64 (scripts/build-examples-amd64.sh) and `lake build Janus`.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"; cd "$root"
for e in "${@:-AtomicAdd AtomicMax CopyWords CopyBlock ClearWords}"; do
for E in $e; do
  W=audit/round2/amd64/work/$E; mkdir -p $W
  base=$(lake env printenv LEAN_PATH)
  export LEAN_PATH="$root/$W:$base"
  [ -f $W/Extracted.olean ] || lake env env LEAN_PATH="$LEAN_PATH" lean -o $W/Extracted.olean artifacts/amd64/$E/Extracted.lean
  [ -f $W/Proof.olean ] || { echo "compiling $E proof..."; lake env env LEAN_PATH="$LEAN_PATH" lean -o $W/Proof.olean examples/proofs-amd64/$E/Proof.lean; }
  echo "== $E witness"
  lake env env LEAN_PATH="$LEAN_PATH" lean audit/round2/amd64/controls/${E}_witness.lean && echo "$E witness OK"
done; done
