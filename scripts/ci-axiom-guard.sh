#!/usr/bin/env bash
# CI guard: no `sorry`, `native_decide`, `bv_decide` or `admit` in the Lean sources of the
# framework, its tests and the example proofs (examples/proofs, examples/asm/proofs,
# examples/proofs-cgo, and examples/proofs-amd64 when it
# exists). `janus verify` rejects them anyway (axiom audit); this catches them early,
# including in files no verification imports. The only exempt file is the deliberately
# rejected fixture examples/proofs/Sorry.lean (if present; the CLI fixtures now live in
# cmd/janus/testdata/, which is not scanned) and the trusted auditor Janus/Tools/Audit.lean,
# which names these terms in order to detect and reject them. Comments are scanned too.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
dirs=(Janus JanusTests examples/proofs examples/proofs-amd64 examples/asm/proofs examples/proofs-cgo)
existing=()
for d in "${dirs[@]}"; do [ -d "$d" ] && existing+=("$d"); done
[ "${#existing[@]}" -eq 0 ] && { echo "axiom guard: nothing to scan"; exit 0; }
hits="$(grep -rnwE --include='*.lean' 'sorry|native_decide|bv_decide|admit' "${existing[@]}" |
  grep -v -e '^examples/proofs/Sorry\.lean:' -e '^Janus/Tools/Audit\.lean:' || true)"
if [ -n "$hits" ]; then
  echo "axiom guard: forbidden tactic/term found:" >&2
  echo "$hits" >&2
  exit 1
fi
echo "axiom guard: no sorry/native_decide/bv_decide/admit in ${existing[*]}"
