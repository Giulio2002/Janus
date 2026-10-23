#!/usr/bin/env bash
# CI guard: no `sorry`, `native_decide`, `bv_decide` or `admit` in the Lean sources of the
# framework and of the proofs. `janus verify` rejects them anyway (axiom audit); this catches
# them early, including in files no verification imports. The only exempt file is the
# deliberately rejected fixture examples/proofs/Sorry.lean (if present; the CLI fixtures now
# live in cmd/janus/testdata/, which is not scanned). Comments are scanned too.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
dirs=(Janus examples/proofs)
for d in targets/*/proofs; do [ -d "$d" ] && dirs+=("$d"); done
existing=()
for d in "${dirs[@]}"; do [ -d "$d" ] && existing+=("$d"); done
[ "${#existing[@]}" -eq 0 ] && { echo "axiom guard: nothing to scan"; exit 0; }
hits="$(grep -rnwE --include='*.lean' 'sorry|native_decide|bv_decide|admit' "${existing[@]}" |
  grep -v '^examples/proofs/Sorry\.lean:' || true)"
if [ -n "$hits" ]; then
  echo "axiom guard: forbidden tactic/term found:" >&2
  echo "$hits" >&2
  exit 1
fi
echo "axiom guard: no sorry/native_decide/bv_decide/admit in ${existing[*]}"
