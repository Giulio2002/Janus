#!/usr/bin/env bash
# audit/round9/model/grow_check.sh GROWFILE: compare the capacities a real binary chose
# ("newLen oldCap newCap" lines from `probe9 grow K`) with the contract's growCap8.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
f="$(mktemp --suffix=.lean)"; trap 'rm -f "$f"' EXIT
{ echo 'import Janus'
  echo 'open Janus.Contracts'
  printf 'def obs : List (Nat × Nat × Nat) := ['
  awk 'NR>1{printf ", "} {printf "(%s, %s, %s)", $1, $2, $3}' "$1"
  echo ']'
  echo '#eval let bad := obs.filter (fun (l, c, n) => growCap8 l c != n); if bad.isEmpty then s!"GROW OK {obs.length} growths match growCap8" else s!"GROW MISMATCH {bad}"'
} > "$f"
cd "$root" && lake env lean "$f"
