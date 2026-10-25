#!/usr/bin/env bash
# Audit rows for agent/maps2 (work package R3): finding R3-C1 (the pre-fix allocating map
# contracts were unsatisfiable) and the SAT row for every map contract.
#   R3C1a  audit/maps/model/Unsat.lean compiles: the pre-fix Assign / MakeSmall contracts (both
#          ISAs) admit no call state under the guard condition every caller's CallerOK gives,
#          kernel-checked, with only the standard axioms.
#   R3C1b  audit/maps/model/UnsatFixed.lean (the same argument against the fixed Map.Assign,
#          which takes H : RtReady) does NOT compile, and fails exactly where H is needed.
#   SAT    audit/round9/sat_check.py: no map contract (Janus/Contracts/Map*.lean) is OPEN or MISSING.
# Writes only under audit/maps/work/ and a mktemp directory (removed at the end).
# Usage: audit/maps/run-maps.sh      (exits 1 if a row fails)
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
lake build Janus >/dev/null || { echo "lake build Janus failed"; exit 1; }
W=audit/maps/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-maps.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
broken=()
check() {
  if [ "$2" = 0 ]; then printf '  %-40s ok       %s\n' "$1" "$3"
  else printf '  %-40s FAILED   %s   <-- BROKEN\n' "$1" "$3"; broken+=("$1"); fi
}

echo "== R3-C1: the pre-fix allocating map contracts were unsatisfiable (kernel-checked)"
o="$(lake env lean audit/maps/model/Unsat.lean 2>&1)"; rc=$?
echo "$o" > "$W/unsat.log"
n="$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" <<<"$o")"
bad="$(grep -E "error|sorryAx|depends on axioms" <<<"$o" | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]")"
[ $rc = 0 ] && [ "$n" = 8 ] && [ -z "$bad" ]
check R3C1a_pre_fix_assign_makesmall_unsat $? "old Assign/MakeSmall (arm64, amd64) admit no call state: $n of 8 theorems with standard axioms only${bad:+ ($bad)}"
o="$(lake env lean audit/maps/model/UnsatFixed.lean 2>&1)"; rc=$?
echo "$o" > "$W/unsatfixed.log"
[ $rc -ne 0 ] && grep -q "Ready H M.priv" <<<"$o" && [ "$(grep -c 'error' <<<"$o")" = 1 ]
check R3C1b_fixed_contract_unsat_attempt $? "the same argument against the fixed Map.Assign fails only where H : RtReady is required"

echo "== SAT: every map contract has a kernel-checked _satisfiable witness"
o="$(python3 -I audit/round9/sat_check.py "$root" 2>&1)"
echo "$o" > "$W/sat.log"
open="$(grep -E 'SAT (OPEN|MISSING) +[A-Za-z0-9]+ +Map[A-Za-z0-9]*\.lean' <<<"$o")"
ok="$(grep -cE 'SAT ok +[A-Za-z0-9]+ +Map[A-Za-z0-9]*\.lean' <<<"$o")"
[ -n "$open" ] && sed 's/^/  /' <<<"$open"
[ -z "$open" ] && [ "$ok" -gt 0 ]
check SAT_map_contract_witnesses $? "$ok map contracts witnessed, $(grep -c . <<<"$open") open or missing"

if [ ${#broken[@]} -gt 0 ]; then echo "BROKEN: ${broken[*]}"; exit 1; fi
echo "all R3 rows ok"
