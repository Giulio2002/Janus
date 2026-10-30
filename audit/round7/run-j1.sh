#!/usr/bin/env bash
# Round-7 row J1a (docs/AUDIT-ROUND7.md J1): the report discloses a pinned dependency definition's body.
# A consumer verification with --fresh (the cold path, exactly as when it was part of run-round7.sh: the
# framework is built from scratch in a temporary workspace, no replay, trusted or verdict cache), as its own
# lane (r7j) so it overlaps the others. It also asserts that the verdict was computed in this run.
# Writes only under audit/round7/work-j1/.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=../../scripts/lib/tmark.sh
. "$root/scripts/lib/tmark.sh"
J="$root/audit/round7/bin/janus"; mkdir -p "$(dirname "$J")"
if [ -n "${JANUS_AUDIT_BIN:-}" ]; then J="$JANUS_AUDIT_BIN"; else go build -o "$J" ./cmd/janus || exit 1; fi
[ "${JANUS_AUDIT_PREBUILT:-}" = 1 ] || lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
W=audit/round7/work-j1; rm -rf "$W"; mkdir -p "$W"
"$J" extract artifacts/examples-arm64 example.com/basic.Add "$W/Add" >/dev/null || exit 1
broken=()

# row NAME EXPECT [PATTERN...]: verdict of $out. EXPECT "blocked" (must not print Verified; if a
# PATTERN is given the output must contain it) or "Verified" (must print Verified and contain
# every PATTERN).
row() {
  local name=$1 expect=$2 verdict status="" pat
  shift 2
  verdict="$(grep -m1 -E '^(Verified|Invalid|Error)' <<<"$out" | cut -c1-150)"
  [ -n "$verdict" ] || verdict="(no verdict) $(head -1 <<<"$out" | cut -c1-120)"
  case $expect in
    blocked) case $verdict in Verified*) status=BROKEN ;; esac ;;
    Verified) case $verdict in Verified*) ;; *) status=BROKEN ;; esac ;;
  esac
  for pat in "$@"; do grep -qF -- "$pat" <<<"$out" || status=BROKEN; done
  printf '  %-36s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}

tmark "J1 start"
dep="$(audit/round7/dep/setup.sh "$root/$W/dep" "$root")" || { echo "  dependency fixture failed"; broken+=(dep-setup); }
j1t0=$(date +%s)
out="$("$J" verify --fresh "$W/Add" --janus-root "$root" --proof "$dep/R7Proofs/Proofs.lean" --proof-root "$dep" --theorem R7Proofs.misnamed 2>&1)"
row J1a_misnamed_dependency_def Verified "Dependency definitions used by the statement" "MisLib.mul : BitVec (64 : Nat) → BitVec (64 : Nat) → BitVec (64 : Nat) := fun (a b : BitVec (64 : Nat)) => a + b"
# The verdict must have been computed in this run: no "Cached:" line, and the report is not older than
# the start of the verification.
jts="$(sed -n 's/.*"timestamp": *"\([^"]*\)".*/\1/p' "$W/Add/verified.json" 2>/dev/null | head -1)"
jep="$(date -u -d "${jts:-1970-01-01T00:00:00Z}" +%s 2>/dev/null || echo 0)"
if grep -q '^  Cached:' <<<"$out" || grep -q '"cached": *true' "$W/Add/verified.json" 2>/dev/null || [ "$jep" -lt "$j1t0" ]; then
  echo "  J1a: the verdict was not computed in this run (cached or stale report)   <-- BROKEN"; broken+=(J1a-not-fresh-run)
fi
# diagnostic only: when the row is BROKEN keep the janus output (the row line cuts it at 150 characters)
if [ ${#broken[@]} -gt 0 ]; then echo "  ---- janus output of the J1a verification (first 40 lines) ----"; head -40 <<<"$out" | cut -c1-600 | sed 's/^/  | /'; fi
tmark "J1 end"
if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo; echo "All round-7 J1 rows as expected."
