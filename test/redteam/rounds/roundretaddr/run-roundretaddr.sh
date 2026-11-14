#!/usr/bin/env bash
# Red-team round retaddr (v0.4.0): `Ensures` evaluates its precondition BEFORE the return address is installed
# (`State.setRet`), so a precondition cannot restrict the caller's return address. The Lean-level claims (the pinned
# statement covers every admissible return address; the pin is not invariant under `setRet`; what `janus_pre_setRet`
# discharges and refuses) are theorems in test/lean/JanusTests/RetAddr.lean (built by `lake build JanusTests.RetAddr`; a
# regression there fails the build). This script runs the auditor-level rows: the probe forms of v0.3.3
# (/srv/janus-ops/v033/probe/RspBypass64.lean: c1-c8, d0; LrPin.lean: e1, e2) and their siblings. Before v0.4.0 the amd64
# probes were seven accepted bypasses of a syntactic rule and the arm64 ones had no rule at all. Now EVERY row must be
# Verified (audit-only): the pinned word is the caller's old word, which the call overwrites. Exits 1 if a row differs.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=test/redteam/rounds/roundretaddr
J="${JANUS_AUDIT_BIN:-$root/$R/bin/janus}"
if [ -z "${JANUS_AUDIT_BIN:-}" ]; then mkdir -p "$(dirname "$J")"; go build -o "$J" ./cmd/janus || exit 1; fi
if [ "${JANUS_AUDIT_PREBUILT:-}" != 1 ]; then
  lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
  [ -f artifacts/examples-amd64 ] || bash scripts/build/build-examples-amd64.sh >/dev/null 2>&1
  [ -f artifacts/examples-arm64 ] || bash scripts/build/build-examples.sh >/dev/null 2>&1
fi
W=$R/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-roundretaddr.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
. scripts/verify/example-contracts.sh
mapfile -t tg < <(scripts/verify/example-targets.sh ErrWrap)
"$J" extract artifacts/examples-amd64 "$(example_symbol ErrWrap)" "$W/ErrWrap64" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
"$J" extract artifacts/examples-arm64 "$(example_symbol Add)" "$W/Add64" >/dev/null 2>&1 || exit 1
broken=()
P=Proof
run() { # PROOF ART THEOREM...
  local pf=$1 art=$2; shift 2; local a=()
  for t in "$@"; do a+=(--theorem "$P.$t"); done
  "$J" verify --audit-only --janus-root "$root" --proof "$pf" "$art" "${a[@]}" 2>&1 | sed -E 's/^Audit-only: /Verified: /; s/^(=== .*): audit-only \(NOT verified\) ===\$/\1: verified ===/'
}
all_amd="$(run $R/attacks/RetAddrPin64.lean "$W/ErrWrap64" c1 c2 c3 c4 c5 c6 c7 c8 d0 d1 d2 d3)"
printf '%s\n' "$all_amd" > "$W/RetAddrPin64.txt"
all_arm="$(run $R/attacks/RetAddrPinA64.lean "$W/Add64" e1 e2 e3 e4)"
printf '%s\n' "$all_arm" > "$W/RetAddrPinA64.txt"
row() { # ALL NAME : every row of this round is Verified (the pinned word is the caller's old word)
  local all=$1 name=$2 out verdict status=""
  out="$(awk -v n="=== $P.$name:" 'index($0,n)==1{p=1;print;next} /^=== /{p=0} p' <<<"$all")"
  verdict="$(grep -m1 -E '^=== ' <<<"$out" | cut -c1-100)"
  [ -n "$verdict" ] || { verdict="(no block)"; status=BROKEN; }
  case $verdict in *verified*) ;; *) status=BROKEN ;; esac
  grep -q "^Verified: $P.$name" <<<"$out" || status=BROKEN   # the audit-only run passed (not a FAILED block)
  printf '  %-6s %-8s %s%s\n' "$name" Verified "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name"); return 0
}
echo "== amd64: RetAddrPin64.lean (the RspBypass64 probes, bounds, the instruction-count forms)"
for n in c1 c2 c3 c4 c5 c6 c7 c8 d0 d1 d2 d3; do row "$all_amd" $n; done
echo "== arm64: RetAddrPinA64.lean (the LrPin probes)"
for n in e1 e2 e3 e4; do row "$all_arm" $n; done
echo
if [ ${#broken[@]} -gt 0 ]; then echo "round retaddr: BROKEN rows: ${broken[*]}"; exit 1; fi
echo "round retaddr: all rows as expected"
