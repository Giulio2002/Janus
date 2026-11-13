#!/usr/bin/env bash
# Red-team round n9 (today's new features: U14 live convT, U-GROWMULTI, ErrorfLive amd64 RetLow/r15, Lake-free verify,
# janus_grab). Semantic attacks on the contracts are Lean theorems in test/lean/JanusTests/RedTeamN9.lean (built by
# `lake build JanusTests.RedTeamN9`; a regression there fails the build). This script runs the auditor-level rows:
# RetLow smuggled into a consumer statement. Rows: b1-b7 and b9 must be rejected by the auditor with the reason checked; b8 (CallOK64 as-is) and b12 (stack-argument words at RSP+8/+16) are controls and verify; b13-b16 (offset < 8, non-numeral, negative offset, mixed definition) must be rejected. Exits 1 if a row differs.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=test/redteam/rounds/roundn9
J="${JANUS_AUDIT_BIN:-$root/$R/bin/janus}"
if [ -z "${JANUS_AUDIT_BIN:-}" ]; then mkdir -p "$(dirname "$J")"; go build -o "$J" ./cmd/janus || exit 1; fi
if [ "${JANUS_AUDIT_PREBUILT:-}" != 1 ]; then
  lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
  [ -f artifacts/examples-amd64 ] || bash scripts/build/build-examples-amd64.sh >/dev/null 2>&1
fi
W=$R/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-roundn9.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
. scripts/verify/example-contracts.sh
mapfile -t tg < <(scripts/verify/example-targets.sh ErrWrap)
"$J" extract artifacts/examples-amd64 "$(example_symbol ErrWrap)" "$W/ErrWrap64" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
broken=()
P=Proof
all="$("$J" verify --audit-only --janus-root "$root" --proof "$R/attacks/RetLowAlias64.lean" "$W/ErrWrap64" \
  --theorem $P.b1 --theorem $P.b2 --theorem $P.b3 --theorem $P.b4 --theorem $P.b5 --theorem $P.b6 --theorem $P.b7 --theorem $P.b8 --theorem $P.b9 --theorem $P.b10 --theorem $P.b11 --theorem $P.b12 --theorem $P.b13 --theorem $P.b14 --theorem $P.b15 --theorem $P.b16 2>&1 | sed -E 's/^Audit-only: /Verified: /; s/^(=== .*): audit-only \(NOT verified\) ===\$/\1: verified ===/')"
printf '%s\n' "$all" > "$W/RetLowAlias64.txt"
blk() { awk -v n="=== $P.$1:" 'index($0,n)==1{p=1;print;next} /^=== /{p=0} p' <<<"$all"; }
. "$root/test/redteam/lib/blocked.sh"
row() { # NAME blocked pattern
  local name=$1 expect=$2 pat=${3:-} out verdict status=""
  out="$(blk "$name")"; verdict="$(grep -m1 -E '^=== ' <<<"$out" | cut -c1-100)"
  [ -n "$verdict" ] || { verdict="(no block)"; status=BROKEN; }
  case $expect in
    Verified) case $verdict in *verified*) ;; *) status=BROKEN ;; esac ;;
    blocked) case $verdict in *verified*) status=BROKEN ;; esac; grep -qF -- "$pat" <<<"$out" || status=BROKEN ;;
    gap) case $verdict in *verified*) ;; *) status=BROKEN ;; esac ;;
  esac
  # blocked rows: pinned reason, and no Lean elaboration failure (test/redteam/lib/blocked.sh)
  if [ "$expect" = blocked ]; then why="$(blocked_check rounds/roundn9/run-roundn9.sh "$name" "$out")"; [ -n "$why" ] && { status=BROKEN; verdict="$verdict [$why]"; }; fi
  printf '  %-6s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name"); return 0
}
echo "== amd64: RetLowAlias64.lean"
RL='constrains the memory word at the entry `RSP`'
row b1 blocked "$RL"
row b2 blocked "$RL"
row b3 blocked "$RL"
row b4 blocked "$RL"
row b5 blocked "$RL"
row b6 blocked "$RL"
row b7 blocked "$RL"
row b8 Verified
row b9 blocked "$RL"
row b10 blocked "$RL"
row b11 blocked "$RL"
row b12 Verified
row b13 blocked "$RL"
row b14 blocked "$RL"
row b15 blocked "$RL"
row b16 blocked "$RL"
echo
if [ ${#broken[@]} -gt 0 ]; then echo "round n9: BROKEN rows: ${broken[*]}"; exit 1; fi
echo "round n9: all rows as expected"
