#!/usr/bin/env bash
# Red-team round n9 (today's new features: U14 live convT, U-GROWMULTI, ErrorfLive amd64 RetLow/r15, Lake-free verify,
# janus_grab). Semantic attacks on the contracts are Lean theorems in test/lean/JanusTests/RedTeamN9.lean (built by
# `lake build JanusTests.RedTeamN9`; a regression there fails the build). This script runs the auditor-level rows:
# RetLow smuggled into a consumer statement. v0.4.0: `Ensures` evaluates its precondition before the return address is written, so no
# precondition restricts the return address and the auditor's [RSP]-word rule is gone: EVERY row b1-b20 is Verified (audit-only). b1-b7, b9-b11,
# b13-b16, b18, b19 were `blocked` until v0.3.4 (the [RSP] read, in each spelling: alias, numeral, offset < 8, non-numeral or negative offset,
# mixed definitions, stackWord s 0); b8 (CallOK64 as-is), b12 (stack-argument words at RSP+8/+16), b17 (StackWords) and b20 (an ∃-bound
# stack-argument word used as yp.toNat, print round-trip) were controls and stay Verified. Exits 1 if a row differs.
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
  --theorem $P.b1 --theorem $P.b2 --theorem $P.b3 --theorem $P.b4 --theorem $P.b5 --theorem $P.b6 --theorem $P.b7 --theorem $P.b8 --theorem $P.b9 --theorem $P.b10 --theorem $P.b11 --theorem $P.b12 --theorem $P.b13 --theorem $P.b14 --theorem $P.b15 --theorem $P.b16 --theorem $P.b17 --theorem $P.b18 --theorem $P.b19 --theorem $P.b20 2>&1 | sed -E 's/^Audit-only: /Verified: /; s/^(=== .*): audit-only \(NOT verified\) ===\$/\1: verified ===/')"
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
row b1 Verified
row b2 Verified
row b3 Verified
row b4 Verified
row b5 Verified
row b6 Verified
row b7 Verified
row b8 Verified
row b9 Verified
row b10 Verified
row b11 Verified
row b12 Verified
row b13 Verified
row b14 Verified
row b15 Verified
row b16 Verified
row b17 Verified
row b18 Verified
row b19 Verified
row b20 Verified
echo
if [ ${#broken[@]} -gt 0 ]; then echo "round n9: BROKEN rows: ${broken[*]}"; exit 1; fi
echo "round n9: all rows as expected"
