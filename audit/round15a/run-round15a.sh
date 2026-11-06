#!/usr/bin/env bash
# Round-15a rows (RT15A). Every row must be REJECTED, with the reason checked:
#   C1..C6  vacuous theorems that assume NewobjectContract in disguise (Prop hyp / PLift / Subtype / Nonempty /
#           in the precondition / in the conclusion): blocked by non-vacuity (C1,C5,C6) or the round-10/13 binder checks.
#   R1      Go test TestRound15aLakefileNotCacheable + TestRound15aResolvableSubsetOfSnapshot (result-cache key coverage).
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"; cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=audit/round15a; J="${JANUS_AUDIT_BIN:-$root/$R/janus}"
[ -n "${JANUS_AUDIT_BIN:-}" ] || go build -o "$J" ./cmd/janus || exit 1
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
W=$R/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-round15a.XXXXXX")" || exit 1; trap 'rm -rf "$T"' EXIT
# JANUS_AUDIT_KEEP_CACHE=1: use the caller's (pre-seeded) JANUS_CACHE_DIR instead of an empty private one
if [ "${JANUS_AUDIT_KEEP_CACHE:-}" != 1 ]; then mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"; fi
. scripts/example-contracts.sh
mapfile -t tg < <(scripts/example-targets.sh NewPair)
"$J" extract artifacts/examples-arm64 "$(example_symbol NewPair)" "$W/NewPair" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
broken=()
all="$("$J" verify --janus-root "$root" --proof $R/attacks/ContractForms.lean "$W/NewPair" \
  --theorem Proof.ctl --theorem Proof.plift --theorem Proof.sub --theorem Proof.nonempty --theorem Proof.inpre --theorem Proof.inconc 2>&1)"
row() { # NAME reason
  local blk; blk="$(awk -v n="=== Proof.$1:" 'index($0,n)==1{p=1;print;next} /^=== /{p=0} p' <<<"$all")"
  if grep -q 'FAILED' <<<"$blk" && grep -qF -- "$2" <<<"$blk"; then echo "  $1 rejected ($2)"; else echo "  $1 BROKEN"; broken+=("$1"); fi
}
row ctl 'Stage: non-vacuity'; row plift 'non-Prop binder'; row sub 'non-Prop binder'
row nonempty 'round 10 V1'; row inpre 'Stage: non-vacuity'; row inconc 'Stage: non-vacuity'
. "$root/audit/lib/gotest-row.sh"
gotest_row round15a-R1 memcap go test -count=1 -timeout 60m -run 'TestRound15a' ./cmd/janus || broken+=("R1")
[ ${#broken[@]} -gt 0 ] && { echo "round 15a: BROKEN rows: ${broken[*]}"; exit 1; }
echo "round 15a: all rows as expected"
