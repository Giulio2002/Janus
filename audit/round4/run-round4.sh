#!/usr/bin/env bash
# Round-4 regression rows (docs/AUDIT-ROUND4.md). Exits 1 if a fixed finding regresses.
# Writes only under audit/round4/work/ and audit/round4/bin/.  Usage: audit/round4/run-round4.sh [-j N]  (-j: blocks at once, scripts/lib/parallel.sh)
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=../../scripts/lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
# shellcheck source=../../scripts/lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
par_init "$@"
J="$root/audit/round4/bin/janus"; mkdir -p "$(dirname "$J")"
go build -o "$J" ./cmd/janus || exit 1
memguard_lake build Janus Janus.Tools.Audit >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
W=audit/round4/work; mkdir -p $W
"$J" extract artifacts/examples-arm64 example.com/basic.Add $W/Add >/dev/null || exit 1
broken=()

# D1/D2 verify and then explain the same artifact (its verified.json): one block.
d12_block() {
echo "== D1/D2: disclosed definition bodies round-trip, and are shown by verify and explain =="
# The original fixture's literal (256 at BitVec 8) is out of range: since round 6 (F2) it is
# rejected outright. The disclosure property is checked on the in-range variant D1b.
out="$("$J" verify --janus-root "$root" --proof audit/round4/attacks/D1_def_numeral_type.lean $W/Add 2>&1)"
grep -m1 -E '^(Verified|Invalid)' <<<"$out" | cut -c1-140 | sed 's/^/  D1 /'
grep -q 'out-of-range numeral' <<<"$out" || { echo "  >>> D1 (256 : BitVec 8) is no longer rejected as an out-of-range numeral"; broken+=(D1-wrap); }
out="$("$J" verify --janus-root "$root" --proof audit/round4/attacks/D1b_def_numeral_type_inrange.lean $W/Add 2>&1)"
grep -m1 -E '^(Verified|Invalid)' <<<"$out" | sed 's/^/  D1b /'
grep -q 'Proof-local definitions used by the statement' <<<"$out" || { echo "  >>> D2 regressed: verify does not show definitions"; broken+=(D2-verify); }
grep -q 'Proof.wide : Prop := (255 : BitVec' <<<"$out" || { echo "  >>> D1 regressed: disclosure hides the numeral type"; broken+=(D1); }
ex="$("$J" explain $W/Add 2>&1)"
grep -q 'Proof.wide : Prop := (255 : BitVec' <<<"$ex" || { echo "  >>> D2 regressed: explain does not show definitions"; broken+=(D2-explain); }
}
d3_block() {
echo "== D3: control characters in report text are neutralized (unit test) =="
(cd cmd/janus && memguard_run -n go-test -- go test -run TestTermSafe . >/dev/null 2>&1) || { echo "  >>> D3 regressed"; broken+=(D3); }
}
par_run d12_block
par_run d3_block
par_wait

if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo; echo "All round-4 rows as expected."
