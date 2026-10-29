#!/usr/bin/env bash
# Self-test of scripts/gate-speedcheck.py: a regression of 1.5x or more fails and names item, baseline,
# measured time and ratio; the absolute floor keeps a few-second item from flapping; a new item is
# reported, not failed; an item that did not pass is not judged; `update` writes a baseline that the
# same run then passes.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-speed.XXXXXX")"; trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
chk() { python3 -I "$here/scripts/gate-speedcheck.py" check "$t/tl" "$t/base" "$t/logs"; }
mkdir -p "$t/logs"
printf 'amd64:DeferOrder\t90\t3.2\narm64:Add\t3\t0.3\narm64:Gone\t5\t0.1\n' > "$t/base"
cat > "$t/tl" <<'E'
{"kind":"gate","commit":"x","jobs":2,"load1":55}
{"kind":"item","pool":"verify","id":"amd64:DeferOrder","status":"PASS","wall":1320}
{"kind":"item","pool":"verify","id":"arm64:Add","status":"PASS","wall":9}
{"kind":"item","pool":"verify","id":"arm64:New","status":"PASS","wall":3}
{"kind":"item","pool":"verify","id":"arm64:Gone","status":"FAIL","wall":500}
E
out=$(chk); rc=$?
[ $rc = 1 ] && ok "regression fails" || bad "rc=$rc"
grep -q 'SLOW amd64:DeferOrder: baseline 90.0s, measured 1320.0s, ratio 14.67' <<<"$out" && ok "message names item, baseline, measured, ratio" || bad "message: $out"
grep -q 'SLOW arm64:Add' <<<"$out" && bad "floor: 3s -> 9s must not flap" || ok "absolute floor (3s -> 9s passes)"
grep -q 'NEW (no baseline, not failed): arm64:New' <<<"$out" && ok "new item reported" || bad "new item"
grep -q 'arm64:Gone' <<<"$out" && bad "failed item judged" || ok "non-PASS items not judged"
grep -q 'load 55' <<<"$out" && ok "host load printed" || bad "load"
python3 -I "$here/scripts/gate-speedcheck.py" update "$t/tl" "$t/base2" "$t/logs" >/dev/null
python3 -I "$here/scripts/gate-speedcheck.py" check "$t/tl" "$t/base2" "$t/logs" >/dev/null && ok "update then check passes" || bad "update/check"
# peaks from janus's own reports (memoryGuard.peakBytes), the max over an item's theorems; a stale report is ignored
mkdir -p "$t/art/Heavy/verified" "$t/art/amd64/Light" "$t/art/Stale"
printf '{"memoryGuard":{"peakBytes":%d}}' $((5 * 1073741824 + 536870912)) > "$t/art/Heavy/verified.json"
printf '{"memoryGuard":{"peakBytes":%d}}' $((6 * 1073741824)) > "$t/art/Heavy/verified/Proof.Witness.nonvacuous.json"
printf '{"memoryGuard":{"peakBytes":%d}}' $((300 * 1048576)) > "$t/art/amd64/Light/verified.json"
printf '{"memoryGuard":{"peakBytes":%d}}' $((9 * 1073741824)) > "$t/art/Stale/verified.json"; touch -d '3 days ago' "$t/art/Stale/verified.json"
now=$(date +%s)
cat > "$t/tl2" <<E2
{"kind":"gate","commit":"x","jobs":2,"load1":5,"start":$((now - 5))}
{"kind":"item","pool":"verify","id":"arm64:Heavy","status":"PASS","wall":100,"start":1,"end":2}
{"kind":"item","pool":"verify","id":"amd64:Light","status":"PASS","wall":5,"start":1,"end":2}
{"kind":"item","pool":"verify","id":"arm64:Stale","status":"PASS","wall":5,"start":1,"end":2}
{"kind":"item","pool":"verify","id":"arm64:NoReport","status":"PASS","wall":5,"start":1,"end":2}
E2
python3 -I "$here/scripts/gate-speedcheck.py" update "$t/tl2" "$t/base3" "$t/logs" "$t/art" >/dev/null
grep -q $'^arm64:Heavy\t100.0\t6.00$' "$t/base3" && ok "heavy item: max over its theorems (6.00 GiB)" || bad "heavy: $(grep Heavy "$t/base3")"
grep -q $'^amd64:Light\t5.0\t0.29$' "$t/base3" && ok "light item: 0.29 GiB" || bad "light: $(grep Light "$t/base3")"
grep -q $'^arm64:Stale\t5.0\t0.00$' "$t/base3" && ok "a stale report is ignored" || bad "stale: $(grep Stale "$t/base3")"
grep -q $'^arm64:NoReport\t5.0\t0.00$' "$t/base3" && ok "an item without a report records 0 (admission then uses the conservative estimate)" || bad "noreport"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
