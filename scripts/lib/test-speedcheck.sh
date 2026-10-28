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
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
