#!/usr/bin/env bash
# Self-test of scripts/lib/pool.sh with toy items (seconds). Checks:
#   1. longest first by the recorded times, items without a time first;
#   2. every result line is printed when its item finishes (a fast item's line precedes the slow one's);
#   3. PASS / FAIL / TIMEOUT / FAIL (a killed item; MISSING: the item's own shell vanished) / SKIP are told apart, any of FAIL, TIMEOUT and
#      MISSING fails the pool and is listed in POOL_FAILED;
#   4. a progress line appears while an item runs; the timeline has one JSON line per item;
#   5. at most JOBS items run at once;
#   6. the wall of a passing item lands in <id>.time, a skipped one has none.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-pool.XXXXXX")"
trap 'rm -rf "$t"' EXIT
. "$here/parallel.sh"
. "$here/pool.sh"
fail=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fail=1; }

printf 'slow\t50\nmid\t20\nfast\t1\n' > "$t/times"
POOL_PROGRESS_SECS=1 POOL_TIMELINE="$t/timeline.jsonl"
pool_init toy 2 "$t/state"
pool_times "$t/times"
pool_add fast 'echo fast; exit 0'
pool_add slow 'sleep 3; exit 0'
pool_add mid 'echo mid >> '"$t"'/order; sleep 1'
pool_add new 'echo new >> '"$t"'/order; sleep 1'
pool_add bad 'echo oops; exit 3'
pool_add tmo 'echo "TIMEOUT: janus verify exceeded"; exit 1'
pool_add gone 'kill -9 $(ps -o ppid= -p $BASHPID); sleep 5'
pool_add killed 'kill -9 $BASHPID'
pool_add skp 'echo "arm64  X skipped (unchanged since)"; exit 0'
pool_add conc 'echo x >> '"$t"'/running; sleep 1.5; echo y >> '"$t"'/running'
rc=0
pool_run > "$t/out" 2>&1 || rc=$?
cat "$t/out"
[ "$rc" = 1 ] && ok "pool fails when an item fails" || bad "pool rc=$rc"
for want in "PASS +fast" "PASS +slow" "FAIL +bad" "TIMEOUT +tmo" "FAIL +gone" "FAIL +killed" "SKIP +skp"; do
  grep -Eq "$want" "$t/out" && ok "result line: $want" || bad "no result line: $want"
done
[ "${POOL_FAILED[*]}" = "${POOL_FAILED[*]}" ] && for f in bad tmo gone killed; do
  case " ${POOL_FAILED[*]} " in *" $f "*) ok "$f in POOL_FAILED" ;; *) bad "$f missing from POOL_FAILED" ;; esac
done
# order: the first two lines of order are "new" then "mid" (no time first, then longest)
[ "$(head -1 "$t/order")" = new ] && ok "item without a time starts first" || bad "order: $(cat "$t/order")"
grep -n 'PASS.* fast\|PASS.* slow' "$t/out" | head -2 | grep -q fast && ok "fast result streamed before slow" || bad "fast not before slow"
grep -q '^-- pool toy:' "$t/out" && ok "progress line printed" || bad "no progress line"
[ "$(wc -l < "$t/timeline.jsonl")" -ge 11 ] && ok "timeline has an item line each + the pool" || bad "timeline: $(wc -l < "$t/timeline.jsonl") lines"
[ -f "$t/state/slow.time" ] && [ ! -f "$t/state/skp.time" ] && [ ! -f "$t/state/bad.time" ] && ok "walls recorded for passes only" || bad "time files"
# concurrency bound
mx=0; cur=0; while read -r l; do if [ "$l" = x ]; then cur=$((cur+1)); else cur=$((cur-1)); fi; [ $cur -gt $mx ] && mx=$cur; done < "$t/running"
[ "$mx" -le 2 ] && ok "at most 2 items at once" || bad "saw $mx at once"

# needs: an item runs after the items it needs passed; an item whose need failed is BLOCKED (a failure)
pool_init deps 2 "$t/state2"
pool_add dep-b 'echo b >> '"$t"'/dorder' "" "dep-a"
pool_add dep-a 'sleep 1; echo a >> '"$t"'/dorder'
pool_add dep-c 'echo c' "" "dep-bad"
pool_add dep-bad 'exit 1'
pool_add dep-u 'echo u' "" "nonexistent"
pool_add dep-cyc1 'echo x' "" "dep-cyc2"
pool_add dep-cyc2 'echo x' "" "dep-cyc1"
rc=0; pool_run > "$t/out2" 2>&1 || rc=$?
[ "$(tr '\n' ' ' < "$t/dorder")" = "a b " ] && ok "needs: b ran after a" || bad "needs order: $(cat "$t/dorder")"
for w in "BLOCKED +dep-c" "BLOCKED +dep-u" "BLOCKED +dep-cyc1" "BLOCKED +dep-cyc2" "FAIL +dep-bad"; do
  grep -Eq "$w" "$t/out2" && ok "needs: $w" || { bad "needs: no $w"; cat "$t/out2"; }
done
[ "$rc" = 1 ] && ok "blocked items fail the pool" || bad "deps rc=$rc"
exit $fail
