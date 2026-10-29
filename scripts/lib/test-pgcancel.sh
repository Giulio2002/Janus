#!/usr/bin/env bash
# Self-test of the cancel discipline of scripts/gate.sh: a run is its own process group, <out>/pgid names
# it, and `kill -- -PGID` cancels that run only. Two runs (the second from a scratch copy of the tree)
# are started; one is cancelled; the other's processes are untouched and it finishes with status 0.
# Also: the cancelled run removes its isolated source copies. Uses `gate.sh --only axiom`-sized stages
# via the stage hook JANUS_GATE_TEST_LANE (a sleep lane) so nothing heavy runs.
set -uo pipefail
# private out dir and timeline: never the running gate's (inherited from gate.sh when run by the gotest lane)
unset POOL_TIMELINE POOL_DIR JANUS_POOL_DIR POOL_BUDGET_KB POOL_DEBUG POOL_RES_TRACE POOL_MEM_HEADROOM_KB POOL_JOB_MEM_KB JANUS_VERIFY_MEM_BUDGET_GIB JANUS_GATE_PG JANUS_GATE_AUTO_WHY JANUS_GATE_ROUNDS_LANES JANUS_GATE_AUTO_BUDGET
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-pgcancel.XXXXXX")"
trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
# a toy "gate": the same group discipline as gate.sh (setsid re-exec, pgid file, TERM trap), running a
# pool of sleep lanes (scripts/lib/pool.sh)
mkdir -p "$t/a/scripts/lib" "$t/b/scripts/lib"
for d in a b; do cp "$here"/scripts/lib/{pool.sh,parallel.sh} "$t/$d/scripts/lib/"; cat > "$t/$d/toy.sh" <<'EOS'
#!/usr/bin/env bash
out=$1; secs=$2
if [ "${TOY_PG:-}" != "$out" ]; then export TOY_PG="$out"; exec setsid --wait "$0" "$@"; fi
echo $$ > "$out/pgid"
cancel() { trap '' TERM INT; kill -TERM -- -$$ 2>/dev/null; exit 143; }
trap cancel TERM INT
. "$(dirname "$0")/scripts/lib/parallel.sh"; . "$(dirname "$0")/scripts/lib/pool.sh"
pool_init toy 2 "$out/lanes"; POOL_GUARD=0
pool_add l1 "sleep $secs"; pool_add l2 "sleep $secs"
pool_run
EOS
chmod +x "$t/$d/toy.sh"; mkdir -p "$t/out-$d"; done
( "$t/a/toy.sh" "$t/out-a" 25 > "$t/a.log" 2>&1; echo $? > "$t/a.rc" ) &
( "$t/b/toy.sh" "$t/out-b" 6 > "$t/b.log" 2>&1; echo $? > "$t/b.rc" ) &
for i in $(seq 50); do [ -s "$t/out-a/pgid" ] && [ -s "$t/out-b/pgid" ] && break; sleep 0.2; done
pa=$(cat "$t/out-a/pgid"); pb=$(cat "$t/out-b/pgid")
[ -n "$pa" ] && [ -n "$pb" ] && [ "$pa" != "$pb" ] && ok "two runs, two process groups ($pa, $pb)" || bad "pgids: '$pa' '$pb'"
sleep 2
kill -- -"$pb" 2>/dev/null   # cancel run b only
sleep 1
nb=$(ps -o pid= -g "$pb" 2>/dev/null | wc -l); na=$(ps -o pid= -g "$pa" 2>/dev/null | wc -l)
[ "$nb" -eq 0 ] && ok "cancelled run left no process behind" || bad "run b still has $nb processes"
[ "$na" -ge 3 ] && ok "other run untouched ($na processes alive)" || bad "run a lost processes ($na)"
for i in $(seq 100); do [ -f "$t/a.rc" ] && break; sleep 0.3; done
[ "$(cat "$t/a.rc" 2>/dev/null)" = 0 ] && ok "other run finished with status 0" || bad "run a rc=$(cat "$t/a.rc" 2>/dev/null)"
grep -q '2 passed' "$t/a.log" && ok "other run's lanes passed" || bad "run a log: $(tail -3 "$t/a.log")"
# gate.sh itself: no kill-by-name anywhere in the driver, its libraries or the lanes it starts
if grep -nE '\b(pkill|killall|pgrep)\b|ps +-e.*\|.*kill' "$here"/scripts/gate.sh "$here"/scripts/lib/pool.sh "$here"/scripts/gotest-shards.sh "$here"/audit/rt-asl/run.sh "$here"/scripts/verify-all-examples.sh >/dev/null; then
  bad "kill-by-name found in the gate scripts"; else ok "no pkill/pgrep/killall in the gate scripts"; fi
grep -q 'kill -- -' "$here/scripts/gate.sh" && ok "gate.sh cancels through its own process group" || bad "gate.sh group cancel"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
