#!/usr/bin/env bash
# Self-test of the pool's per-item memory admission (scripts/lib/pool.sh): a fake item set of a few heavy items
# (recorded peak 6 GiB) and many small ones (0.3 GiB), 12 slots, a 20 GiB budget. Checks: peak concurrency >= 10
# (small items run wide), the sum of reservations never exceeds the budget at any admission step, the heavy items
# never run all together (3 x 7.8 GiB > 20 GiB), an unknown item reserves the conservative 9.15 GiB, a deferral
# is logged under POOL_DEBUG, and the timeline pool line records peakConcurrency / peakReservedGiB.
set -uo pipefail
# private out dir and timeline: never the running gate's (inherited from gate.sh when run by the gotest lane)
unset POOL_TIMELINE POOL_DIR JANUS_POOL_DIR POOL_BUDGET_KB POOL_DEBUG POOL_RES_TRACE POOL_MEM_HEADROOM_KB POOL_JOB_MEM_KB JANUS_VERIFY_MEM_BUDGET_GIB JANUS_GATE_PG JANUS_GATE_AUTO_WHY JANUS_GATE_ROUNDS_LANES JANUS_GATE_AUTO_BUDGET
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-poolmem.XXXXXX")"; trap 'rm -rf "$t"' EXIT
. "$here/parallel.sh"; . "$here/pool.sh"
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
{ for i in 1 2 3; do printf 'heavy:%d\t60\t6.00\n' $i; done; for i in $(seq 40); do printf 'small:%d\t5\t0.30\n' $i; done; } > "$t/base"
POOL_TIMELINE="$t/tl" POOL_DEBUG=1 POOL_RES_TRACE="$t/trace" POOL_GUARD=0 POOL_PROGRESS_SECS=100
POOL_BUDGET_KB=$((20 * 1048576)) POOL_MEM_HEADROOM_KB=1
pool_init selftest-mem 12 "$t/state"; pool_peaks "$t/base"
for i in 1 2 3; do pool_add "heavy:$i" "echo \$\$ >> $t/hv; sleep 1.5; echo \$\$ >> $t/hv"; done
for i in $(seq 40); do pool_add "small:$i" "sleep 0.4"; done
pool_add unknown:1 "sleep 0.3"
pool_run > "$t/out" 2>&1; rc=$?
[ "$rc" = 0 ] && ok "pool passes ($(grep -c PASS "$t/out") items)" || { bad "rc=$rc"; tail -5 "$t/out"; }
pk=$(sed -n 's/.*"peakConcurrency":\([0-9]*\).*/\1/p' "$t/tl")
[ "${pk:-0}" -ge 10 ] && ok "peak concurrency $pk >= 10" || bad "peak concurrency ${pk:-none}"
budget=$((20 * 1048576))
over=$(awk -v b=$budget '$1 > b { n++ } END { print n + 0 }' "$t/trace")
[ "$over" = 0 ] && ok "the sum of reservations is within the budget at all $(wc -l < "$t/trace") admission steps (max $(sort -n "$t/trace" | tail -1 | cut -d' ' -f1) kB of $budget)" || bad "$over steps over budget"
grep -q '"peakReservedGiB"' "$t/tl" && ok "timeline: $(sed -n 's/.*\("peakConcurrency".*\)}/\1/p' "$t/tl")" || bad "timeline fields"
# heavy items: at most 2 at a time (3 x 7.8 GiB = 23.4 > 20)
python3 -I - "$t/hv" <<'PY' && ok "at most 2 heavy items at once" || bad "3 heavy items ran together"
import sys
c={}
ev=[l.split()[0] for l in open(sys.argv[1])]
live=set(); mx=0
for p in ev:
    if p in live: live.discard(p)
    else: live.add(p); mx=max(mx,len(live))
sys.exit(0 if mx<=2 else 1)
PY
grep -q 'pool selftest-mem: defer heavy:3' "$t/out" && ok "deferral logged: $(grep -m1 'defer' "$t/out")" || bad "no deferral log"
# unknown item reservation is the conservative one
r=$(POOL_KEYS=(unknown:1) _pool_res_kb 0); [ "$r" = 9594470 ] && ok "unknown item reserves 9.15 GiB" || bad "unknown reservation $r"
# a budget below one item still admits the first item (no deadlock)
POOL_BUDGET_KB=1000; pool_init selftest-mem2 4 "$t/state2"; pool_peaks "$t/base"; pool_add heavy:1 "sleep 0.1"; pool_add heavy:2 "sleep 0.1"
pool_run > "$t/out2" 2>&1 && ok "a tiny budget serialises but never deadlocks" || bad "tiny budget: $(tail -2 "$t/out2")"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
