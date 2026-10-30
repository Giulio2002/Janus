#!/usr/bin/env bash
# Self-test of scripts/gate.sh's lane memory limits and kept/reused isolated trees. Uses the filtered gate
# (--only testlane,rtasl-btf): 1. a lake lane runs with a 48G per-job limit (memguard says so), the
# override JANUS_GATE_MEM_RTASL_BTF applies; 2. a failing lane keeps the isolated tree and reports its path;
# 3. a rerun of the same sources reuses it; 4. a passing run removes it. Needs a built tree (run in a worktree
# where `lake build` is done), so it is a script test, not part of go test.
set -uo pipefail
# private out dir and timeline: never the running gate's (inherited from gate.sh when run by the gotest lane)
unset POOL_TIMELINE POOL_DIR JANUS_POOL_DIR POOL_BUDGET_KB POOL_DEBUG POOL_RES_TRACE POOL_MEM_HEADROOM_KB POOL_JOB_MEM_KB JANUS_VERIFY_MEM_BUDGET_GIB JANUS_GATE_PG JANUS_GATE_AUTO_WHY JANUS_GATE_ROUNDS_LANES JANUS_GATE_AUTO_BUDGET
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"; cd "$here"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-gatelanes.XXXXXX")"; trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
g() { JANUS_GATE_FORCE=1 scripts/gate.sh -j 1 --only testlane,rtasl-btf --out "$t/$1" > "$t/$1.log" 2>&1; echo $?; }
export JANUS_GATE_TEST_LANE='. scripts/lib/memguard.sh; echo "LANELIMIT=$(( $(memguard_limit) >> 30 ))G JANUS_MEM_MAX=$JANUS_MEM_MAX"; exit 1'
rc=$(g r1); [ "$rc" = 1 ] && ok "failing lane fails the gate" || bad "rc=$rc"
grep -q 'LANELIMIT=48G JANUS_MEM_MAX=48G' "$t/r1/lanes/testlane.log" && ok "lane runs under the 48G per-job limit (memguard_limit)" || bad "limit: $(grep LANELIMIT "$t/r1/lanes/testlane.log")"
kept=$(sed -n 's/^gate: isolated lake-lane trees KEPT.*: //p' "$t/r1.log")
[ -n "$kept" ] && [ -d "$kept" ] && ok "tree kept at a reported path ($kept)" || bad "tree not kept: $(grep -i 'kept\|isolated' "$t/r1.log")"
rc=$(g r2); grep -q "gate: reusing $kept/asl" "$t/r2.log" && ok "rerun reuses the tree" || bad "no reuse: $(grep isolated "$t/r2.log")"
export JANUS_GATE_TEST_LANE='. scripts/lib/memguard.sh; echo "LANELIMIT=$(( $(memguard_limit) >> 30 ))G"' JANUS_GATE_MEM_TESTLANE=7G
rc=$(g r3); [ "$rc" = 0 ] && ok "passing run passes" || bad "rc=$rc"
grep -q 'LANELIMIT=7G' "$t/r3/lanes/testlane.log" && ok "JANUS_GATE_MEM_* override applies" || bad "override"
[ ! -d "$kept" ] && ok "tree removed after a pass" || bad "tree still there"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
