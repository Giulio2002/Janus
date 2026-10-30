#!/usr/bin/env bash
# Self-test of the gate's stage graph (scripts/lib/dag.sh) run through the real pool (scripts/lib/pool.sh) with FAKE stages
# (sleep + a start/end log): 1. the graph is consistent; every reader of the shared framework build (verify, gotest, rounds,
# decoder, every tree copy and so every lake lane) has pre-pin in its closure, i.e. starts only after the build it reads has
# finished and been hashed; 2. a stage starts only after all its dependencies ended; 3. independent stages overlap (lanes
# start while the framework build is still running; the fixture runs beside the verify pool; axiom/govet need nothing);
# 4. a failing stage blocks exactly its dependents (BLOCKED) and fails the gate while independent stages still run.
set -uo pipefail
unset POOL_TIMELINE JANUS_POOL_DIR JANUS_GATE_PG POOL_BUDGET_KB
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-dag.XXXXXX")"; trap 'rm -rf "$t"' EXIT
. "$here/parallel.sh"; . "$here/pool.sh"; . "$here/dag.sh"
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
dag_check && ok "the stage graph is consistent (no unknown dependency, no cycle)" || bad "graph"
for r in verify gotest rounds decoder tree-x86 tree-asl tree-aslv tree-go x86 oracle asl-build sail-build asl-verify rtasl-prove rtasl-replay rtasl-go rtasl-btf; do
  dag_closure "$r" | grep -qx pre-pin || bad "$r does not wait for pre-pin"
done; ok "every reader of the shared framework build waits for pre-pin"
for r in axiom govet cachekeys; do [ -z "${DAG_DEPS[$r]}" ] && ok "$r needs nothing" || bad "$r has deps"; done
dag_closure pre-pin | grep -qx pre-stamp && ! dag_closure pre-stamp | grep -qx pre-pin && ok "pre-pin waits for pre-stamp (every write janus can make to the shared build precedes the hash)" || bad "stamp before pin"
dag_closure pre-pin | grep -qx pre-lake && ! dag_closure pre-lake | grep -qx pre-pin && ok "pre-pin follows pre-lake (the only writer), not the reverse" || bad "pin/lake order"

dag_closure pre-fixture | grep -qx pre-stamp && dag_closure pre-fixture | grep -qx pre-pin && ! dag_closure pre-pin | grep -qx pre-fixture && ok "pre-fixture waits for pre-stamp and pre-pin (its --janus-root verification reads a fresh stamp after the hash)" || bad "fixture ordering"
# a rerun into the same --out with a stale marker: gate.sh removes it before any stage, so the lakeguard is not armed early
here_repo="$(cd "$here/../.." && pwd)"
grep -n 'rm -f "$out/.pinned" "$out/fw_hash0"' "$here_repo/scripts/gate.sh" | cut -d: -f1 > "$t/rmline"
rml=$(head -1 "$t/rmline"); pml=$(grep -n '^pre_pin()' "$here_repo/scripts/gate.sh" | cut -d: -f1); poolrun=$(grep -n '^pool_run\|pool_run ||' "$here_repo/scripts/gate.sh" | head -1 | cut -d: -f1)
[ -n "$rml" ] && [ "$rml" -gt "$pml" ] && [ "$rml" -lt "$poolrun" ] && ok "gate.sh clears a stale .pinned/fw_hash0 before the pool runs" || bad "stale marker is not cleared before the stages ($rml $pml $poolrun)"
mkdir -p "$t/rerun/root" "$t/rerun/out"; : > "$t/rerun/root/lakefile.toml"; : > "$t/rerun/out/.pinned"; echo stale > "$t/rerun/out/fw_hash0"
cat > "$t/rerun/real" <<'EOS'
#!/bin/sh
echo "$@" > "$RERUN_LOG"
EOS
chmod +x "$t/rerun/real"
out="$t/rerun/out"; eval "$(grep -m1 'rm -f "$out/.pinned" "$out/fw_hash0"' "$here_repo/scripts/gate.sh")"
( cd "$t/rerun/root" && RERUN_LOG="$t/rerun/log" JANUS_REAL_LAKE="$t/rerun/real" JANUS_LAKEGUARD_ROOT="$(pwd -P)" JANUS_LAKEGUARD_PIN="$out/.pinned" "$here/lakeguard/lake" build X )
[ "$(cat "$t/rerun/log")" = "build X" ] && [ ! -e "$out/fw_hash0" ] && ok "after the startup cleanup a stale .pinned does not make lake build a --no-build" || bad "guard armed by a stale marker: $(cat "$t/rerun/log")"
( : > "$out/.pinned"; cd "$t/rerun/root" && RERUN_LOG="$t/rerun/log" JANUS_REAL_LAKE="$t/rerun/real" JANUS_LAKEGUARD_ROOT="$(pwd -P)" JANUS_LAKEGUARD_PIN="$out/.pinned" "$here/lakeguard/lake" build X )
[ "$(cat "$t/rerun/log")" = "build --no-build X" ] && ok "with a fresh pin the guard is armed (--no-build)" || bad "guard not armed after the pin: $(cat "$t/rerun/log")"

run() { # DIR FAILSTAGE: queue every stage with a fake body; returns the pool status
  local d=$1 failst=${2:-} n
  POOL_GUARD=0 POOL_PROGRESS_SECS=100
  pool_init selftest-dag 40 "$d/state"
  for n in "${!DAG_DEPS[@]}"; do
    local dur=0.25; case "$n" in pre-lake) dur=1.5 ;; pre-fixture) dur=5 ;; verify) dur=1.5 ;; esac
    local body="echo START $n \$(date +%s.%N) >> $d/log; sleep $dur; echo END $n \$(date +%s.%N) >> $d/log"
    [ "$n" != "$failst" ] || body="$body; exit 1"
    pool_add "$n" "$body" "$n" "${DAG_DEPS[$n]}"
  done
  pool_run > "$d/out" 2>&1
}
mkdir -p "$t/a"; : > "$t/a/log"; run "$t/a"; rc=$?
[ "$rc" = 0 ] && ok "all stages pass: the pool passes" || { bad "rc=$rc"; tail -5 "$t/a/out"; }
python3 -I - "$t/a/log" "$here/dag.sh" <<'PY' && ok "every stage starts after all its dependencies ended" || bad "a stage started before a dependency ended"
import sys,re,subprocess
ev={}
for l in open(sys.argv[1]):
    k,n,ts=l.split(); ev.setdefault(n,{})[k]=float(ts)
deps=subprocess.run(["bash","-c",'. %s; for n in "${!DAG_DEPS[@]}"; do echo "$n ${DAG_DEPS[$n]}"; done'%sys.argv[2]],capture_output=True,text=True).stdout.splitlines()
bad=[]
for l in deps:
    w=l.split(); n,ds=w[0],w[1:]
    for d in ds:
        if ev[n]["START"] < ev[d]["END"]: bad.append((n,d))
sys.exit(1 if bad or len(ev)<30 else 0)
PY
python3 -I - "$t/a/log" <<'PY' && ok "independent stages overlap: axiom/govet and the example builds run during pre-lake; the fixture overlaps verify; trees start before the fixture ends" || bad "no overlap where the graph allows it"
import sys
ev={}
for l in open(sys.argv[1]):
    k,n,ts=l.split(); ev.setdefault(n,{})[k]=float(ts)
ov=lambda a,b: ev[a]["START"]<ev[b]["END"] and ev[b]["START"]<ev[a]["END"]
need=[("axiom","pre-lake"),("govet","pre-lake"),("pre-ex-arm64","pre-lake"),("pre-fixture","verify"),("tree-asl","pre-fixture")]
sys.exit(0 if all(ov(a,b) for a,b in need) else 1)
PY
# a failure blocks exactly its dependents
mkdir -p "$t/b"; : > "$t/b/log"; run "$t/b" pre-lake; rc=$?
[ "$rc" != 0 ] && ok "a failing pre-lake fails the gate" || bad "rc=0 with a failed pre-lake"
closure_dependents() { for n in "${!DAG_DEPS[@]}"; do dag_closure "$n" | grep -qx pre-lake && [ "$n" != pre-lake ] && echo "$n"; done | sort; }
blocked=$(grep -E '^\[ *[0-9]+/[0-9]+\] BLOCKED' "$t/b/out" | awk '{print $3}' | sort)
[ "$blocked" = "$(closure_dependents)" ] && ok "exactly the stages that depend on pre-lake are BLOCKED ($(wc -l <<<"$blocked"))" || bad "blocked set differs: $(diff <(echo "$blocked") <(closure_dependents) | head -3)"
grep -q 'START axiom' "$t/b/log" && grep -q 'END govet' "$t/b/log" && ok "independent stages still ran (axiom, govet)" || bad "independent stages did not run"
! grep -q 'START verify' "$t/b/log" && ! grep -q 'START gotest' "$t/b/log" && ok "no reader started after the failed build" || bad "a reader ran"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
