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
  dag_has "$r" pre-pin || bad "$r does not wait for pre-pin"
done; ok "every reader of the shared framework build waits for pre-pin"
for r in axiom govet cachekeys; do [ -z "${DAG_DEPS[$r]}" ] && ok "$r needs nothing" || bad "$r has deps"; done
# lane cachekeys also runs the incremental-key liveness check (scripts/lib/test-incr-liveness.sh): it needs nothing built, so it must stay
# dependency-free, and it must touch no shared resource of DAG_RES: its own binary and result cache live in a private mktemp directory
# (never bin/janus, artifacts/Add, the framework build or a shared cache), its only inputs are checked-in files and the toolchain.
grep -n '^add cachekeys ' "$here/../gate.sh" | grep -q 'scripts/lib/test-incr-liveness.sh' && ok "lane cachekeys runs the incremental-key liveness check" || bad "cachekeys does not run test-incr-liveness.sh"
grep -n "^add cachekeys " "$here/../gate.sh" | grep -q "scripts/lib/test-incr-hosttools.sh" && ok "lane cachekeys runs the host-tool key mutation tests" || bad "cachekeys does not run test-incr-hosttools.sh"
! grep -v '^\s*#' "$here/test-incr-liveness.sh" "$here/incr-liveness.sh" "$here/test-incr-hosttools.sh" | grep -qE 'bin/janus|artifacts/(Add|examples)|framework|\.lake' && ok "the liveness check uses only private files (no bin/janus, no shared artifact or build): no DAG_RES entry needed" || bad "the liveness check touches a shared resource"
dag_has pre-pin pre-stamp && ! dag_has pre-stamp pre-pin && ok "pre-pin waits for pre-stamp (every write janus can make to the shared build precedes the hash)" || bad "stamp before pin"
dag_has pre-pin pre-lake && ! dag_has pre-lake pre-pin && ok "pre-pin follows pre-lake (the only writer), not the reverse" || bad "pin/lake order"

dag_has pre-fixture pre-stamp && dag_has pre-fixture pre-pin && ! dag_has pre-pin pre-fixture && ok "pre-fixture waits for pre-stamp and pre-pin (its --janus-root verification reads a fresh stamp after the hash)" || bad "fixture ordering"
# the embedded-only fixture stage starts at t=0: it needs nothing, shares nothing with the user-cache writers or the shared build,
# and the checkout part (pre-fixture) is ordered after it (both write the fixture)
[ -z "${DAG_DEPS[pre-fixture-emb]}" ] && ok "pre-fixture-emb needs nothing (starts at t=0)" || bad "pre-fixture-emb has deps"
for r in pre-lake pre-stamp pre-warm pre-pin; do ! dag_has pre-fixture-emb "$r" || bad "pre-fixture-emb waits for $r"; done
dag_has pre-fixture pre-fixture-emb && dag_has gotest pre-fixture-emb && dag_has rtasl-go pre-fixture-emb && ok "pre-fixture, gotest and rtasl-go wait for the embedded fixture stage" || bad "fixture parts unordered"
! dag_has pre-fixture pre-warm && ok "pre-fixture no longer waits for pre-warm (it never reads the user cache's framework build)" || bad "pre-fixture waits for pre-warm"
for res in framework-build user-cache-framework artifact:Add bin/janus; do grep -q "pre-fixture-emb" <<<"${DAG_RES[$res]}" && bad "pre-fixture-emb listed as touching $res"; done
saved=${DAG_DEPS[pre-fixture]}; DAG_DEPS[pre-fixture]="pre-lake pre-stamp pre-pin"
mut=$(dag_unordered); grep -q 'go-test-fixture: pre-fixture (w) and pre-fixture-emb (w) are not ordered\|go-test-fixture: pre-fixture-emb (w) and pre-fixture (w) are not ordered' <<<"$mut" && ok "the resource check catches an unordered fixture pair" || bad "the resource check missed an unordered fixture pair"
DAG_DEPS[pre-fixture]=$saved
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

# pre-warm (embedded framework, its own extraction dir) runs beside pre-stamp (the checkout, artifacts/Add): they share no resource
! dag_has pre-warm pre-stamp && ! dag_has pre-warm pre-lake && ok "pre-warm waits for neither pre-stamp nor pre-lake (it reads neither the checkout's build nor artifacts/Add)" || bad "pre-warm waits for pre-stamp or pre-lake"

un=$(dag_unordered); [ -z "$un" ] && ok "no two stages touching the same artifact, binary or lock (one writing) can run at once" || { bad "unordered resource users:"; echo "$un" | head -5; }
# the check detects a collision: if pre-warm used artifacts/Add again (as it did when it waited for pre-stamp) it must be reported
saved=${DAG_RES[artifact:Add]}; DAG_RES[artifact:Add]="$saved w:pre-warm"
mut=$(dag_unordered); grep -q 'artifact:Add: pre-stamp (w) and pre-warm (w) are not ordered' <<<"$mut" && ok "the resource check catches a pre-stamp / pre-warm collision on artifacts/Add" || bad "the resource check missed the collision"
DAG_RES[artifact:Add]=$saved

# the flake of `dag_closure X | grep -qx Y` under pipefail: a producer that is still writing when grep leaves gets SIGPIPE (141)
# and the pipeline "fails" although Y is there. A slow producer makes it certain; dag_has must not be fooled.
if ( set -o pipefail; slow() { echo a; sleep 0.05; echo b; sleep 0.05; echo c; }; slow | grep -qx a ) ; then
  bad "premise: a slow producer did not make the early-exit pipeline fail (the test below would prove nothing)"
else
  dag_closure_real=$(declare -f dag_closure)
  dag_closure() { echo "$1"; sleep 0.05; echo pre-lake; sleep 0.05; echo late; sleep 0.05; echo later; }
  ( set -o pipefail; dag_has rounds pre-lake ) && ok "dag_has finds a dependency although the producer is slow (no SIGPIPE false negative)" || bad "dag_has is fooled by a slow producer"
  eval "$dag_closure_real"
fi

# host sanity: gate.sh refuses to run when /dev/null is not the null device, before any stage
hs=$(grep -n '^if \[ ! -c /dev/null \]' "$here_repo/scripts/gate.sh" | head -1 | cut -d: -f1); pl=$(grep -n '^pre_pin()' "$here_repo/scripts/gate.sh" | cut -d: -f1)
[ -n "$hs" ] && [ "$hs" -lt "$pl" ] && ok "gate.sh refuses a host whose /dev/null is not a character device (before any stage)" || bad "no /dev/null preflight in gate.sh"

# the replay sizing goes to a FILE (JANUS_REPLAY_SIZING_FILE), never to JANUS_MEMGUARD_LOG's stderr lines (they broke parsed rows)
rs=$(grep -n '^: > "$out/replay-sizing.log"; export JANUS_REPLAY_SIZING_FILE=' "$here_repo/scripts/gate.sh" | head -1 | cut -d: -f1); pl2=$(grep -n '^pre_pin()' "$here_repo/scripts/gate.sh" | cut -d: -f1)
[ -n "$rs" ] && [ "$rs" -lt "$pl2" ] && ! grep -q 'export JANUS_MEMGUARD_LOG' "$here_repo/scripts/gate.sh" && ok "gate.sh exports JANUS_REPLAY_SIZING_FILE before the stages and does not export JANUS_MEMGUARD_LOG" || bad "replay sizing wiring wrong"

grep -q '^unset JANUS_MEMGUARD_LOG JANUS_MEMGUARD_VERBOSE' "$here_repo/scripts/gate.sh" && ok "gate.sh unsets JANUS_MEMGUARD_LOG / VERBOSE (rows parse the first output line)" || bad "gate.sh may inherit JANUS_MEMGUARD_LOG"

# the round scripts run `go test` (D3, A1, D1, ...): their TestMain waits for the fixture lock while pre-fixture builds the fixture (1583 s
# when the verifier changed), longer than go test's default 10 min timeout: rounds must start after pre-fixture
dag_has rounds pre-fixture && ok "rounds waits for pre-fixture (its go test rows block on the fixture lock otherwise)" || bad "rounds does not wait for pre-fixture"

# every `go test` of the gate and round scripts has an explicit -timeout (the default 10 min fired while the fixture was rebuilt)
nt=$(cd "$here_repo" && grep -rn "go test " scripts audit --include=*.sh | grep -v -e "-timeout" -e "go test -c" | grep -v "^[^:]*:[0-9]*:[[:space:]]*#" | grep -v 'echo\|tmark\|printf\|dag_has\|usage' | wc -l)
[ "$nt" = 0 ] && ok "every go test in the gate and round scripts has an explicit -timeout" || bad "$nt go test call(s) without -timeout"

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
closure_dependents() { for n in "${!DAG_DEPS[@]}"; do dag_has "$n" pre-lake && [ "$n" != pre-lake ] && echo "$n"; done | sort; }
blocked=$(grep -E '^\[ *[0-9]+/[0-9]+\] BLOCKED' "$t/b/out" | awk '{print $3}' | sort)
[ "$blocked" = "$(closure_dependents)" ] && ok "exactly the stages that depend on pre-lake are BLOCKED ($(wc -l <<<"$blocked"))" || bad "blocked set differs: $(diff <(echo "$blocked") <(closure_dependents) | head -3)"
grep -q 'START axiom' "$t/b/log" && grep -q 'END govet' "$t/b/log" && ok "independent stages still ran (axiom, govet)" || bad "independent stages did not run"
! grep -q 'START verify' "$t/b/log" && ! grep -q 'START gotest' "$t/b/log" && ok "no reader started after the failed build" || bad "a reader ran"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
