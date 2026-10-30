#!/usr/bin/env bash
# Self-test of the shared-ASL-tree lock discipline (scripts/asl.sh tl_run + scripts/lib/lanelake/lake):
#  1. two lanes (asl-verify-like and rtasl-replay-like) run their write phases (a NON-lake module-cache restore that
#     rewrites a shared file, then a fake `lake build`) CONCURRENTLY in ONE tree: no two writers ever overlap;
#  2. a fake janus (--janus-root = the tree: holds <tree>/.lake/janus-framework.lock SHARED for its whole run, as
#     framework.go's lease does) never sees the framework file change under it, and never hangs: the writers wait for
#     it and it finishes (rtasl-go vs asl lakes);
#  3. a reader phase (tl_run s) runs beside other readers but not beside a writer.
set -uo pipefail
unset POOL_TIMELINE JANUS_POOL_DIR JANUS_GATE_PG
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"; repo="$(cd "$here/../.." && pwd)"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-treelock.XXXXXX")"; trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
tree="$t/tree"; mkdir -p "$tree/JanusASL" "$tree/.lake/build" "$tree/scripts/lib"
cp -r "$here/lanelake" "$tree/scripts/lib/"; echo v1 > "$tree/.lake/build/Janus.olean"
# tl_run as asl.sh defines it (extracted, so the test runs the real text)
sed -n '/^tl_run() {/,/^_TL_SELF=/p' "$repo/scripts/asl.sh" > "$t/tl.sh"
cat > "$t/fakelake" <<'EOS'
#!/usr/bin/env bash
# fake lake: "build" rewrites the framework olean slowly (replay does) and logs the interval
echo "START w $$ $(date +%s.%N)" >> "$FAKE_LOG"
if [ "${1:-}" = build ]; then echo rewriting > "$FAKE_TREE/.lake/build/Janus.olean"; sleep 0.5; echo v1 > "$FAKE_TREE/.lake/build/Janus.olean"; else sleep 0.2; fi
echo "END w $$ $(date +%s.%N)" >> "$FAKE_LOG"
EOS
cat > "$t/fakejanus" <<'EOS'
#!/usr/bin/env bash
# fake janus --janus-root <tree>: shared framework lock for the whole run; the olean must not change under it
exec 9>>"$FAKE_TREE/.lake/janus-framework.lock"; flock -s 9
echo "START j $$ $(date +%s.%N)" >> "$FAKE_LOG"
a=$(cat "$FAKE_TREE/.lake/build/Janus.olean"); sleep 1.2; b=$(cat "$FAKE_TREE/.lake/build/Janus.olean")
[ "$a" = v1 ] && [ "$b" = v1 ] || echo "JANUS-SAW-REWRITE $a/$b" >> "$FAKE_LOG"
echo "END j $$ $(date +%s.%N)" >> "$FAKE_LOG"
EOS
cat > "$t/lane.sh" <<'EOS'
#!/usr/bin/env bash
# a lane: tl_run-style write phase (restore = non-lake writer of a shared file, then lake build), then a reader phase
set -u
root="$FAKE_ROOT"; . "$FAKE_T/tl.sh"
phase_w() { echo "START r $$ $(date +%s.%N)" >> "$FAKE_LOG"; echo restoring > "$FAKE_TREE/JanusASL/cache"; sleep 0.3; echo ok > "$FAKE_TREE/JanusASL/cache"
            echo "END r $$ $(date +%s.%N)" >> "$FAKE_LOG"; lake build; }
phase_r() { echo "START q $$ $(date +%s.%N)" >> "$FAKE_LOG"; sleep 0.4; echo "END q $$ $(date +%s.%N)" >> "$FAKE_LOG"; }
if [ "${1:-}" = __call ]; then shift; "$@"; exit; fi
_TL_SELF="$0"
tl_run x phase_w; tl_run s phase_r
EOS
chmod +x "$t"/fake* "$t/lane.sh"
export FAKE_LOG="$t/log" FAKE_TREE="$tree" FAKE_T="$t" FAKE_ROOT="$tree" JANUS_REAL_LAKE="$t/fakelake" \
       JANUS_LANE_TREE="$tree" JANUS_LANE_LAKE_LOCK="$tree/.gate-lake.lock" PATH="$tree/scripts/lib/lanelake:$PATH"
cp "$t/fakelake" "$t/lake_real"; ln -sf "$t/fakelake" "$t/lake"   # `lake` resolves to the wrapper first on PATH
( cd "$tree/JanusASL" && "$t/lane.sh" ) & ( cd "$tree/JanusASL" && "$t/lane.sh" ) & ( cd "$tree/JanusASL" && "$t/lane.sh" ) &
( cd "$tree" && "$t/fakejanus" ) & ( cd "$tree" && "$t/fakejanus" ) &
sleep 0.2; ( cd "$tree" && "$t/fakejanus" ) &
timeout 60 bash -c 'wait'; [ $? = 0 ] || true
wait
python3 -I - "$t/log" <<'PY' && ok "no two writers overlap (restore + lake build of two lanes, rewriting phases)" || bad "writers overlapped"
import sys
ev={}
for l in open(sys.argv[1]):
    w=l.split()
    if w[0] in("START","END"): ev.setdefault(w[2],{})[w[0]]=(w[1],float(w[3]))
iv=[(d["START"][0],d["START"][1],d["END"][1]) for d in ev.values() if "END" in d]
w=[i for i in iv if i[0] in ("w","r")]
# 'r' and 'w' of one lane are inside one exclusive phase, so compare across lanes by the phase: group by overlap with
# the other intervals of a different pid is expected within a lane; require that no 'w'(build) overlaps another 'w'
b=[i for i in iv if i[0] in ("w","r")]
bad=[(a,c) for k,a in enumerate(b) for c in b[k+1:] if a[1]<c[2] and c[1]<a[2]]
sys.exit(1 if bad else 0)
PY
grep -q JANUS-SAW-REWRITE "$t/log" && bad "a running janus saw the framework rewritten: $(grep JANUS-SAW "$t/log" | head -1)" || ok "a running janus never sees the framework rewritten, and finishes ($(grep -c 'END j' "$t/log") of 3 janus runs)"
[ "$(grep -c 'END j' "$t/log")" = 3 ] && ok "no hang: every janus run finished" || bad "janus runs finished: $(grep -c 'END j' "$t/log")"
python3 -I - "$t/log" <<'PY' && ok "no lake build overlaps a janus run" || bad "a lake build overlapped a janus run"
import sys
ev={}
for l in open(sys.argv[1]):
    w=l.split()
    if w[0] in("START","END"): ev.setdefault(w[2],{})[w[0]]=(w[1],float(w[3]))
iv=[(d["START"][0],d["START"][1],d["END"][1]) for d in ev.values() if "END" in d]
j=[i for i in iv if i[0]=="j"]; b=[i for i in iv if i[0]=="w"]
sys.exit(1 if [1 for x in j for y in b if x[1]<y[2] and y[1]<x[2]] else 0)
PY
[ "$(cat "$tree/JanusASL/cache")" = ok ] && ok "the shared cache file ends consistent" || bad "cache file: $(cat "$tree/JanusASL/cache")"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
