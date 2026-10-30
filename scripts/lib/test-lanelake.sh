#!/usr/bin/env bash
# Self-test of scripts/lib/lanelake/lake: two lanes share one isolated tree; a fake `lake` (JANUS_REAL_LAKE) records
# when each call starts and ends, and a call "build" REWRITES a shared file (as a dependency re-resolution that
# deletes packages/Sail does) while a call "env" reads it. Run concurrently, no rewrite may overlap any other lake
# call of the tree, two `env` calls may overlap each other, and a call outside the tree is not serialised.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-lanelake.XXXXXX")"; trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
mkdir -p "$t/tree/JanusASL/.lake" "$t/other"; : > "$t/tree/JanusASL/lakefile.toml"; LK="$t/tree/JanusASL/.lake/.gate-lake.lock"
cat > "$t/reallake" <<'EOS'
#!/usr/bin/env bash
# fake lake: logs "START/END kind pid time"; build rewrites $T/tree/state (non-atomically, slowly), env reads it
T="${FAKE_T:?}"
kind="${1:-}"
echo "START $kind $$ $(date +%s.%N)" >> "$T/log"
case "$kind" in
  build) echo partial > "$T/tree/state"; sleep 0.6; echo complete > "$T/tree/state" ;;
  env) s=$(cat "$T/tree/state" 2>/dev/null); sleep 0.5; [ "$s" = complete ] || echo "READ-DURING-REWRITE $s" >> "$T/log" ;;
  *) sleep 0.3 ;;
esac
echo "END $kind $$ $(date +%s.%N)" >> "$T/log"
EOS
chmod +x "$t/reallake"; echo complete > "$t/tree/state"
export FAKE_T="$t" JANUS_REAL_LAKE="$t/reallake" JANUS_LANE_TREE="$t/tree" JANUS_LANE_LAKE_LOCK=1
L="$here/lanelake/lake"
lane() { ( cd "$t/tree/JanusASL" && "$L" "$@" ); }
# lane A: a rebuild; lane B: two read-only calls; lane C: another rebuild
lane build & lane env & lane env & lane build & sleep 0.1; lane env &
wait
grep -q READ-DURING-REWRITE "$t/log" && bad "a read overlapped a rewrite: $(grep READ "$t/log" | head -1)" || ok "no read during a rewrite"
# no build interval overlaps any other interval
python3 -I - "$t/log" <<'PY' && ok "builds never overlap another lake call" || bad "overlap found"
import sys
ev={}
for l in open(sys.argv[1]):
    w=l.split()
    if w[0] in("START","END"): ev.setdefault(w[2],{})[w[0]]=(w[1],float(w[3]))
iv=[(d["START"][0],d["START"][1],d["END"][1]) for d in ev.values()]
bad=[(a,b) for i,a in enumerate(iv) for b in iv[i+1:] if "build" in (a[0],b[0]) and a[1]<b[2] and b[1]<a[2]]
sys.exit(1 if bad else 0)
PY
python3 -I - "$t/log" <<'PY' && ok "read-only calls overlap each other (not serialised)" || bad "env calls were serialised"
import sys
ev={}
for l in open(sys.argv[1]):
    w=l.split()
    if w[0] in("START","END"): ev.setdefault(w[2],{})[w[0]]=(w[1],float(w[3]))
iv=[(d["START"][1],d["END"][1]) for d in ev.values() if d["START"][0]=="env"]
sys.exit(0 if any(a[0]<b[1] and b[0]<a[1] for i,a in enumerate(iv) for b in iv[i+1:]) else 1)
PY
# a call outside the tree is not locked: it runs while another holds the lock
: > "$t/log"
( cd "$t/tree/JanusASL" && "$L" build ) & sleep 0.15
s=$(date +%s.%N); ( cd "$t/other" && "$L" other ); e=$(date +%s.%N)
wait
awk -v s="$s" -v e="$e" 'BEGIN { exit !(e - s < 0.45) }' && ok "a call outside the tree passes through" || bad "outside call waited"
# the lock file: created 0600, a symlink or a foreign/linked file is refused (and never followed)
: > "$t/log"; rm -f "$LK"
( cd "$t/tree/JanusASL" && "$L" build ) && [ "$(stat -c %a "$LK")" = 600 ] && ok "lock file created with mode 0600" || bad "lock mode $(stat -c %a "$LK" 2>&1)"
: > "$t/log"; rm -f "$LK"; echo precious > "$t/victim"; ln -s "$t/victim" "$LK"
out=$( cd "$t/tree/JanusASL" && "$L" build 2>&1 ); rc=$?
[ "$rc" != 0 ] && grep -q 'symlink is refused' <<<"$out" && [ "$(cat "$t/victim")" = precious ] && [ ! -s "$t/log" ] && ok "a symlinked lock file is refused, not followed, lake not run" || bad "symlink: rc=$rc $out"
rm -f "$LK"; ln "$t/victim" "$LK"
out=$( cd "$t/tree/JanusASL" && "$L" build 2>&1 ); rc=$?
[ "$rc" != 0 ] && grep -q 'one link' <<<"$out" && ok "a hard-linked lock file is refused" || bad "hardlink: rc=$rc $out"
rm -f "$LK"; mkdir "$LK"
out=$( cd "$t/tree/JanusASL" && "$L" build 2>&1 ); rc=$?
[ "$rc" != 0 ] && ok "a directory as lock file is refused" || bad "directory accepted"
rmdir "$LK"

# ---- a janus that holds the framework lock EXCLUSIVELY while it runs `lake build` in the tree root (framework.go build):
# the wrapper must not wait for a lock its own parent holds (it was a self-deadlock: janus holds <tree>/.lake/janus-framework.lock,
# its child lanelake/lock wanted the same lock exclusively), and a root-package lake call racing such a janus must not form a
# lock-order cycle (janus: fw -> root package; wrapper: fw -> root package).
rm -rf "$t/rt"; mkdir -p "$t/rt/.lake"; : > "$t/rt/lakefile.toml"; : > "$t/log"
cat > "$t/fakejanus" <<'EOS'
#!/usr/bin/env bash
# fake janus: exclusive framework lock, then `lake build` in the tree root as its child, marker set like leanRunner does
exec 9>>"$FAKE_RT/.lake/janus-framework.lock"; flock -x 9
export JANUS_FRAMEWORK_LOCK_HELD_X="$FAKE_RT/.lake/janus-framework.lock"
cd "$FAKE_RT" && "$FAKE_L" build
EOS
chmod +x "$t/fakejanus"
export FAKE_RT="$t/rt" FAKE_L="$L"
saveT=$JANUS_LANE_TREE; export JANUS_LANE_TREE="$t/rt"
timeout 20 "$t/fakejanus" > "$t/fj.out" 2>&1; rc=$?
[ "$rc" = 0 ] && grep -q '^START build' "$t/log" && ok "janus holding the framework lock exclusively can run lake build through the wrapper (no self-deadlock)" || bad "self-deadlock: rc=$rc (124 = it hung) $(cat "$t/fj.out")"
# the same without the marker would wait for its own parent: the wrapper still takes the lock (guarantee kept) -> times out
sed -i 's/^export JANUS_FRAMEWORK_LOCK_HELD_X=.*$/:/' "$t/fakejanus"; : > "$t/log"
timeout 3 "$t/fakejanus" > /dev/null 2>&1; rc=$?
[ "$rc" = 124 ] && [ ! -s "$t/log" ] && ok "without janus' claim the wrapper still takes the framework lock (it waits: lock not weakened)" || bad "unclaimed hold not respected: rc=$rc"
# a claim naming another file is ignored
sed -i 's/^:$/export JANUS_FRAMEWORK_LOCK_HELD_X=\/nonexistent\/janus-framework.lock/' "$t/fakejanus"; : > "$t/log"
timeout 3 "$t/fakejanus" > /dev/null 2>&1; rc=$?
[ "$rc" = 124 ] && ok "a claim for another lock file does not skip the framework lock" || bad "foreign claim honoured: rc=$rc"
# lock-order cycle: wrapper root-package calls and the fake janus (fw -> root pkg) racing 12 times each must all finish
sed -i 's/^export JANUS_FRAMEWORK_LOCK_HELD_X=.*$/export JANUS_FRAMEWORK_LOCK_HELD_X="$FAKE_RT\/.lake\/janus-framework.lock"/' "$t/fakejanus"; : > "$t/log"
pids=(); for i in $(seq 12); do ( cd "$t/rt" && timeout 60 "$L" build ) & pids+=($!); timeout 60 "$t/fakejanus" > /dev/null 2>&1 & pids+=($!); done
bad_n=0; for p in "${pids[@]}"; do wait "$p" || bad_n=$((bad_n + 1)); done
[ "$bad_n" = 0 ] && ok "24 racing root-package lake calls and janus builds all finish (no lock-order cycle)" || bad "$bad_n of 24 failed or hung"
export JANUS_LANE_TREE=$saveT
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
