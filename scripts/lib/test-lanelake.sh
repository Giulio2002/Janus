#!/usr/bin/env bash
# Self-test of scripts/lib/lanelake/lake: two lanes share one isolated tree; a fake `lake` (JANUS_REAL_LAKE) records
# when each call starts and ends, and a call "build" REWRITES a shared file (as a dependency re-resolution that
# deletes packages/Sail does) while a call "env" reads it. Run concurrently, no rewrite may overlap any other lake
# call of the tree, two `env` calls may overlap each other, and a call outside the tree is not serialised.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-lanelake.XXXXXX")"; trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
mkdir -p "$t/tree/JanusASL" "$t/other"
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
export FAKE_T="$t" JANUS_REAL_LAKE="$t/reallake" JANUS_LANE_TREE="$t/tree" JANUS_LANE_LAKE_LOCK="$t/tree/.lock"
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
( cd "$t/tree" && "$L" build ) & sleep 0.15
s=$(date +%s.%N); ( cd "$t/other" && "$L" other ); e=$(date +%s.%N)
wait
awk -v s="$s" -v e="$e" 'BEGIN { exit !(e - s < 0.45) }' && ok "a call outside the tree passes through" || bad "outside call waited"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
