#!/usr/bin/env bash
# Self-test of the cached-vs-cold comparison (scripts/gate-cachecmp.py) with fake gate outputs.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cmp_py="$root/scripts/gate-cachecmp.py"
t=$(mktemp -d "${TMPDIR:-/tmp}/test-cachecmp.XXXXXX"); trap 'rm -rf "$t"' EXIT
fail=0
mk() { # mk DIR COMMIT ASLSTATUS FSQRTSTATUS HASH
  mkdir -p "$1"
  cat > "$1/timeline.jsonl" <<J
{"kind":"gate","commit":"$2","jobs":2}
{"kind":"prebuild","name":"lake build","rc":0}
{"kind":"stage","name":"asl-build","rc":$3}
{"kind":"item","pool":"gate","id":"rtasl-fsqrt","status":"$4","wall":10}
{"kind":"item","pool":"gate","id":"gotest","status":"PASS","wall":10}
J
  printf '{"combined":"%s","sail-driver":"%s","olean:ArmASL.olean":"aa"}\n' "$5" "$5" > "$1/artifact-hashes.json"
}
check() { # check DESC WANT_RC DIR1 DIR2
  local rc=0; out=$(python3 -I "$cmp_py" compare "$3" "$4" 2>&1) || rc=$?
  if [ "$rc" = "$2" ]; then echo "ok   $1 (rc $rc)"; else echo "FAIL $1: rc $rc, wanted $2: $out"; fail=1; fi
}
mk "$t/a" c1 0 PASS h1; mk "$t/b" c1 0 PASS h1
check "identical runs agree" 0 "$t/a" "$t/b"
mk "$t/b" c1 0 FAIL h1
check "a lane that passes cached and fails cold is P0" 1 "$t/a" "$t/b"
m=$(python3 -I "$cmp_py" compare "$t/a" "$t/b"); case "$m" in *"P0 CACHE BUG"*) true ;; *) false ;; esac && echo "ok   the report says P0 CACHE BUG" || { echo "FAIL no P0 message"; fail=1; }
mk "$t/b" c1 1 PASS h1
check "a stage that fails cold only is P0" 1 "$t/a" "$t/b"
mk "$t/b" c1 0 PASS h2
check "a different artifact hash is P0" 1 "$t/a" "$t/b"
mk "$t/b" c1 0 PASS h1; sed -i '/gotest/d' "$t/b/timeline.jsonl"
check "an item missing from one run is P0" 1 "$t/a" "$t/b"
mk "$t/b" c2 0 PASS h1
check "different commits are not comparable" 2 "$t/a" "$t/b"
mk "$t/b" c1 0 PASS h1; rm "$t/b/artifact-hashes.json"
check "missing artifact hashes cannot be compared" 2 "$t/a" "$t/b"
mk "$t/b" c1 0 PASS h1; echo "{bad" >> "$t/b/timeline.jsonl"
check "a malformed timeline cannot be compared" 2 "$t/a" "$t/b"
# hashes on a fake worktree
mkdir -p "$t/w/JanusASL/.lake/build/lib/lean" "$t/w/oracle-sail/target/release"; echo o > "$t/w/JanusASL/.lake/build/lib/lean/ArmASL.olean"; echo d > "$t/w/oracle-sail/target/release/janus-oracle-sail"
python3 -I "$cmp_py" hashes "$t/w" "$t/h1.json"; echo p >> "$t/w/oracle-sail/target/release/janus-oracle-sail"; python3 -I "$cmp_py" hashes "$t/w" "$t/h2.json"
python3 -I - "$t" <<'PY' && echo "ok   hashes: records oleans and the driver; a changed driver changes the combined digest" || { echo "FAIL hashes"; fail=1; }
import json, sys
a, b = (json.load(open(sys.argv[1] + "/h%d.json" % i)) for i in (1, 2))
assert "olean:ArmASL.olean" in a and "sail-driver" in a and a["combined"] != b["combined"] and a["olean:ArmASL.olean"] == b["olean:ArmASL.olean"]
PY
[ "$fail" = 0 ] && echo "cachecmp tests: all passed" || { echo "cachecmp tests: FAILED"; exit 1; }
