#!/usr/bin/env bash
# Self-test of the cached-vs-cold comparison (scripts/gate-cachecmp.py) with fake gate outputs.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cmp_py="$root/scripts/gate-cachecmp.py"
t=$(mktemp -d "${TMPDIR:-/tmp}/test-cachecmp.XXXXXX"); trap 'rm -rf "$t"' EXIT
fail=0
mk() { # mk DIR COMMIT ASLSTATUS FSQRTSTATUS HASH [SAIL_SPLIT [PARTS]]
  mkdir -p "$1"
  cat > "$1/timeline.jsonl" <<J
{"kind":"gate","commit":"$2","jobs":2}
{"kind":"prebuild","name":"lake build","rc":0}
{"kind":"stage","name":"asl-build","rc":$3}
{"kind":"item","pool":"gate","id":"rtasl-fsqrt","status":"$4","wall":10}
{"kind":"item","pool":"gate","id":"gotest","status":"PASS","wall":10}
J
  printf '{"combined":"%s","sail-driver":"%s","olean:ArmASL.olean":"aa","config:SAIL_SPLIT":"%s","config:SAIL_SPLIT_PARTS":"%s"}\n' "$5" "$5" "${6:-1}" "${7:-48}" > "$1/artifact-hashes.json"
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
# a SAIL_SPLIT / parts-count mismatch is a configuration mismatch (rc 2, never "P0 CACHE BUG"), even when the drivers differ
mk "$t/b" c1 0 PASS h2 0
check "a SAIL_SPLIT mismatch is not comparable" 2 "$t/a" "$t/b"
m=$(python3 -I "$cmp_py" compare "$t/a" "$t/b"); case "$m" in *"CONFIGURATION MISMATCH"*SAIL_SPLIT*) true ;; *) false ;; esac && case "$m" in *"P0 CACHE BUG"*) false ;; *) true ;; esac && echo "ok   the report says CONFIGURATION MISMATCH, not P0 CACHE BUG" || { echo "FAIL config message: $m"; fail=1; }
mk "$t/b" c1 0 PASS h1 1 24
check "a parts-count mismatch is not comparable" 2 "$t/a" "$t/b"
mk "$t/b" c1 0 PASS h1 0
check "SAIL_SPLIT mismatch with identical hashes still fails closed" 2 "$t/a" "$t/b"
mk "$t/a" c1 0 PASS h2 0 48; mk "$t/b" c1 0 PASS h2 0 48
check "both runs with the same explicit SAIL_SPLIT=0 agree" 0 "$t/a" "$t/b"
mk "$t/b" c1 0 PASS h3 0 48
check "same configuration, different driver hash is still P0" 1 "$t/a" "$t/b"
mk "$t/a" c1 0 PASS h1; mk "$t/b" c1 0 PASS h1; sed -i 's/"config:SAIL_SPLIT":"1",//' "$t/b/artifact-hashes.json"
check "an unrecorded SAIL_SPLIT (older gate) fails closed" 2 "$t/a" "$t/b"
mk "$t/a" c1 0 PASS h1; mk "$t/b" c1 0 PASS h1
# hashes on a fake worktree
mkdir -p "$t/w/JanusASL/.lake/build/lib/lean" "$t/w/oracle-sail/target/release"; echo o > "$t/w/JanusASL/.lake/build/lib/lean/ArmASL.olean"; echo d > "$t/w/oracle-sail/target/release/janus-oracle-sail"
python3 -I "$cmp_py" hashes "$t/w" "$t/h1.json"; echo p >> "$t/w/oracle-sail/target/release/janus-oracle-sail"; python3 -I "$cmp_py" hashes "$t/w" "$t/h2.json"
mkdir -p "$t/w/scripts"; printf 'SAIL_SPLIT_PARTS=48\n' > "$t/w/scripts/oracle-sail.sh"
python3 -I "$cmp_py" hashes "$t/w" "$t/h3.json"; SAIL_SPLIT=0 python3 -I "$cmp_py" hashes "$t/w" "$t/h4.json"
python3 -I - "$t" <<'PY' && echo "ok   hashes records SAIL_SPLIT and the parts count, outside the combined digest" || { echo "FAIL hashes config"; fail=1; }
import json, sys
a, b = (json.load(open(sys.argv[1] + "/h%d.json" % i)) for i in (3, 4))
assert a["config:SAIL_SPLIT"] == "1" and b["config:SAIL_SPLIT"] == "0" and a["config:SAIL_SPLIT_PARTS"] == "48", (a, b)
assert a["combined"] == b["combined"]
PY
python3 -I - "$t" <<'PY' && echo "ok   hashes: records oleans and the driver; a changed driver changes the combined digest" || { echo "FAIL hashes"; fail=1; }
import json, sys
a, b = (json.load(open(sys.argv[1] + "/h%d.json" % i)) for i in (1, 2))
assert "olean:ArmASL.olean" in a and "sail-driver" in a and a["combined"] != b["combined"] and a["olean:ArmASL.olean"] == b["olean:ArmASL.olean"]
PY
[ "$fail" = 0 ] && echo "cachecmp tests: all passed" || { echo "cachecmp tests: FAILED"; exit 1; }
