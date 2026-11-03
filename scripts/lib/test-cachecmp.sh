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
  printf '{"combined":"%s","sail-driver":"%s","olean:ArmASL.olean":"aa","ir:janus/Janus/Foo.c.o.export":"oo","config:SAIL_SPLIT":"%s","config:SAIL_SPLIT_PARTS":"%s"}\n' "$5" "$5" "${6:-1}" "${7:-48}" > "$1/artifact-hashes.json"
}
check() { # check DESC WANT_RC DIR1 DIR2
  local rc=0; out=$(python3 -I "$cmp_py" compare "$3" "$4" 2>&1) || rc=$?
  if [ "$rc" = "$2" ]; then echo "ok   $1 (rc $rc)"; else echo "FAIL $1: rc $rc, wanted $2: $out"; fail=1; fi
}
mk "$t/a" c1 0 PASS h1; mk "$t/b" c1 0 PASS h1
check "identical runs agree" 0 "$t/a" "$t/b"
sed -i 's/"ir:[^,]*,//' "$t/b/artifact-hashes.json"
check "a run with no emitted C / compiled object hashed is not comparable (fails closed)" 2 "$t/a" "$t/b"
sed -i 's/"ir:[^,]*,//' "$t/a/artifact-hashes.json"
check "neither run hashed one: not comparable either" 2 "$t/a" "$t/b"
mk "$t/a" c1 0 PASS h1; mk "$t/b" c1 0 PASS h1
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
# every ir/*.c and ir/*.c.o.* of every Lake tree is hashed (traces are not: they hold worktree paths), and a changed Janus.* object is P0
w2="$t/w2"; mkdir -p "$w2/.lake/build/ir/Janus" "$w2/JanusASL/.lake/build/ir/ArmASL" "$w2/JanusASL/.lake/build/ir/JanusASL" "$w2/JanusASL/.lake/packages/Sail/.lake/build/ir/Sail" "$w2/JanusASL/.lake/build/lib/lean"
echo c > "$w2/.lake/build/ir/Janus/Foo.c"; echo o > "$w2/.lake/build/ir/Janus/Foo.c.o.export"; echo h > "$w2/.lake/build/ir/Janus/Foo.c.o.export.hash"; echo cin > "$w2/.lake/build/ir/Janus/Foo.c.o.export.cin"; echo '{"p":"/some/worktree"}' > "$w2/.lake/build/ir/Janus/Foo.c.o.export.trace"
echo a > "$w2/JanusASL/.lake/build/ir/ArmASL/Part01.c"; echo ao > "$w2/JanusASL/.lake/build/ir/ArmASL/Part01.c.o.export"
echo j > "$w2/JanusASL/.lake/build/ir/JanusASL/Check.c.o.export"; echo s > "$w2/JanusASL/.lake/packages/Sail/.lake/build/ir/Sail/Attr.c.o.export"; echo '{}' > "$w2/JanusASL/.lake/build/ir/JanusASL/Check.setup.json"
python3 -I "$cmp_py" hashes "$w2" "$t/i1.json"
echo o2 > "$w2/.lake/build/ir/Janus/Foo.c.o.export"; python3 -I "$cmp_py" hashes "$w2" "$t/i2.json"
python3 -I - "$t" <<'PY' && echo "ok   ir: hashes cover the janus, janusasl and Sail trees (C, objects, .hash; not traces/setup.json/the object cache's .cin records) and a changed object changes the digest" || { echo "FAIL ir hashes"; fail=1; }
import json, sys
a = json.load(open(sys.argv[1] + "/i1.json")); b = json.load(open(sys.argv[1] + "/i2.json"))
ks = sorted(k for k in a if k.startswith("ir:"))
want = ["ir:janus/Janus/Foo.c", "ir:janus/Janus/Foo.c.o.export", "ir:janus/Janus/Foo.c.o.export.hash", "ir:janusasl/ArmASL/Part01.c",
        "ir:janusasl/ArmASL/Part01.c.o.export", "ir:janusasl/JanusASL/Check.c.o.export", "ir:sail/Sail/Attr.c.o.export"]
assert ks == want, ks
assert a["combined"] != b["combined"] and a["ir:janus/Janus/Foo.c.o.export"] != b["ir:janus/Janus/Foo.c.o.export"]
PY
mk "$t/a" c1 0 PASS h1; mk "$t/b" c1 0 PASS h1
python3 - "$t" <<'PY'
import json, sys
for d, v in (("a", "x1"), ("b", "x2")):
    p = sys.argv[1] + "/" + d + "/artifact-hashes.json"; j = json.load(open(p)); j["ir:janus/Janus/Foo.c.o.export"] = v; json.dump(j, open(p, "w"))
PY
check "a changed Janus.* object between the cached and the cold run is P0" 1 "$t/a" "$t/b"
m=$(python3 -I "$cmp_py" compare "$t/a" "$t/b"); case "$m" in *"ir:janus/Janus/Foo.c.o.export"*) echo "ok   ... naming it";; *) echo "FAIL report: $m"; fail=1;; esac
mk "$t/a" c1 0 PASS h1; mk "$t/b" c1 0 PASS h1
python3 - "$t" <<'PY'
import json, sys
p = sys.argv[1] + "/b/artifact-hashes.json"; j = json.load(open(p)); j["ir:janus/Janus/Extra.c.o.export"] = "zz"; json.dump(j, open(p, "w"))
PY
check "an object present in one run only is P0" 1 "$t/a" "$t/b"
# a symlinked object is recorded (not skipped) and differs from the regular file of the other run
w3="$t/w3"; cp -a "$w2" "$w3"; rm "$w3/.lake/build/ir/Janus/Foo.c.o.export"; ln -s "$w2/.lake/build/ir/Janus/Foo.c.o.export" "$w3/.lake/build/ir/Janus/Foo.c.o.export"
python3 -I "$cmp_py" hashes "$w2" "$t/s1.json"; python3 -I "$cmp_py" hashes "$w3" "$t/s2.json"
python3 -I - "$t" <<'PY' && echo "ok   a symlinked object is recorded as symlink:<target>, not skipped" || { echo "FAIL symlink recording"; fail=1; }
import json, sys
a = json.load(open(sys.argv[1] + "/s1.json")); b = json.load(open(sys.argv[1] + "/s2.json"))
k = "ir:janus/Janus/Foo.c.o.export"
assert k in b and b[k].startswith("symlink:") and a[k] != b[k] and a["combined"] != b["combined"], (a.get(k), b.get(k))
PY
mk "$t/a" c1 0 PASS h1; mk "$t/b" c1 0 PASS h1
python3 - "$t" <<'PY'
import json, sys
for d, v in (("a", "r1"), ("b", "symlink:/elsewhere/Foo.c.o.export")):
    p = sys.argv[1] + "/" + d + "/artifact-hashes.json"; j = json.load(open(p)); j["ir:janus/Janus/Foo.c.o.export"] = v; json.dump(j, open(p, "w"))
PY
check "a symlinked object in one run (regular in the other) is P0" 1 "$t/a" "$t/b"
mk "$t/a" c1 0 PASS h1; mk "$t/b" c1 0 PASS h1
python3 - "$t" <<'PY'
import json, sys
p = sys.argv[1] + "/b/artifact-hashes.json"; j = json.load(open(p)); j["ir:janus/Janus/Foo.c"] = "cc"; json.dump(j, open(p, "w"))
PY
check "a C file present in one run only is P0" 1 "$t/a" "$t/b"
mk "$t/a" c1 0 PASS h1; mk "$t/b" c1 0 PASS h1
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
