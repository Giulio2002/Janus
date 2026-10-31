#!/usr/bin/env bash
# Self-test of scripts/lib/restamp.py (the framework stamp's pins follow ONLY cache-restored, verified files) and of the
# `--record` output of JanusASL/tools/asl_mod_cache.py restore.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
t="$(mktemp -d "${TMPDIR:-/var/tmp}/test-restamp.XXXXXX")"; trap 'rm -rf "$t"' EXIT
export JANUS_CACHE_KEY_DIR="$t/key"; mkdir -m 700 "$t/key"   # a private HMAC key for the records
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
sha() { sha256sum "$1" | cut -d' ' -f1; }
# sign TREE OUT [PATH=SHA ...]: write a signed record (what `asl_mod_cache.py restore --record` writes); with no args from stdin JSON
sign() { python3 -I - "$here/bcache.py" "$@" <<'PY'
import importlib.util, json, sys
spec = importlib.util.spec_from_file_location("bcache", sys.argv[1]); bc = importlib.util.module_from_spec(spec); spec.loader.exec_module(bc)
tree, out = sys.argv[2], sys.argv[3]
files = dict(a.rsplit("=", 1) for a in sys.argv[4:])
json.dump({"files": files, "mac": bc.record_mac(tree, files)}, open(out, "w"))
PY
}
rs() { python3 -I "$here/restamp.py" "$@"; }
mk() { # DIR: a tree with a stamp over three framework modules A (restored), B (not restored, modified), C (untouched)
  local d=$1; mkdir -p "$d/.lake/build/lib/lean/Janus"
  for m in A B C; do echo "orig $m" > "$d/.lake/build/lib/lean/Janus/$m.olean"; done
  python3 -I - "$d" <<'PY'
import hashlib, json, sys
d = sys.argv[1]; h = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()
pins = {"Janus/%s.olean" % m: h("%s/.lake/build/lib/lean/Janus/%s.olean" % (d, m)) for m in "ABC"}
json.dump({"sha256": "S", "manifest": "M", "targets": ["Janus"], "pins": pins, "auditExe": "E"}, open(d + "/.lake/janus-framework.ready", "w"))
PY
}
pin() { python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["pins"][sys.argv[2]])' "$1/.lake/janus-framework.ready" "$2"; }
mk "$t/a"; L="$t/a/.lake/build/lib/lean/Janus"
oldA=$(pin "$t/a" Janus/A.olean); oldB=$(pin "$t/a" Janus/B.olean)
echo "restored A" > "$L/A.olean"; echo "evil B" > "$L/B.olean"
sign "$t/a" "$t/rec.json" "$t/a/.lake/build/lib/lean/Janus/A.olean=$(sha "$L/A.olean")"
python3 -I "$here/restamp.py" "$t/a" "$t/rec.json" > "$t/out" 2>&1
[ "$(pin "$t/a" Janus/A.olean)" = "$(sha "$L/A.olean")" ] && [ "$(pin "$t/a" Janus/A.olean)" != "$oldA" ] && ok "a file restored from a verified cache entry gets its pin moved" || bad "restored pin not moved"
[ "$(pin "$t/a" Janus/B.olean)" = "$oldB" ] && ok "a modified file that the cache did not restore keeps its old pin (janus will reject/rebuild it)" || bad "unrestored modified file was re-pinned"
python3 -I -c 'import json,sys; s=json.load(open(sys.argv[1])); assert (s["sha256"],s["manifest"],s["targets"],s["auditExe"])==("S","M",["Janus"],"E")' "$t/a/.lake/janus-framework.ready" && ok "sources hash, manifest, targets and the auditor's SHA-256 are untouched" || bad "stamp header changed"
# the record names A but A is changed again after the restore: no pin follows
mk "$t/b"; echo "restored A" > "$t/b/.lake/build/lib/lean/Janus/A.olean"
sign "$t/b" "$t/recb.json" "$t/b/.lake/build/lib/lean/Janus/A.olean=$(sha "$t/b/.lake/build/lib/lean/Janus/A.olean")"
oldA=$(pin "$t/b" Janus/A.olean); echo "tampered after the restore" > "$t/b/.lake/build/lib/lean/Janus/A.olean"
python3 -I "$here/restamp.py" "$t/b" "$t/recb.json" > /dev/null 2>&1
[ "$(pin "$t/b" Janus/A.olean)" = "$oldA" ] && ok "a restored file changed after the restore is not re-pinned" || bad "tampered-after-restore file was re-pinned"
# a symlink in place of a module file is never followed
mk "$t/c"; rm "$t/c/.lake/build/lib/lean/Janus/A.olean"; echo "x" > "$t/x"; ln -s "$t/x" "$t/c/.lake/build/lib/lean/Janus/A.olean"
sign "$t/c" "$t/recc.json" "$t/c/.lake/build/lib/lean/Janus/A.olean=$(sha "$t/x")"
oldA=$(pin "$t/c" Janus/A.olean); python3 -I "$here/restamp.py" "$t/c" "$t/recc.json" > /dev/null 2>&1
[ "$(pin "$t/c" Janus/A.olean)" = "$oldA" ] && ok "a symbolic link in place of a module file is not re-pinned" || bad "symlink re-pinned"
# no stamp / no record: nothing happens, rc 0
python3 -I "$here/restamp.py" "$t/nonexistent" "$t/rec.json" > /dev/null 2>&1 && ok "no stamp: nothing to do, rc 0" || bad "no stamp rc"
mk "$t/d"; echo changed > "$t/d/.lake/build/lib/lean/Janus/A.olean"; before=$(cat "$t/d/.lake/janus-framework.ready")
python3 -I "$here/restamp.py" "$t/d" "$t/missing-record.json" > /dev/null 2>&1; [ "$(cat "$t/d/.lake/janus-framework.ready")" = "$before" ] && ok "no record: the stamp is left as it is" || bad "stamp changed without a record"

# ---- authenticity of the record (HMAC) ----
unchanged() { # TREE: the stamp equals its pre-restamp pins (A and B,C still the original pins)
  [ "$(pin "$1" Janus/A.olean)" = "$2" ]; }
mk "$t/e"; E="$t/e/.lake/build/lib/lean/Janus"; oldA=$(pin "$t/e" Janus/A.olean); echo "restored A" > "$E/A.olean"
shaA=$(sha "$E/A.olean"); keyA="$t/e/.lake/build/lib/lean/Janus/A.olean"
# a forged record with no MAC (the old plain format and the new envelope without a tag)
echo "{\"$keyA\": \"$shaA\"}" > "$t/forged.json"
rs "$t/e" "$t/forged.json" > "$t/out" 2>&1; rc=$?
[ $rc -ne 0 ] && unchanged "$t/e" "$oldA" && ok "a record without a MAC is refused (rc $rc), nothing pinned" || bad "unsigned record accepted"
echo "{\"files\": {\"$keyA\": \"$shaA\"}}" > "$t/forged2.json"
rs "$t/e" "$t/forged2.json" > "$t/out" 2>&1; rc=$?
[ $rc -ne 0 ] && unchanged "$t/e" "$oldA" && ok "an envelope without a MAC is refused" || bad "envelope without MAC accepted"
# wrong MAC
echo "{\"files\": {\"$keyA\": \"$shaA\"}, \"mac\": \"$(printf '0%.0s' $(seq 64))\"}" > "$t/forged3.json"
rs "$t/e" "$t/forged3.json" > "$t/out" 2>&1; rc=$?
[ $rc -ne 0 ] && unchanged "$t/e" "$oldA" && ok "a record with a wrong MAC is refused" || bad "wrong MAC accepted"
# a MAC made under another key
mkdir -m 700 "$t/key2"; JANUS_CACHE_KEY_DIR="$t/key2" sign "$t/e" "$t/other.json" "$keyA=$shaA"
rs "$t/e" "$t/other.json" > "$t/out" 2>&1; rc=$?
[ $rc -ne 0 ] && unchanged "$t/e" "$oldA" && ok "a record signed with another key is refused" || bad "foreign-key record accepted"
# a record signed for another tree
sign "$t/a" "$t/othertree.json" "$keyA=$shaA"
rs "$t/e" "$t/othertree.json" > "$t/out" 2>&1; rc=$?
[ $rc -ne 0 ] && unchanged "$t/e" "$oldA" && ok "a record signed for another tree is refused" || bad "cross-tree record accepted"
# edited after the MAC
sign "$t/e" "$t/edit.json" "$keyA=$(printf 'f%.0s' $(seq 64))"
python3 -I - "$t/edit.json" "$shaA" <<'PY'
import json, sys
d = json.load(open(sys.argv[1])); k = next(iter(d["files"])); d["files"][k] = sys.argv[2]; json.dump(d, open(sys.argv[1], "w"))
PY
rs "$t/e" "$t/edit.json" > "$t/out" 2>&1; rc=$?
[ $rc -ne 0 ] && unchanged "$t/e" "$oldA" && ok "a record edited after it was signed is refused" || bad "edited record accepted"
# the genuine record still works
sign "$t/e" "$t/good.json" "$keyA=$shaA"
rs "$t/e" "$t/good.json" > "$t/out" 2>&1 && [ "$(pin "$t/e" Janus/A.olean)" = "$shaA" ] && ok "the genuine signed record re-pins" || bad "genuine record failed"
# a symlinked record file is not followed
mk "$t/f"; F="$t/f/.lake/build/lib/lean/Janus"; echo "restored A" > "$F/A.olean"; oldA=$(pin "$t/f" Janus/A.olean)
sign "$t/f" "$t/realrec.json" "$t/f/.lake/build/lib/lean/Janus/A.olean=$shaA"; ln -s "$t/realrec.json" "$t/linkrec.json"
rs "$t/f" "$t/linkrec.json" > "$t/out" 2>&1; rc=$?
[ $rc -ne 0 ] && unchanged "$t/f" "$oldA" && ok "a symlinked record file is refused" || bad "symlinked record followed"
# ---- path hygiene ----
# a symlinked parent directory component (Janus -> elsewhere holding an identical-content restored A)
mk "$t/g"; G="$t/g/.lake/build/lib/lean"; oldA=$(pin "$t/g" Janus/A.olean)
mkdir "$t/real"; echo "restored A" > "$t/real/A.olean"; cp "$G/Janus/B.olean" "$G/Janus/C.olean" "$t/real/"
rm -r "$G/Janus"; ln -s "$t/real" "$G/Janus"
sign "$t/g" "$t/recg.json" "$G/Janus/A.olean=$shaA" "$t/real/A.olean=$shaA"
rs "$t/g" "$t/recg.json" > "$t/out" 2>&1
[ "$(pin "$t/g" Janus/A.olean)" = "$oldA" ] && ok "a symbolic link as a parent directory component is not followed" || bad "symlinked parent followed"
# a symlinked .lake
mk "$t/h"; oldA=$(pin "$t/h" Janus/A.olean); echo "restored A" > "$t/h/.lake/build/lib/lean/Janus/A.olean"
mv "$t/h/.lake" "$t/h-lake"; ln -s "$t/h-lake" "$t/h/.lake"
sign "$t/h" "$t/rech.json" "$t/h/.lake/build/lib/lean/Janus/A.olean=$shaA"
rs "$t/h" "$t/rech.json" > "$t/out" 2>&1
[ "$(pin "$t/h" Janus/A.olean)" = "$oldA" ] && ok "a symbolic link as .lake is not followed" || bad "symlinked .lake followed"
# '..' in a record path, and a path outside the tree
mk "$t/i"; I="$t/i/.lake/build/lib/lean"; oldA=$(pin "$t/i" Janus/A.olean); echo "restored A" > "$I/Janus/A.olean"
sign "$t/i" "$t/reci.json" "$I/Janus/../Janus/A.olean=$shaA" "$t/i/.lake/build/lib/lean/Janus/./A.olean=$shaA" "$t/elsewhere/A.olean=$shaA"
rs "$t/i" "$t/reci.json" > "$t/out" 2>&1
[ "$(pin "$t/i" Janus/A.olean)" = "$oldA" ] && ok "'..', '.' and outside-the-tree record paths never match" || bad "dotdot record path accepted"
# '..' in a stamp pin
mk "$t/j"; python3 -I - "$t/j" <<'PY'
import json, sys
p = sys.argv[1] + "/.lake/janus-framework.ready"; s = json.load(open(p)); s["pins"]["Janus/../Janus/A.olean"] = "0" * 64; json.dump(s, open(p, "w"))
PY
echo "restored A" > "$t/j/.lake/build/lib/lean/Janus/A.olean"
sign "$t/j" "$t/recj.json" "$t/j/.lake/build/lib/lean/Janus/../Janus/A.olean=$shaA"
rs "$t/j" "$t/recj.json" > "$t/out" 2>&1
python3 -I -c 'import json,sys; assert json.load(open(sys.argv[1]))["pins"]["Janus/../Janus/A.olean"]=="0"*64' "$t/j/.lake/janus-framework.ready" && ok "a '..' pin path is refused" || bad "dotdot pin followed"
# ---- the record is written safely by `asl_mod_cache.py restore --record` ----
grep -q 'O_EXCL | os.O_NOFOLLOW' "$here/../../JanusASL/tools/asl_mod_cache.py" && ok "restore --record opens its temp file O_CREAT|O_EXCL|O_NOFOLLOW at 0600" || bad "record temp open not exclusive"
grep -q 'mktemp -d "\${TMPDIR:-/var/tmp}/asl-restored' "$here/../asl.sh" && ok "asl.sh keeps the record in a private (0700) mktemp -d directory" || bad "asl.sh record dir"
# the restore's --record output: a signed entry restores and is recorded; see JanusASL/tools/test_asl_mod_cache.sh for the cache itself
grep -q -- '--record' "$here/../../JanusASL/tools/asl_mod_cache.py" && grep -q 'RESTORED\[dst\] = h' "$here/../../JanusASL/tools/asl_mod_cache.py" && ok "asl_mod_cache.py restore records exactly the files it copied from verified entries" || bad "restore --record missing"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
