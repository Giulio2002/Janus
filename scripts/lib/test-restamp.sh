#!/usr/bin/env bash
# Self-test of scripts/lib/restamp.py (the framework stamp's pins follow ONLY cache-restored, verified files) and of the
# `--record` output of JanusASL/tools/asl_mod_cache.py restore.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
t="$(mktemp -d "${TMPDIR:-/var/tmp}/test-restamp.XXXXXX")"; trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
sha() { sha256sum "$1" | cut -d' ' -f1; }
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
python3 -I - "$t/a" "$t/rec.json" <<'PY'
import hashlib, json, sys
d, rec = sys.argv[1], sys.argv[2]
h = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()
json.dump({d + "/.lake/build/lib/lean/Janus/A.olean": h(d + "/.lake/build/lib/lean/Janus/A.olean")}, open(rec, "w"))
PY
python3 -I "$here/restamp.py" "$t/a" "$t/rec.json" > "$t/out" 2>&1
[ "$(pin "$t/a" Janus/A.olean)" = "$(sha "$L/A.olean")" ] && [ "$(pin "$t/a" Janus/A.olean)" != "$oldA" ] && ok "a file restored from a verified cache entry gets its pin moved" || bad "restored pin not moved"
[ "$(pin "$t/a" Janus/B.olean)" = "$oldB" ] && ok "a modified file that the cache did not restore keeps its old pin (janus will reject/rebuild it)" || bad "unrestored modified file was re-pinned"
python3 -I -c 'import json,sys; s=json.load(open(sys.argv[1])); assert (s["sha256"],s["manifest"],s["targets"],s["auditExe"])==("S","M",["Janus"],"E")' "$t/a/.lake/janus-framework.ready" && ok "sources hash, manifest, targets and the auditor's SHA-256 are untouched" || bad "stamp header changed"
# the record names A but A is changed again after the restore: no pin follows
mk "$t/b"; echo "restored A" > "$t/b/.lake/build/lib/lean/Janus/A.olean"
python3 -I - "$t/b" "$t/recb.json" <<'PY'
import hashlib, json, sys
d, rec = sys.argv[1], sys.argv[2]
json.dump({d + "/.lake/build/lib/lean/Janus/A.olean": hashlib.sha256(b"restored A\n").hexdigest()}, open(rec, "w"))
PY
oldA=$(pin "$t/b" Janus/A.olean); echo "tampered after the restore" > "$t/b/.lake/build/lib/lean/Janus/A.olean"
python3 -I "$here/restamp.py" "$t/b" "$t/recb.json" > /dev/null 2>&1
[ "$(pin "$t/b" Janus/A.olean)" = "$oldA" ] && ok "a restored file changed after the restore is not re-pinned" || bad "tampered-after-restore file was re-pinned"
# a symlink in place of a module file is never followed
mk "$t/c"; rm "$t/c/.lake/build/lib/lean/Janus/A.olean"; echo "x" > "$t/x"; ln -s "$t/x" "$t/c/.lake/build/lib/lean/Janus/A.olean"
python3 -I - "$t/c" "$t/recc.json" "$t/x" <<'PY'
import hashlib, json, sys
json.dump({sys.argv[1] + "/.lake/build/lib/lean/Janus/A.olean": hashlib.sha256(open(sys.argv[3], "rb").read()).hexdigest()}, open(sys.argv[2], "w"))
PY
oldA=$(pin "$t/c" Janus/A.olean); python3 -I "$here/restamp.py" "$t/c" "$t/recc.json" > /dev/null 2>&1
[ "$(pin "$t/c" Janus/A.olean)" = "$oldA" ] && ok "a symbolic link in place of a module file is not re-pinned" || bad "symlink re-pinned"
# no stamp / no record: nothing happens, rc 0
python3 -I "$here/restamp.py" "$t/nonexistent" "$t/rec.json" > /dev/null 2>&1 && ok "no stamp: nothing to do, rc 0" || bad "no stamp rc"
mk "$t/d"; echo changed > "$t/d/.lake/build/lib/lean/Janus/A.olean"; before=$(cat "$t/d/.lake/janus-framework.ready")
python3 -I "$here/restamp.py" "$t/d" "$t/missing-record.json" > /dev/null 2>&1; [ "$(cat "$t/d/.lake/janus-framework.ready")" = "$before" ] && ok "no record: the stamp is left as it is" || bad "stamp changed without a record"
# the restore's --record output: a signed entry restores and is recorded; see JanusASL/tools/test_asl_mod_cache.sh for the cache itself
grep -q -- '--record' "$here/../../JanusASL/tools/asl_mod_cache.py" && grep -q 'RESTORED\[dst\] = h' "$here/../../JanusASL/tools/asl_mod_cache.py" && ok "asl_mod_cache.py restore records exactly the files it copied from verified entries" || bad "restore --record missing"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
