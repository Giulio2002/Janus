#!/usr/bin/env bash
# Tests of the per-module JanusASL build cache (JanusASL/tools/asl_mod_cache.py; scripts/asl.sh
# ASL_CACHE; docs/ASL.md "Build cache").
#
#   JanusASL/tools/test_asl_mod_cache.sh              key tests (seconds)
#   JanusASL/tools/test_asl_mod_cache.sh --e2e CACHE  also end to end, with CACHE holding this
#                                                     commit's ArmASL and module entries (only read):
#                                                     a fresh copy of the checkout restores and builds
#                                                     JanusASL (timed; Lake must build no JanusASL or
#                                                     Janus module), then an edit to one proof file
#                                                     rebuilds exactly the modules whose key changed
#                                                     (that file and its dependents).
#
# Everything happens in mktemp directories, which are removed at the end.
set -euo pipefail
export LC_ALL=C
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
e2e=""
if [ "${1:-}" = --e2e ]; then e2e="${2:?--e2e CACHE}"; fi
t=$(mktemp -d "${TMPDIR:-/tmp}/asl-mod-cache-test.XXXXXX")
trap 'rm -rf "$t"' EXIT
fail=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fail=1; }

copy() {  # copy DIR: a copy of the checkout without builds
  rm -rf "$1"; mkdir -p "$1"
  rsync -a --exclude=.git --exclude=.lake --exclude=artifacts --exclude='JanusASL/ArmASL' \
    --exclude='JanusASL/ArmASL.lean' "$root/" "$1/"
}
keys() { python3 -I "$1/JanusASL/tools/asl_mod_cache.py" keys "$1" | sort; }
dependents() {  # dependents ROOT MODULE: MODULE and every module that imports it, transitively
  python3 -I - "$1" "$2" <<'PY'
import importlib.util, os, sys
root, target = sys.argv[1], sys.argv[2]
spec = importlib.util.spec_from_file_location("m", os.path.join(root, "JanusASL/tools/asl_mod_cache.py"))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
ks = m.Keys(root)
mods = ks.modules()
imp = {x: m.header_imports(ks.pkg_of(x).source(x)) for x in mods}
out, todo = {target}, True
while todo:
    todo = False
    for x in mods:
        if x not in out and any(i in out for i in imp[x]):
            out.add(x); todo = True
print("\n".join(sorted(out)))
PY
}
changed() { join -j1 <(keys "$1") <(keys "$2") | awk '$2 != $3 {print $1}'; }

copy "$t/a"
keys "$t/a" > "$t/a.keys"
n=$(wc -l < "$t/a.keys")
[ "$(grep -c ' None$' "$t/a.keys" || true)" = 0 ] && ok "every one of the $n JanusASL and Janus modules has a key" ||
  bad "modules without a key: $(grep ' None$' "$t/a.keys" | head -3 | tr '\n' ' ')"
copy "$t/b"
[ "$(keys "$t/b" | sha256sum)" = "$(sha256sum < "$t/a.keys")" ] && ok "keys do not depend on the checkout's path" || bad "keys depend on the path"

# a comment and a reformatting in the JanusASL lakefile: parsed, so no key changes
printf '\n# a comment\n' >> "$t/b/JanusASL/lakefile.toml"
[ -z "$(changed "$t/a" "$t/b")" ] && ok "a lakefile comment changes no key" || bad "a lakefile comment changed keys"

# one proof file: it and exactly its dependents
copy "$t/b"
f=JanusASL/JanusASL/Proofs/Madd.lean
echo "-- edited" >> "$t/b/$f"
c=$(changed "$t/a" "$t/b")
deps=$(dependents "$t/b" JanusASL.Proofs.Madd)
[ "$c" = "$deps" ] && ok "editing $f changes exactly its $(echo "$c" | wc -l) dependents' keys (of $n)" ||
  bad "editing $f changed: $(echo "$c" | tr '\n' ' ') expected: $(echo "$deps" | tr '\n' ' ')"

# a framework file every proof imports: every JanusASL module and the Janus dependents
copy "$t/b"
echo "-- edited" >> "$t/b/Janus/Arm64/State.lean"
c=$(changed "$t/a" "$t/b")
d=$(dependents "$t/b" Janus.Arm64.State)
[ "$c" = "$d" ] && ok "editing Janus/Arm64/State.lean changes exactly its $(echo "$c" | wc -l) dependents' keys ($(echo "$c" | grep -c '^JanusASL') JanusASL)" ||
  bad "State.lean edit changed $(echo "$c" | wc -l) keys, expected $(echo "$d" | wc -l)"

# a setting Lake traces (a library's moreLeanArgs) and the toolchain
copy "$t/b"
sed -i 's/^name = "JanusASL"$/name = "JanusASL"\nmoreLeanArgs = ["--tstack=100000"]/' "$t/b/JanusASL/lakefile.toml"
c=$(changed "$t/a" "$t/b" | grep -c '^JanusASL' || true)
[ "$c" -gt 0 ] && ok "a JanusASL lib option changes the JanusASL keys ($c)" || bad "a lib option changed no key"
copy "$t/b"
echo "leanprover/lean4:v4.99.0" > "$t/b/lean-toolchain"
c=$(changed "$t/a" "$t/b" | wc -l)
[ "$c" = "$n" ] && ok "the toolchain changes every key" || bad "the toolchain changed $c of $n keys"


# `restore --record`: a signed record (scripts/lib/restamp.py verifies it), written O_EXCL|O_NOFOLLOW at 0600
export JANUS_CACHE_KEY_DIR="$t/key"; mkdir -m 700 "$t/key"
mkdir -m 700 "$t/recd" "$t/emptycache"
python3 -I "$t/a/JanusASL/tools/asl_mod_cache.py" restore "$t/a" "$t/emptycache" --record "$t/recd/record.json" > /dev/null 2>&1
if python3 -I - "$t/recd/record.json" "$t/a" "$root/scripts/lib/bcache.py" <<'PY'
import importlib.util, json, os, stat, sys
rec, tree, bcp = sys.argv[1:4]
spec = importlib.util.spec_from_file_location("bcache", bcp); bc = importlib.util.module_from_spec(spec); spec.loader.exec_module(bc)
d = json.load(open(rec))
assert set(d) == {"files", "mac"} and d["mac"] == bc.record_mac(tree, d["files"]) and d["mac"] != bc.record_mac(tree + "x", d["files"])
assert stat.S_IMODE(os.lstat(rec).st_mode) == 0o600
PY
then ok "restore --record writes a 0600 record with an HMAC over its files, bound to the tree"; else bad "restore --record output"; fi
# a symlink planted at the temp name (same pid via exec) is not followed
echo untouched > "$t/victim"; rm -f "$t/recd/record.json"
python3 -I - "$t/a" "$t/emptycache" "$t/recd/record.json" "$t/victim" "$t/a/JanusASL/tools/asl_mod_cache.py" <<'PY' > /dev/null 2>&1 || true
import os, sys
tree, cache, rec, victim, tool = sys.argv[1:6]
os.symlink(victim, rec + ".tmp%d" % os.getpid())
os.execv(sys.executable, [sys.executable, "-I", tool, "restore", tree, cache, "--record", rec])
PY
[ "$(cat "$t/victim")" = untouched ] && [ ! -e "$t/recd/record.json" ] && ok "a symlink planted at the record's temp name is not followed (the write fails, the victim is untouched)" || bad "planted temp symlink followed"

# publish refuses a Janus module whose output differs from the framework stamp's pin (a stamped tree)
mkdir -p "$t/a/.lake/build/lib/lean/Janus"; echo built > "$t/a/.lake/build/lib/lean/Janus/State.olean"
sp="$t/a/.lake/janus-framework.ready"
if python3 -I - "$t/a" "$sp" <<'PY'
import hashlib, importlib.util, json, os, sys
root, sp = sys.argv[1:3]
spec = importlib.util.spec_from_file_location("m", os.path.join(root, "JanusASL/tools/asl_mod_cache.py")); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
ks = m.Keys(root); p = ks.pkg_of("Janus.State") or ks.pkgs[1]
ol = os.path.join(root, ".lake/build/lib/lean/Janus/State.olean")
assert m.stamp_mismatch(ks, p, "Janus.State") is None            # no stamp: unconstrained
good = hashlib.sha256(b"built\n").hexdigest()
json.dump({"pins": {"Janus/State.olean": good}}, open(sp, "w"))
assert m.stamp_mismatch(ks, p, "Janus.State") is None            # as pinned
open(ol, "w").write("tampered\n")
assert m.stamp_mismatch(ks, p, "Janus.State") is not None        # differs from the pin
json.dump({"pins": {"Janus/Other.olean": good}}, open(sp, "w"))
assert m.stamp_mismatch(ks, p, "Janus.State") is None            # not a pinned file
PY
then ok "publish refuses a Janus module output that differs from the stamp's pin (and only then)"; else bad "stamp_mismatch"; fi
rm -rf "$t/a/.lake"

if [ -n "$e2e" ]; then
  # A fresh copy at this commit: restore (ArmASL and modules) and build JanusASL.
  copy "$t/w"
  (cd "$t/w/JanusASL" && tar -xzf vendor/ArmASL.tar.gz && touch ArmASL.lean)
  start=$(date +%s)
  (cd "$t/w" && ASL_CACHE="$e2e" ASL_CACHE_READONLY=1 scripts/asl.sh restore) > "$t/restore.log" 2>&1
  python3 -I "$t/w/JanusASL/tools/asl_mod_cache.py" restore "$t/w" "$e2e" | tee -a "$t/restore.log"
  (cd "$t/w/JanusASL" && lake build --no-ansi JanusASL) > "$t/build.log" 2>&1
  secs=$(( $(date +%s) - start ))
  built=$(grep -cE '(Built|Replayed) (JanusASL|Janus)\.' "$t/build.log" | head -1 || true)
  nb=$(grep -E 'Built (JanusASL|Janus)[. ]' "$t/build.log" | grep -vc ':c\.o\|:o\b' || true)
  [ "$nb" = 0 ] && ok "a fresh copy restores and builds JanusASL in ${secs}s, elaborating no module" ||
    bad "the fresh copy elaborated $nb modules ($(grep -E 'Built (JanusASL|Janus)[. ]' "$t/build.log" | head -3 | tr '\n' ' '))"
  # One proof file edited: Lake builds exactly the modules whose key changed.
  keys "$t/w" > "$t/w.keys"
  # a change to the module's content (a comment would leave its .olean, and so its dependents'
  # traces, unchanged: Lake then rebuilds only the edited module)
  printf '\ntheorem asl_mod_cache_test_edit : True := trivial\n' >> "$t/w/$f"
  # the modules `lake build JanusASL` builds: the closure of the library's roots
  inlib=$(python3 -I - "$t/w" <<'PY'
import importlib.util, os, sys
root = sys.argv[1]
spec = importlib.util.spec_from_file_location("m", os.path.join(root, "JanusASL/tools/asl_mod_cache.py"))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
ks = m.Keys(root)
roots = [r for lib in ks.pkgs[0].cfg.get("lean_lib", []) if lib.get("name") == "JanusASL" for r in lib.get("roots", ["JanusASL"])]
print("\n".join(sorted(m.closure(ks, roots))))
PY
)
  expect=$(join -j1 "$t/w.keys" <(keys "$t/w") | awk '$2 != $3 {print $1}' | sort | comm -12 - <(echo "$inlib"))
  start=$(date +%s)
  (cd "$t/w/JanusASL" && lake build --no-ansi JanusASL) > "$t/build2.log" 2>&1
  secs=$(( $(date +%s) - start ))
  got=$(grep -oE 'Built (JanusASL|Janus)\.[A-Za-z0-9_.]+( |$)' "$t/build2.log" | awk '{print $2}' | sort -u)
  [ "$got" = "$expect" ] && ok "after editing $f, Lake rebuilt exactly it and its $(( $(echo "$got" | wc -l) - 1 )) dependents in ${secs}s (of $n modules)" ||
    bad "after editing $f Lake rebuilt: $(echo "$got" | tr '\n' ' ') expected: $(echo "$expect" | tr '\n' ' ')"
fi
exit $fail
