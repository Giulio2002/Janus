#!/usr/bin/env bash
# Tests of the compiled-object cache (kind armobj: asl_mod_cache.py objkey/objfiles, scripts/lib/bcache.py;
# scripts/asl.sh objcache_*; asl_mod_cache.py "Compiled objects"): the C objects of ArmASL and lean-sail are reused
# across checkout paths, and a tampered object, a wrong HMAC key, a changed C file or an incomplete set is a miss
# or a rejection (rebuild), never a silent pass. Seconds; everything happens in mktemp directories.
#
#   JanusASL/tools/test_asl_obj_cache.sh
set -uo pipefail
export LC_ALL=C
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
t=$(mktemp -d "${TMPDIR:-/tmp}/asl-obj-cache-test.XXXXXX")
trap 'rm -rf "$t"' EXIT
export JANUS_CACHE_KEY_DIR="$t/keys"
fail=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fail=1; }
B() { python3 -I "$root/scripts/lib/bcache.py" "$@"; }
M() { python3 -I "$root/JanusASL/tools/asl_mod_cache.py" "$@"; }
expect() {  # expect RC DESCRIPTION CMD...
  local want=$1 d=$2 rc=0; shift 2
  "$@" > "$t/out" 2> "$t/err" || rc=$?
  if [ "$rc" = "$want" ]; then ok "$d (rc $rc)"; else bad "$d: rc $rc, wanted $want: $(head -c 300 "$t/out" "$t/err" | tr '\n' ' ')"; fi
}

copy() {  # copy DIR: a copy of the checkout without builds
  rm -rf "$1"; mkdir -p "$1"
  rsync -a --exclude=.git --exclude=.lake --exclude=artifacts --exclude='JanusASL/ArmASL' \
    --exclude='JanusASL/ArmASL.lean' "$root/" "$1/"
}
# a built-looking tree: emitted C, and an object + hash + trace for each, as Lake writes them (the trace records the
# compile command, the object's output hash and the C file's hash), compiled by the toolchain's clang
prefix=$(cd "$root/JanusASL" && lean --print-prefix); clang="$prefix/bin/clang"
[ -x "$clang" ] || { echo "FAIL: no toolchain clang at $clang"; exit 1; }
mkobj() {  # mkobj LAKE CFILE [CLANG]: compile CFILE as Lake would (and write .hash/.trace/.c.hash)
  local f="$2" cc="${3:-$clang}" oh ch
  (cd "$(dirname "$f")" && "$cc" -c -o "$f.o.export" "$f" -I "$prefix/include" -fPIC -O3 -DNDEBUG -DLEAN_EXPORTING)
  oh=$(sha256sum < "$f.o.export" | cut -c1-16); ch=$(sha256sum < "$f" | cut -c1-16)
  echo "$oh" > "$f.o.export.hash"; echo "$ch" > "$f.c.hash.tmp"; mv "$f.c.hash.tmp" "$f.hash"
  python3 -I - "$f" "$cc" "$oh" "$ch" "$prefix" > "$f.o.export.trace" <<'PY'
import json, sys
f, cc, oh, ch, prefix = sys.argv[1:]
cmd = "%s -c -o %s.o.export %s -I %s/include -fPIC -O3 -DNDEBUG -DLEAN_EXPORTING" % (cc, f, f, prefix)
print(json.dumps({"synthetic": False, "schemaVersion": "2025-09-10", "outputs": oh + ".o",
                  "log": [{"message": ".> " + cmd, "level": "trace"}],
                  "inputs": [["M:c", [[f, ch], ["Lean 4", "e9"]]], ["traceArgs: #[-O3]", "2d"]], "depHash": "e9ea8fa0bde1bdff"}))
PY
}
build() {  # build DIR: fake .lake/build/ir with the same C in any directory
  local lake="$1/JanusASL/.lake" d f
  for d in "$lake/build/ir/ArmASL" "$lake/packages/Sail/.lake/build/ir/Sail" "$lake/build/ir/JanusASL"; do mkdir -p "$d"; done
  for f in "$lake/build/ir/ArmASL.c" "$lake/build/ir/ArmASL/Part01.c" "$lake/build/ir/ArmASL/Part02.c" \
           "$lake/packages/Sail/.lake/build/ir/Sail/Attr.c" "$lake/build/ir/JanusASL/Check.c"; do
    printf '// Lean compiler output\nint f_%s(void){return %d;}\n' "$(basename "$f" .c)" "$(basename "$f" .c | wc -c)" > "$f"
    case "$f" in */ir/JanusASL/*) continue ;; esac   # the jasl scope is built by build_jasl
    mkobj "$lake" "$f"
  done
}
cache="$t/cache"; mkdir -p "$cache"
copy "$t/a"; build "$t/a"
copy "$t/deep/er/b"; build "$t/deep/er/b"
ida=$(M objkey "$t/a"); idb=$(M objkey "$t/deep/er/b")
[ -n "$ida" ] && [ "$ida" = "$idb" ] && ok "the entry id does not depend on the checkout's path ($ida)" || bad "id differs by path: $ida vs $idb"
[ -n "$clang" ] && { cmp -s "$t/a/JanusASL/.lake/build/ir/ArmASL/Part01.c.o.export" "$t/deep/er/b/JanusASL/.lake/build/ir/ArmASL/Part01.c.o.export" &&
  ok "the same C compiled in two directories gives a bit-identical object" || bad "objects differ across directories"; }
M objfiles "$t/a" | tr '\0' '\n' | grep -c . | grep -qx 12 && ok "4 C files (ArmASL.c, 2 parts, 1 Sail) x (object, hash, trace) = 12 files; JanusASL C is out of scope" || bad "objfiles count"

store() { M objfiles "$1" > "$t/fl" && B store armobj "$cache" "$ida" "$1/JanusASL/.lake" < "$t/fl"; }
expect 0 "store from the first checkout" store "$t/a"
expect 0 "fetch into the other path hits" B fetch armobj "$cache" "$idb" "$t/new/.lake"
(cd "$t/a/JanusASL/.lake" && M objfiles "$t/a" | tr '\0' '\n' | while read -r f; do cmp -s "$f" "$t/new/.lake/$f" || echo "DIFF $f"; done) > "$t/diff"
[ ! -s "$t/diff" ] && ok "the restored files are byte-identical" || bad "restore differs: $(head -3 "$t/diff")"
B fetch armobj "$cache" "$idb" "$t/new/.lake" > "$t/o"; [ "$(cat "$t/o")" = current ] && ok "an identical tree is 'current'" || bad "current"

# the JanusASL scope: its own id/entry (per-library C, e.g. the huge Proofs.Config), independent of the arm scope
build_jasl() { mkobj "$1/JanusASL/.lake" "$1/JanusASL/.lake/build/ir/JanusASL/Check.c"; }
build_jasl "$t/a"; build_jasl "$t/deep/er/b"
ja=$(M objkey "$t/a" jasl); jb=$(M objkey "$t/deep/er/b" jasl)
[ -n "$ja" ] && [ "$ja" = "$jb" ] && [ "$ja" != "$ida" ] && ok "the jasl scope has its own id, path independent" || bad "jasl id: $ja $jb $ida"
M objfiles "$t/a" jasl | tr '\0' '\n' | grep -c . | grep -qx 3 && ok "jasl scope = 1 C file x 3" || bad "jasl objfiles"
M objfiles "$t/a" | tr "\0" "\n" | { grep -c JanusASL/Check || true; } | grep -qx 0 && ok "arm scope still excludes JanusASL C" || bad "arm scope leaks"
printf '// c\nint g;\n' > "$t/a/JanusASL/.lake/build/ir/JanusASL/NoObj.c"
M objfiles "$t/a" jasl | tr '\0' '\n' | grep -c . | grep -qx 3 && ok "jasl: a C file without any object is skipped" || bad "jasl partial"
rm "$t/a/JanusASL/.lake/build/ir/JanusASL/NoObj.c"
rm "$t/a/JanusASL/.lake/build/ir/JanusASL/Check.c.o.export.trace"; expect 1 "jasl: an incomplete triple still refuses" M objfiles "$t/a" jasl
echo '{}' > "$t/a/JanusASL/.lake/build/ir/JanusASL/Check.c.o.export.trace"
expect 1 "an unknown scope is refused" M objkey "$t/a" bogus
M objfiles "$t/a" jasl > "$t/fl"; expect 0 "store jasl scope" B store armobj "$cache" "$ja" "$t/a/JanusASL/.lake" < "$t/fl"
expect 0 "fetch jasl scope into another path" B fetch armobj "$cache" "$jb" "$t/newj/.lake"
rm -rf "$cache/armobj/$ja"

# a changed emitted C file: another id, so a miss (never the stale object)
copy "$t/c"; build "$t/c"; echo '// edit' >> "$t/c/JanusASL/.lake/build/ir/ArmASL/Part02.c"
idc=$(M objkey "$t/c"); [ "$idc" != "$ida" ] && ok "one changed C byte changes the id" || bad "id unchanged"
expect 2 "... which is a miss" B fetch armobj "$cache" "$idc" "$t/new2/.lake"
[ -z "$(find "$t/new2" -type f 2>/dev/null)" ] && ok "... and copies nothing" || bad "files copied on a miss"
# an incomplete set (an object removed) is not published
rm "$t/c/JanusASL/.lake/build/ir/ArmASL/Part01.c.o.export.trace"
expect 1 "an incomplete object set has no file list (nothing is stored)" M objfiles "$t/c"
# a changed compiler flag is in the ArmASL key, hence in the id
copy "$t/d"; build "$t/d"; sed -i 's/^moreLeancArgs = \["-fbracket-depth=100000"\]$/moreLeancArgs = ["-fbracket-depth=100001"]/' "$t/d/JanusASL/lakefile.toml"
[ "$(M objkey "$t/d")" != "$ida" ] && ok "a changed compiler flag changes the id" || bad "flag change not in the id"

e="$cache/armobj/$ida"
tamper_case() {  # DESC COMMAND: a fresh entry, COMMAND, then fetch must reject (rc 3) and copy nothing
  rm -rf "$cache/armobj" "$t/dx"; store "$t/a" > /dev/null; eval "$2"
  expect 3 "rejected: $1" B fetch armobj "$cache" "$ida" "$t/dx/.lake"
  [ -z "$(find "$t/dx" -type f ! -name '.bcache-tree.lock' 2>/dev/null)" ] && ok "  ... nothing copied: $1" || bad "  ... files copied: $1"
  expect 3 "  ... verify says invalid: $1" B verify armobj "$cache" "$ida"
  store "$t/a" > /dev/null 2>&1; B verify armobj "$cache" "$ida" > /dev/null && ok "  ... the next store replaces it: $1" || bad "  ... not replaced: $1"
}
o=build/ir/ArmASL/Part01.c.o.export
tamper_case "a tampered object" 'chmod u+w "$e/tree/$o"; printf X | dd of="$e/tree/$o" bs=1 count=1 conv=notrunc 2>/dev/null'
tamper_case "a tampered trace" 'chmod u+w "$e/tree/$o.trace"; echo evil >> "$e/tree/$o.trace"'
tamper_case "a missing object" 'rm "$e/tree/$o"'
tamper_case "an object replaced by a symlink" 'rm "$e/tree/$o"; ln -s /etc/passwd "$e/tree/$o"'
tamper_case "an object and its manifest hash rewritten (HMAC no longer matches)" \
  'echo evil > "$e/tree/$o"; h=$(sha256sum "$e/tree/$o" | cut -d" " -f1); sed -i "s|^[0-9a-f]*  build/ir/ArmASL/Part01.c.o.export\$|$h  build/ir/ArmASL/Part01.c.o.export|" "$e/MANIFEST.sha256"'
tamper_case "a bad HMAC" 'echo 0000000000000000000000000000000000000000000000000000000000000000 > "$e/MANIFEST.hmac"'

# a wrong key: an entry signed under another per-user key is rejected, not used
rm -rf "$cache/armobj" "$t/dx"; store "$t/a" > /dev/null
rc=0; JANUS_CACHE_KEY_DIR="$t/otherkeys" B fetch armobj "$cache" "$ida" "$t/dx/.lake" > "$t/out" 2> "$t/err" || rc=$?
[ "$rc" = 3 ] && [ -z "$(find "$t/dx" -type f ! -name '.bcache-tree.lock' 2>/dev/null)" ] && ok "an entry signed under another key is rejected (rc 3), nothing copied" || bad "wrong key: rc $rc"
# an entry copied under another id (a poisoned/misplaced entry) is rejected: the id is in the HMAC
cp -a "$cache/armobj/$ida" "$cache/armobj/$(printf 'f%.0s' {1..40})"
expect 3 "an entry moved to another id is rejected" B fetch armobj "$cache" "$(printf 'f%.0s' {1..40})" "$t/dy/.lake"
# the gc treats armobj entries as ordinary LRU entries
touch -d '2 days ago' "$cache/armobj/$ida" "$cache/armobj/$ida.use" 2>/dev/null
touch -d '2 days ago' "$cache/armobj/$(printf 'f%.0s' {1..40})"
M gc "$cache" --max 1K --grace 0 > "$t/out" 2>&1; [ ! -e "$cache/armobj/$ida" ] && ok "gc evicts armobj entries over budget" || bad "gc kept an armobj entry: $(cat "$t/out")"


# ======== publish side: objstage binds the objects to the current C and to the keyed compiler ========
copy "$t/p"; build "$t/p"; build_jasl "$t/p"
stage() {  # stage DIR SCOPE: objstage into a fresh stage; prints the id (rc 0) or fails
  rm -rf "$t/st"; mkdir -p "$t/st"; M objstage "$1" "$2" "$t/st" "$t/st.list"
}
expect 0 "objstage accepts a genuine tree (arm)" stage "$t/p" arm
[ "$(cat "$t/out")" = "$(M objkey "$t/p")" ] && ok "  ... and prints the id objkey gives" || bad "objstage id differs from objkey"
ls "$t/st/build/ir/ArmASL/Part01.c.o.export.cin" > /dev/null 2>&1 && ok "  ... with a .cin record of each C file" || bad "no .cin"
expect 0 "objstage accepts a genuine tree (jasl)" stage "$t/p" jasl
# (publish-side lie 1) the C changed after the object was compiled (lean re-emitted it: .c.hash is new, the trace is old)
copy "$t/q"; build "$t/q"; q="$t/q/JanusASL/.lake/build/ir/ArmASL/Part02.c"
echo '// other C' >> "$q"; sha256sum < "$q" | cut -c1-16 > "$q.hash"
expect 1 "objstage refuses an object whose trace records another C hash than the current C" stage "$t/q" arm
# (lie 2) the object bytes were swapped but hash/trace kept: objstage cannot see it, the recompile at store does
copy "$t/r"; build "$t/r"; r="$t/r/JanusASL/.lake/build/ir/ArmASL/Part01.c"
printf 'int other(void){return 7;}\n' > "$t/other.c"; (cd "$t" && "$clang" -c -o "$r.o.export" other.c -I "$prefix/include" -fPIC -O3 -DNDEBUG -DLEAN_EXPORTING)
expect 0 "objstage cannot see swapped object bytes under an unchanged hash/trace (the recompile does)" stage "$t/r" arm
idr=$(cat "$t/out"); rm -rf "$cache/armobj"
expect 4 "store --recompile refuses to publish the swapped object" B store armobj "$cache" "$idr" "$t/st" --c-root "$t/r/JanusASL/.lake" --recompile all < "$t/st.list"
[ ! -e "$cache/armobj/$idr" ] && ok "  ... and nothing was stored" || bad "stored a poisoned entry"
# poisoned entry published without the recompile (an old/other publisher): verify --recompile detects it, store --recompile replaces it
expect 0 "a poisoned entry stored without recompile" B store armobj "$cache" "$idr" "$t/st"  < "$t/st.list"
expect 3 "verify --recompile all reports POISONED" B verify armobj "$cache" "$idr" --c-root "$t/r/JanusASL/.lake" --recompile all
grep -q POISONED "$t/out" && ok "  ... says POISONED" || bad "no POISONED message"
cp "$t/q/JanusASL/.lake/build/ir/ArmASL/Part02.c" /dev/null
build "$t/r"   # rebuild the genuine objects in place
stage "$t/r" arm > /dev/null
expect 0 "store --recompile replaces the poisoned entry when the recompile differs" B store armobj "$cache" "$idr" "$t/st" --c-root "$t/r/JanusASL/.lake" --recompile all < "$t/st.list"
grep -q stored "$t/out" && ok "  ... (stored, not 'present')" || bad "poisoned entry not replaced: $(cat "$t/out")"
expect 0 "the replacement verifies and recompiles bit-identically" B verify armobj "$cache" "$idr" --c-root "$t/r/JanusASL/.lake" --recompile all
# (lie 3) a shim compiler at another path, and a shim at the keyed path (content hashed into the id)
copy "$t/s"; build "$t/s"; mkdir -p "$t/shim"; printf '#!/bin/sh\nexec "%s" "$@"\n' "$clang" > "$t/shim/clang"; chmod +x "$t/shim/clang"
mkobj "$t/s/JanusASL/.lake" "$t/s/JanusASL/.lake/build/ir/ArmASL/Part01.c" "$t/shim/clang"
expect 1 "objstage refuses an object whose trace names another compiler than the keyed one" stage "$t/s" arm
id0=$(M objkey "$t/p"); id1=$(LEAN_CC="$t/shim/clang" M objkey "$t/p")
[ "$id0" != "$id1" ] && ok "LEAN_CC set changes the id" || bad "LEAN_CC not in the id"
printf '#!/bin/sh\n# other bytes\nexec "%s" "$@"\n' "$clang" > "$t/shim/clang2"; chmod +x "$t/shim/clang2"
id2=$(LEAN_CC="$t/shim/clang2" M objkey "$t/p"); [ "$id1" != "$id2" ] && ok "another LEAN_CC binary is another id" || bad "LEAN_CC keyed by name only"
cp "$t/shim/clang2" "$t/shim/clang"; id3=$(LEAN_CC="$t/shim/clang" M objkey "$t/p")
printf '#!/bin/sh\n# third\nexec "%s" "$@"\n' "$clang" > "$t/shim/clang"; id4=$(LEAN_CC="$t/shim/clang" M objkey "$t/p")
[ "$id4" != "$id3" ] && ok "the same LEAN_CC path with other content is another id" || bad "LEAN_CC same path new content"
# (B2) every compile-affecting variable and table changes the id
for v in CCC_OVERRIDE_OPTIONS CCC_ADD_ARGS COMPILER_PATH GCC_EXEC_PREFIX CLANG_FOO CPLUS_INCLUDE_PATH; do
  idv=$(env "$v=x" python3 -I "$root/JanusASL/tools/asl_mod_cache.py" objkey "$t/p"); [ "$idv" != "$id0" ] && ok "$v changes the id" || bad "$v not keyed"
done
copy "$t/w"; build "$t/w"; build_jasl "$t/w"
j0=$(M objkey "$t/w" jasl)
grep -n "weakLeancArgs\|^name = \"JanusASL\"\|\[\[lean_lib\]\]" "$t/w/JanusASL/lakefile.toml" | head -3 > /dev/null
python3 -I - "$t/w/JanusASL/lakefile.toml" <<'PY'
import re, sys
p = sys.argv[1]; s = open(p).read()
i = s.index('name = "JanusASL"'); j = s.index("\n", i)
open(p, "w").write(s[:j] + '\nweakLeancArgs = ["-fno-foo"]' + s[j:])
PY
j1=$(M objkey "$t/w" jasl); [ "$j0" != "$j1" ] && ok "weakLeancArgs of lean_lib JanusASL changes the jasl id" || bad "weakLeancArgs not in the jasl id"
copy "$t/w2"; build "$t/w2"; build_jasl "$t/w2"
python3 -I - "$t/w2/JanusASL/lakefile.toml" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read()
i = s.index('name = "janus-asl-check"'); j = s.index("\n", i)
open(p, "w").write(s[:j] + '\nmoreLinkArgs = ["-lfoo"]' + s[j:])
PY
j2=$(M objkey "$t/w2" jasl); [ "$j0" != "$j2" ] && ok "a lean_exe janus-asl-check link arg changes the jasl id" || bad "exe table not in the jasl id"
# mutants: machine and scope are in the id
mid=$(python3 -I - "$root" "$t/p" <<'PY'
import importlib.util, platform, sys
spec = importlib.util.spec_from_file_location("m", sys.argv[1] + "/JanusASL/tools/asl_mod_cache.py"); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
lake = sys.argv[2] + "/JanusASL/.lake"; cs = m.obj_c_files(lake)
a = m.obj_id(sys.argv[2], cs); platform.machine = lambda: "riscv64"; b = m.obj_id(sys.argv[2], cs)
m.obj_tables = lambda r, sc="jasl": {}   # isolate the scope field from the tables
seen = []; oc = m.canonical; m.canonical = lambda o: (seen.append(o), oc(o))[1]
m.obj_id(sys.argv[2], cs, "jasl"); inp = seen[-1]
print("machine-keyed" if a != b else "machine-NOT-keyed", "scope-keyed" if inp.get("scope") == "jasl" and "scope" not in (seen.append(None) or {}) else "scope-NOT-keyed")
PY
)
[ "$mid" = "machine-keyed scope-keyed" ] && ok "the id depends on the machine and on the scope" || bad "id mutants: $mid"
# an object that is a symlink is refused by objfiles AND objstage
copy "$t/y"; build "$t/y"; yo="$t/y/JanusASL/.lake/build/ir/ArmASL/Part01.c.o.export"; cp "$yo" "$t/y.o"; rm "$yo"; ln -s "$t/y.o" "$yo"
expect 1 "objfiles refuses an object that is a symlink" M objfiles "$t/y"
expect 1 "objstage refuses an object that is a symlink" stage "$t/y" arm

# ======== D1: per-kind path allowlist, at store and at fetch ========
expect 4 "store refuses a non-object path in an armobj entry" B store armobj "$cache" "$(printf 'a%.0s' {1..40})" "$t/p/JanusASL" < <(printf 'JanusASL.lean\0')
expect 4 "store refuses an .olean in an armobj entry" B store armobj "$cache" "$(printf 'a%.0s' {1..40})" "$t/p/JanusASL/.lake" < <(printf 'build/ir/ArmASL/Foo.olean\0')
# a correctly signed entry that contains an .olean: fetch rejects it and writes nothing
python3 -I - "$root" "$cache" "$t/p" <<'PY'
import os, sys, importlib.util
spec = importlib.util.spec_from_file_location("bcache", sys.argv[1] + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
cache, ident = sys.argv[2], "b" * 40
e = b.entry_dir("armobj", cache, ident); os.makedirs(e + "/tree/build/lib/lean"); open(e + "/tree/build/lib/lean/Foo.olean", "w").write("evil")
data = ("%s  build/lib/lean/Foo.olean\n" % b.sha_file(e + "/tree/build/lib/lean/Foo.olean")).encode()
open(e + "/MANIFEST.sha256", "wb").write(data); open(e + "/MANIFEST.hmac", "w").write(b.mac("armobj", ident, data) + "\n")
PY
mkdir -p "$t/dz/.lake/build/lib/lean"; echo good > "$t/dz/.lake/build/lib/lean/Foo.olean"
expect 3 "fetch rejects a signed armobj entry that would overwrite an .olean" B fetch armobj "$cache" "$(printf 'b%.0s' {1..40})" "$t/dz/.lake"
[ "$(cat "$t/dz/.lake/build/lib/lean/Foo.olean")" = good ] && ok "  ... the olean is untouched" || bad "olean overwritten"
# ======== D2: a symlinked destination component is refused ========
rm -rf "$cache/armobj/$ida"; stage "$t/a" arm > /dev/null; B store armobj "$cache" "$ida" "$t/st" < "$t/st.list" > /dev/null
mkdir -p "$t/victim" "$t/dsym/.lake"; ln -s "$t/victim" "$t/dsym/.lake/build"
expect 3 "fetch refuses a destination whose build/ is a symlink" B fetch armobj "$cache" "$ida" "$t/dsym/.lake"
[ -z "$(find "$t/victim" -type f)" ] && ok "  ... nothing was written through the link" || bad "wrote through a symlink: $(find "$t/victim" -type f | head -2)"
mkdir -p "$t/dsym2/.lake/build/ir"; ln -s "$t/victim" "$t/dsym2/.lake/build/ir/ArmASL"
expect 3 "fetch refuses a destination whose build/ir/ArmASL is a symlink" B fetch armobj "$cache" "$ida" "$t/dsym2/.lake"
[ -z "$(find "$t/victim" -type f)" ] && ok "  ... nothing was written through the link" || bad "wrote through a deep symlink"
# ======== concurrency: 6 stores and 6 fetches of one entry ========
rm -rf "$cache/armobj/$ida"; pids=()
for i in 1 2 3 4 5 6; do (B store armobj "$cache" "$ida" "$t/st" < "$t/st.list" > "$t/cs$i" 2>&1; echo $? > "$t/cs$i.rc") & pids+=($!); done; wait "${pids[@]}"
cat "$t"/cs?.rc | sort | uniq -c | tr '\n' ' ' | grep -q "^ *6 0 $" && ok "6 concurrent stores all succeed" || bad "concurrent stores: $(cat "$t"/cs?.rc | tr '\n' ' ')"
[ "$(cat "$t"/cs? | grep -c '^stored$')" = 1 ] && ok "  ... exactly one stored" || bad "stored count: $(cat "$t"/cs? | tr '\n' ' ')"
pids=(); for i in 1 2 3 4 5 6; do (B fetch armobj "$cache" "$ida" "$t/cf/.lake" > "$t/cf$i" 2>&1; echo $? > "$t/cf$i.rc") & pids+=($!); done; wait "${pids[@]}"
cat "$t"/cf?.rc | sort | uniq -c | tr '\n' ' ' | grep -q "^ *6 0 $" && ok "6 concurrent fetches into one tree all succeed" || bad "concurrent fetches: $(cat "$t"/cf?.rc | tr '\n' ' ')"
B verify armobj "$cache" "$ida" > /dev/null && ok "  ... the entry is valid afterwards" || bad "entry invalid after the race"

# ======== per-object scope (jasl): one entry per object, a changed module recompiles only itself ========
mkjc() {  # mkjc LAKE REL NAME: a C file + object under LAKE/build/ir/REL
  mkdir -p "$1/build/ir/$2"; printf '// c\nint %s_f(void){return %d;}\n' "$3" "${#3}" > "$1/build/ir/$2/$3.c"; mkobj "$1" "$1/build/ir/$2/$3.c"
}
copy "$t/pj"; mkdir -p "$t/pj/JanusASL/.lake"
for n in A B Big; do mkjc "$t/pj/JanusASL/.lake" JanusASL "$n"; done
printf '// no object\nint z;\n' > "$t/pj/JanusASL/.lake/build/ir/JanusASL/NoObj.c"; echo 0000000000000000 > "$t/pj/JanusASL/.lake/build/ir/JanusASL/NoObj.c.hash"
pc="$t/pc"; mkdir -p "$pc"
expect 0 "objpublish jasl stores one entry per object that has one" M objpublish "$t/pj" jasl "$pc" all
grep -q "stored 3, already cached 0, no object 1, refused 0" "$t/out" && ok "  ... 3 entries (A, B, Big), NoObj skipped" || bad "jasl publish summary: $(cat "$t/out")"
[ "$(ls "$pc/armobj" | grep -c '^[0-9a-f]\{40\}$')" = 3 ] && ok "  ... 3 entry directories" || bad "entry count"
# a fresh checkout (same C, other path) restores them all
copy "$t/pk"; mkdir -p "$t/pk/JanusASL/.lake/build/ir/JanusASL"
cp "$t/pj/JanusASL/.lake/build/ir/JanusASL/"{A,B,Big,NoObj}.c "$t/pj/JanusASL/.lake/build/ir/JanusASL/"{A,B,Big,NoObj}.c.hash "$t/pk/JanusASL/.lake/build/ir/JanusASL/"
expect 0 "objrestore jasl" M objrestore "$t/pk" jasl "$pc"
grep -q "3 restored, 1 without entry, 0 rejected" "$t/out" && ok "  ... 3 restored, the object-less C has no entry" || bad "restore summary: $(cat "$t/out")"
[ -f "$t/pk/JanusASL/.lake/build/ir/JanusASL/Big.c.o.export" ] && cmp -s "$t/pk/JanusASL/.lake/build/ir/JanusASL/Big.c.o.export" "$t/pj/JanusASL/.lake/build/ir/JanusASL/Big.c.o.export" && ok "  ... byte-identical objects" || bad "restored object differs"
# one module changes: only its entry misses; the others still hit (D3: a changed module does not recompile Config)
echo '// changed' >> "$t/pk/JanusASL/.lake/build/ir/JanusASL/A.c"; rm -rf "$t/pk2"; mkdir -p "$t/pk2"; cp -a "$t/pk/JanusASL" "$t/pk2/JanusASL"; rm -f "$t/pk2/JanusASL/.lake/build/ir/JanusASL/"*.o.export*
copy "$t/pk3"; mkdir -p "$t/pk3/JanusASL/.lake/build/ir/JanusASL"; cp "$t/pk/JanusASL/.lake/build/ir/JanusASL/"*.c "$t/pk/JanusASL/.lake/build/ir/JanusASL/"*.c.hash "$t/pk3/JanusASL/.lake/build/ir/JanusASL/"
expect 0 "objrestore after one C changed" M objrestore "$t/pk3" jasl "$pc"
grep -q "2 restored, 2 without entry" "$t/out" && ok "  ... B and Big restored, only the changed A (and NoObj) miss" || bad "partial restore: $(cat "$t/out")"
# a tampered per-object entry is rejected by name and the others are still used
f1=$(find "$pc/armobj" -path '*/tree/build/ir/JanusASL/*' -name 'B.c.o.export' | head -1); chmod -R u+w "$(dirname "$f1")"; printf X | dd of="$f1" bs=1 count=1 conv=notrunc 2>/dev/null
copy "$t/pk4"; mkdir -p "$t/pk4/JanusASL/.lake/build/ir/JanusASL"; cp "$t/pj/JanusASL/.lake/build/ir/JanusASL/"*.c "$t/pj/JanusASL/.lake/build/ir/JanusASL/"*.c.hash "$t/pk4/JanusASL/.lake/build/ir/JanusASL/"
expect 0 "objrestore with one tampered entry" M objrestore "$t/pk4" jasl "$pc"
grep -q "2 restored, 1 without entry, 1 rejected" "$t/out" && ok "  ... the tampered one is REJECTED, the rest restored" || bad "tampered per-object: $(cat "$t/out")"

[ $fail = 0 ] && echo "test_asl_obj_cache: all passed" || { echo "test_asl_obj_cache: FAILED"; exit 1; }
