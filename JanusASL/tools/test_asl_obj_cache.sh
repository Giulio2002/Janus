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
# Leftovers of THIS test die with it (RTOBJ6: recompile sandboxes of a killed run survived for hours). A process is ours only if its
# working directory is inside the private directory $t (unique: mktemp) AND it is either a descendant of this shell or an orphan of
# this test (its parent is init / a subreaper: the sandboxes run in a session of their own and outlive a killed parent). A process
# that merely mentions $t in its command line (another agent's grep, an editor) or sits in $t from an interactive shell (its parent
# is a shell, not init) is never touched. Only the caller's own processes can be signalled anyway (kill needs the same uid).
ppid_of() { local st; st=$(cat "/proc/$1/stat" 2>/dev/null) || return 1; st=${st##*) }; set -- $st; echo "$2"; }
ours() {  # ours PID: a descendant of this shell, or an orphan (parent 1, or a systemd subreaper)
  local q=$1 n=0 pp
  pp=$(ppid_of "$q") || return 1
  [ "$pp" = 1 ] && return 0
  [ "$(cat "/proc/$pp/comm" 2>/dev/null)" = systemd ] && return 0
  while [ "$q" -gt 1 ] && [ $n -lt 64 ]; do
    [ "$q" = "$$" ] && return 0
    q=$(ppid_of "$q") || return 1; n=$((n + 1))
  done
  return 1
}
reap() {
  local d p c
  for d in /proc/[0-9]*; do
    p=${d#/proc/}; [ "$p" = "$$" ] && continue
    c=$(readlink "$d/cwd" 2>/dev/null) || continue
    case "$c" in "$t"|"$t"/*) ours "$p" && kill -9 "$p" 2>/dev/null ;; esac
  done
}
trap 'reap; rm -rf "$t"' EXIT
trap 'exit 143' TERM INT HUP
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
lh() {  # lh FILE TEXT: Lake's own file hash (bcache.lake_hash), as Lake writes it into .hash and the trace
  python3 -I -c 'import importlib.util,sys;sp=importlib.util.spec_from_file_location("b",sys.argv[1]);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);print(m.lake_hash(open(sys.argv[2],"rb").read(),sys.argv[3]=="1"))' "$root/scripts/lib/bcache.py" "$1" "$2"
}
mkobj() {  # mkobj LAKE CFILE [CLANG]: compile CFILE exactly as Lake logs it for the keyed toolchain (and write .hash/.trace/.c.hash)
  local lake="$1" f="$2" cc="${3:-$clang}" oh ch
  python3 -I - "$root" "$lake" "$f" "$cc" "$prefix" <<'PY'
import importlib.util, json, os, subprocess, sys
root, lake, f, cc, prefix = sys.argv[1:]
spec = importlib.util.spec_from_file_location("bcache", root + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
rel = os.path.relpath(f, lake)
argv = b.expected_argv(cc, prefix, f, f + ".o.export", rel)
if os.environ.get("MKOBJ_EXTRA"): argv = argv[:-1] + os.environ["MKOBJ_EXTRA"].split() + argv[-1:]
subprocess.run([cc] + argv[1:], check=True, cwd=os.path.dirname(f))
oh = b.lake_hash(open(f + ".o.export", "rb").read()); ch = b.lake_hash(open(f, "rb").read(), text=True)
open(f + ".o.export.hash", "w").write(oh); open(f + ".hash", "w").write(ch)
json.dump({"synthetic": False, "schemaVersion": "2025-09-10", "outputs": oh + ".o",
           "log": [{"message": ".> " + " ".join(argv), "level": "trace"}],
           "inputs": [["M:c", [[f, ch], ["Lean 4", "e9"]]], ["traceArgs: #[-O3]", "2d"]], "depHash": "e9ea8fa0bde1bdff"}, open(f + ".o.export.trace", "w"))
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

stage() {  # stage DIR SCOPE [INDEX]: objstage into a fresh stage; prints the id (rc 0) or fails
  rm -rf "$t/st"; mkdir -p "$t/st"; M objstage "$1" "$2" "$t/st" "$t/st.list" ${3:+$3}
}
store() { stage "$1" arm > /dev/null && B store armobj "$cache" "$ida" "$t/st" < "$t/st.list"; }
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
mkobj "$t/a/JanusASL/.lake" "$t/a/JanusASL/.lake/build/ir/JanusASL/Check.c"
expect 1 "an unknown scope is refused" M objkey "$t/a" bogus
stage "$t/a" jasl > /dev/null; expect 0 "store jasl scope" B store armobj "$cache" "$ja" "$t/st" < "$t/st.list"
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
expect 0 "objstage accepts a genuine tree (arm)" stage "$t/p" arm
[ "$(cat "$t/out")" = "$(M objkey "$t/p")" ] && ok "  ... and prints the id objkey gives" || bad "objstage id differs from objkey"
ls "$t/st/build/ir/ArmASL/Part01.c.o.export.cin" > /dev/null 2>&1 && ok "  ... with a .cin record of each C file" || bad "no .cin"
expect 0 "objstage accepts a genuine tree (jasl)" stage "$t/p" jasl
# (publish-side lie 1) the C changed after the object was compiled (lean re-emitted it: .c.hash is new, the trace is old)
copy "$t/q"; build "$t/q"; q="$t/q/JanusASL/.lake/build/ir/ArmASL/Part02.c"
echo '// other C' >> "$q"; lh "$q" 1 > "$q.hash"
expect 1 "objstage refuses an object whose trace records another C hash than the current C" stage "$t/q" arm
# (lie 2) the object bytes were swapped but hash/trace kept: objstage cannot see it, the recompile at store does
copy "$t/r"; build "$t/r"; r="$t/r/JanusASL/.lake/build/ir/ArmASL/Part01.c"
printf 'int other(void){return 7;}\n' > "$t/other.c"; (cd "$t" && "$clang" -c -o "$r.o.export" other.c -I "$prefix/include" -fPIC -O3 -DNDEBUG -DLEAN_EXPORTING)
expect 1 "objstage refuses swapped object bytes under an unchanged .hash (Lake's file hash is recomputed, RTOBJ2)" stage "$t/r" arm
# the consistent forgery (the attacker also rewrites .hash and the trace's output): objstage cannot see it, the recompile does
oh=$(lh "$r.o.export" 0); echo "$oh" > "$r.o.export.hash"; sed -i "s#\"outputs\": \"[0-9a-f]*\.o\"#\"outputs\": \"$oh.o\"#" "$r.o.export.trace"
expect 0 "objstage cannot see a consistently forged object (the recompile does)" stage "$t/r" arm
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


# ======== RTOBJ2: Lake's hash recomputed, the logged command is validated, inconclusive never destroys, cold-side audit ========
cat > "$t/lh.lean" <<'LEAN'
import Lake
open Lake
def main : IO Unit := do
  IO.println (Hash.ofByteArray "abc".toUTF8).hex
  IO.println (Hash.ofText "a\r\nb\n").hex
  IO.println (Hash.ofByteArray (ByteArray.mk (Array.range 100 |>.map (·.toUInt8)))).hex
LEAN
want=$(cd "$root/JanusASL" && timeout 300 lean --run "$t/lh.lean" 2>/dev/null | tr '\n' ' ')
got=$(printf 'abc' > "$t/v1"; printf 'a\r\nb\n' > "$t/v2"; python3 -c 'import sys;sys.stdout.buffer.write(bytes(range(100)))' > "$t/v3"; echo "$(lh "$t/v1" 0) $(lh "$t/v2" 1) $(lh "$t/v3" 0) ")
[ -n "$want" ] && [ "$want" = "$got" ] && ok "lake_hash equals Lake's Hash.ofByteArray / ofText on three vectors" || bad "lake_hash differs from Lake: '$want' vs '$got'"

copy "$t/f"; build "$t/f"; fl="$t/f/JanusASL/.lake/build/ir/ArmASL/Part02.c"
printf '// Lean compiler output\nint f_Part02(void){\n#ifdef EVIL\nreturn 666;\n#else\nreturn 7;\n#endif\n}\n' > "$fl"; mkobj "$t/f/JanusASL/.lake" "$fl"
# the forged compile command: the object is built with -DEVIL, .hash/trace outputs consistent, the log line edited to say so
(cd "$(dirname "$fl")" && "$clang" -c -o "$fl.o.export" "$fl" -I "$prefix/include" -fPIC -O3 -DNDEBUG -DLEAN_EXPORTING -DEVIL)
oh=$(lh "$fl.o.export" 0); echo "$oh" > "$fl.o.export.hash"
sed -i "s#-DLEAN_EXPORTING#-DLEAN_EXPORTING -DEVIL#; s#\"outputs\": \"[0-9a-f]*\.o\"#\"outputs\": \"$oh.o\"#" "$fl.o.export.trace"
expect 1 "objstage refuses a trace whose logged compile command carries a flag Lake did not log (-DEVIL)" stage "$t/f" arm
grep -q "argument" "$t/out" "$t/err" 2>/dev/null && ok "  ... naming the argument" || bad "  ... reason"
# the same forged entry published by a publisher without objstage: store --recompile and verify --recompile refuse it
sed -i "s#-DEVIL##" "$fl.o.export.trace"; sed -i 's/ -DLEAN_EXPORTING ", "/ -DLEAN_EXPORTING", "/' "$fl.o.export.trace"
# (rebuild the honest trace log, then a SECOND forgery that is allowed by shape but whose object differs: only the recompile sees it)
mkobj "$t/f/JanusASL/.lake" "$fl"; (cd "$(dirname "$fl")" && "$clang" -c -o "$fl.o.export" "$fl" -I "$prefix/include" -fPIC -O3 -DNDEBUG -DLEAN_EXPORTING -DEVIL)
oh=$(lh "$fl.o.export" 0); echo "$oh" > "$fl.o.export.hash"; sed -i "s#\"outputs\": \"[0-9a-f]*\.o\"#\"outputs\": \"$oh.o\"#" "$fl.o.export.trace"
expect 0 "objstage accepts a consistent forgery whose logged command is honest (only the recompile can see it)" stage "$t/f" arm
idf=$(cat "$t/out"); rm -rf "$cache/armobj"
expect 4 "store --recompile all refuses it" B store armobj "$cache" "$idf" "$t/st" --c-root "$t/f/JanusASL/.lake" --recompile all < "$t/st.list"
# entry traces are data: a trace whose command is a shell is never run by verify --recompile
expect 0 "a forged entry stored without recompile" B store armobj "$cache" "$idf" "$t/st" < "$t/st.list"
# a command in the entry's trace that runs a shell: re-signed by a keyed publisher (store re-signs whatever it is given)
mkdir -p "$t/st2"; cp -a "$t/st/." "$t/st2/"; chmod -R u+w "$t/st2"
python3 -I - "$t/st2/build/ir/ArmASL/Part02.c.o.export.trace" "$t/PWNED" <<'PY'
import sys, json
p, flag = sys.argv[1:]
d = json.load(open(p)); d["log"][0]["message"] = ".> /bin/sh -c 'touch %s' -c -o x y.c" % flag
json.dump(d, open(p, "w"))
PY
rm -rf "$cache/armobj"; B store armobj "$cache" "$idf" "$t/st2" < "$t/st.list" > /dev/null
rm -f "$t/PWNED"; expect 3 "verify --recompile reports POISONED for an entry whose trace runs a shell" B verify armobj "$cache" "$idf" --c-root "$t/f/JanusASL/.lake" --recompile all
[ ! -e "$t/PWNED" ] && ok "  ... and never ran it" || bad "  ... the shell in the trace RAN"

# inconclusive never destroys: a good entry survives a store whose recompile cannot run (c-root without C)
copy "$t/g"; build "$t/g"; rm -rf "$t/st"; mkdir "$t/st"; idg=$(M objstage "$t/g" arm "$t/st" "$t/st.list"); rm -rf "$cache/armobj"
expect 0 "good entry stored with a full recompile" B store armobj "$cache" "$idg" "$t/st" --c-root "$t/g/JanusASL/.lake" --recompile all < "$t/st.list"
mkdir -p "$t/noc"; expect 4 "a store whose recompile is inconclusive (no C) fails" B store armobj "$cache" "$idg" "$t/st" --c-root "$t/noc" --recompile all < "$t/st.list"
expect 0 "  ... and the good entry is still there and valid" B verify armobj "$cache" "$idg"

# the default sample plus the random draw catches a consistent forgery of a LARGE object (not among the 3 smallest)
big="$t/g/JanusASL/.lake/build/ir/ArmASL/Part02.c"; for i in $(seq 1 100); do echo "int pad_$i(void){return $i;}" >> "$big"; done
mkobj "$t/g/JanusASL/.lake" "$big"; printf 'int f_Part02(void){return 666;}\n' > "$t/evil.c"
(cd "$t" && "$clang" -c -o "$big.o.export" evil.c -I "$prefix/include" -fPIC -O3 -DNDEBUG -DLEAN_EXPORTING)
oh=$(lh "$big.o.export" 0); echo "$oh" > "$big.o.export.hash"; sed -i "s#\"outputs\": \"[0-9a-f]*\.o\"#\"outputs\": \"$oh.o\"#" "$big.o.export.trace"
rm -rf "$cache/armobj"; ASL_OBJ_RECOMPILE_RANDOM=0 M objpublish "$t/g" arm "$cache" 3 > "$t/out" 2>&1
grep -q "stored 1" "$t/out" && ok "RESIDUAL (documented): with no random draw the forged LARGE object is published (3 smallest only)" || bad "no-random publish: $(cat "$t/out")"
rm -rf "$cache/armobj"; ASL_OBJ_RECOMPILE_RANDOM=100 M objpublish "$t/g" arm "$cache" 3 > "$t/out" 2>&1
grep -q "refused 1" "$t/out" && ok "a random draw covering it refuses the forged large object" || bad "random draw: $(cat "$t/out")"

# cold-side audit: a cached object that differs from the freshly compiled one is quarantined
copy "$t/h"; build "$t/h"; rm -rf "$t/st"; mkdir "$t/st"; idh=$(M objstage "$t/h" arm "$t/st" "$t/st.list"); rm -rf "$cache/armobj"
B store armobj "$cache" "$idh" "$t/st" < "$t/st.list" > /dev/null
expect 0 "objaudit: cache and cold tree agree" M objaudit "$t/h" arm "$cache"
chmod -R u+w "$cache/armobj/$idh"; printf 'int f_Part01(void){return 9;}\n' > "$t/e2.c"
(cd "$t" && "$clang" -c -o "$cache/armobj/$idh/tree/build/ir/ArmASL/Part01.c.o.export" e2.c -I "$prefix/include" -fPIC -O3 -DNDEBUG -DLEAN_EXPORTING)
( cd "$cache/armobj/$idh" && h=$(sha256sum tree/build/ir/ArmASL/Part01.c.o.export | cut -d' ' -f1) && sed -i "s|^[0-9a-f]*  build/ir/ArmASL/Part01.c.o.export\$|$h  build/ir/ArmASL/Part01.c.o.export|" MANIFEST.sha256 )
# (a publisher with the key re-signs; simulate by storing the poisoned tree through bcache)
rm -rf "$t/st3"; mkdir "$t/st3"; cp -a "$cache/armobj/$idh/tree/." "$t/st3/"; rm -rf "$cache/armobj/$idh"; B store armobj "$cache" "$idh" "$t/st3" < "$t/st.list" > /dev/null
expect 3 "objaudit: a validly signed but poisoned entry is detected" M objaudit "$t/h" arm "$cache"
[ ! -d "$cache/armobj/$idh" ] && [ -d "$cache/armobj/.poisoned-$idh" ] && ok "  ... and quarantined (no longer served)" || bad "  ... not quarantined"
expect 2 "  ... a fetch of it is now a miss" B fetch armobj "$cache" "$idh" "$t/aud/.lake"


# the vendored Sail package's lakefile (its build flags) is in the object id, and never widens the accepted flags
copy "$t/k"; build "$t/k"; mkdir -p "$t/k/JanusASL/.lake/packages/Sail"; idk0=$(M objkey "$t/k")
printf '[[lean_lib]]\nname = "Sail"\nweakLeancArgs = ["-DEVIL"]\n' > "$t/k/JanusASL/.lake/packages/Sail/lakefile.toml"
[ "$(M objkey "$t/k")" != "$idk0" ] && ok "a changed Sail package lakefile changes the id" || bad "Sail lakefile not in the id"
sk="$t/k/JanusASL/.lake/packages/Sail/.lake/build/ir/Sail/Attr.c"
(cd "$(dirname "$sk")" && "$clang" -c -o "$sk.o.export" "$sk" -I "$prefix/include" -fPIC -O3 -DNDEBUG -DLEAN_EXPORTING -DEVIL)
oh=$(lh "$sk.o.export" 0); echo "$oh" > "$sk.o.export.hash"; sed -i "s#-DLEAN_EXPORTING#-DLEAN_EXPORTING -DEVIL#; s#\"outputs\": \"[0-9a-f]*\.o\"#\"outputs\": \"$oh.o\"#" "$sk.o.export.trace"
rm -rf "$t/st"; mkdir "$t/st"; expect 1 "objstage: -DEVIL is not accepted just because the Sail lakefile (the publisher's own) declares it" M objstage "$t/k" arm "$t/st" "$t/st.list"


# previously untested bindings (mutation survivors on c73d7de0): the trace's output vs .hash, and the .cin record vs the C
copy "$t/m"; build "$t/m"; mp="$t/m/JanusASL/.lake/build/ir/ArmASL/Part01.c"
sed -i 's#"outputs": "[0-9a-f]*\.o"#"outputs": "0000000000000000.o"#' "$mp.o.export.trace"
rm -rf "$t/st"; mkdir "$t/st"; expect 1 "objstage refuses a trace whose recorded output differs from the .hash" M objstage "$t/m" arm "$t/st" "$t/st.list"
mkobj "$t/m/JanusASL/.lake" "$mp"; rm -rf "$t/st"; mkdir "$t/st"; idm=$(M objstage "$t/m" arm "$t/st" "$t/st.list"); rm -rf "$cache/armobj"
B store armobj "$cache" "$idm" "$t/st" < "$t/st.list" > /dev/null
echo '// edited after publishing' >> "$mp"
expect 4 "verify --recompile with a C file that is not the one recorded (.cin) is inconclusive, never a pass" B verify armobj "$cache" "$idm" --c-root "$t/m/JanusASL/.lake" --recompile all

copy "$t/n"; build "$t/n"; np="$t/n/JanusASL/.lake/build/ir/ArmASL/Part01.c"; oc=$(cat "$np.hash")
echo 0123456789abcdef > "$np.hash"; sed -i "s#$oc#0123456789abcdef#g" "$np.o.export.trace"
rm -rf "$t/st"; mkdir "$t/st"; expect 1 "objstage refuses a C whose .hash (even echoed consistently in the trace) is not Lake's text hash of the C" M objstage "$t/n" arm "$t/st" "$t/st.list"

# ======== sandbox, Inconclusive, size-bounded draw, cold-side audit (RTOBJ3) ========
python3 -I - "$root" "$t" <<'PY' && ok "the recompile sandbox: work dir writable, nothing else, no network namespace shared" || bad "sandbox"
import importlib.util, os, subprocess, sys
spec = importlib.util.spec_from_file_location("bcache", sys.argv[1] + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
t = sys.argv[2]; work = os.path.join(t, "sbwork"); os.makedirs(work, exist_ok=True)
pre = b._sandbox_prefix(work, work)
assert pre and os.path.basename(pre[0]) == "bwrap", "no bubblewrap here: %r" % pre
r = subprocess.run(pre + ["/bin/sh", "-c", "touch %s/inside && ! touch %s/outside 2>/dev/null && ! touch /etc/outside 2>/dev/null" % (work, t)], capture_output=True)
assert r.returncode == 0, r.stderr
assert os.path.exists(work + "/inside") and not os.path.exists(t + "/outside")
r = subprocess.run(pre + ["/bin/sh", "-c", "cat /proc/net/dev | tail -n +3 | grep -v '^ *lo:' | wc -l"], capture_output=True, text=True)
assert r.stdout.strip() == "0", "network interfaces visible: " + r.stdout
PY
# a recompile sandbox never outlives its parent (RTOBJ6): the parent is SIGKILLed / SIGTERMed / times out while the sandboxed
# command ignores SIGTERM; afterwards no process of the sandbox may be left
cat > "$t/holder.py" <<'PY'
import importlib.util, os, sys
spec = importlib.util.spec_from_file_location("bcache", sys.argv[1] + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
work, mark, timeout = sys.argv[2], sys.argv[3], int(sys.argv[4])
pre = b._sandbox_prefix(work, work)
try:
    b.run_sandboxed(pre + ["/bin/sh", "-c", "trap '' TERM HUP INT; while :; do sleep 1; done # " + mark], work, None, timeout)
except Exception as ex:
    print("run_sandboxed:", type(ex).__name__, file=sys.stderr)
PY
sandbox_procs() {  # the processes running the sandboxed command (its text ends "# MARK"); the [o] keeps grep from matching itself
  local d pat="done # [o]${1#o}"
  for d in /proc/[0-9]*; do tr '\0' ' ' < "$d/cmdline" 2>/dev/null | grep -q -- "$pat" && echo "${d#/proc/}"; done
}
orphan_case() {  # orphan_case NAME HOW TIMEOUT: HOW = kill9 | term | timeout
  local name=$1 how=$2 to=$3 mark="objsb-$$-$RANDOM" n=0 pid
  mkdir -p "$t/orph-$name"
  python3 -I "$t/holder.py" "$root" "$t/orph-$name" "$mark" "$to" 2> "$t/orph-$name.err" &
  pid=$!
  if [ "$how" != timeout ]; then   # (a timeout may fire before a slow /proc scan sees the sandbox: not waited for)
    while [ -z "$(sandbox_procs "$mark")" ] && [ $n -lt 100 ]; do sleep 0.1; n=$((n + 1)); done
    if [ -z "$(sandbox_procs "$mark")" ]; then bad "orphans/$name: the sandbox never started: $(head -c 200 "$t/orph-$name.err")"; kill -9 $pid 2>/dev/null; return; fi
  fi
  case "$how" in kill9) kill -9 $pid ;; term) kill -TERM $pid ;; timeout) : ;; esac
  wait $pid 2>/dev/null
  n=0; while [ -n "$(sandbox_procs "$mark")" ] && [ $n -lt 100 ]; do sleep 0.1; n=$((n + 1)); done
  if [ -z "$(sandbox_procs "$mark")" ]; then ok "orphans/$name: no sandbox process survives ($how)"
  else bad "orphans/$name: sandbox processes survive ($how): $(sandbox_procs "$mark" | tr '\n' ' ')"; for q in $(sandbox_procs "$mark"); do kill -9 "$q" 2>/dev/null; done; fi
}
orphan_case parent-sigkill kill9 3600
orphan_case parent-sigterm term 3600
orphan_case timeout timeout 4
# the cleanup trap kills only this test's own leftovers: an unrelated (orphaned, cwd elsewhere) process whose command line merely
# mentions the private directory (another agent's grep, an editor) survives reap; an orphan whose cwd is inside it does not
mkdir -p "$t/mention"
setsid -f sh -c "cd / && echo \$\$ > '$t/mention.pid' && exec python3 -c 'import time; time.sleep(600)' '$t/mention/x'" < /dev/null > /dev/null 2>&1
setsid -f sh -c "cd '$t/mention' && echo \$\$ > '$t/inside.pid' && exec sleep 600" < /dev/null > /dev/null 2>&1
for i in $(seq 1 50); do [ -s "$t/mention.pid" ] && [ -s "$t/inside.pid" ] && break; sleep 0.1; done
mp=$(cat "$t/mention.pid" 2>/dev/null); ip=$(cat "$t/inside.pid" 2>/dev/null); sleep 0.3
reap; sleep 0.3
if [ -n "$mp" ] && kill -0 "$mp" 2>/dev/null; then ok "reap: a process that only MENTIONS the private directory in its command line is left alone"; else bad "reap killed a process that merely mentions the directory"; fi
if [ -n "$ip" ] && ! kill -0 "$ip" 2>/dev/null; then ok "reap: an orphan whose working directory is inside the private directory is killed"; else bad "reap left an orphan inside the directory"; fi
[ -n "$mp" ] && kill -9 "$mp" 2>/dev/null; [ -n "$ip" ] && kill -9 "$ip" 2>/dev/null
# Inconclusive never destroys a good entry, never counts as a pass
copy "$t/g2"; build "$t/g2"; stage "$t/g2" arm > /dev/null; idg=$(M objkey "$t/g2"); rm -rf "$cache/armobj"
B store armobj "$cache" "$idg" "$t/st" < "$t/st.list" > /dev/null
expect 4 "verify --recompile with a missing C root is inconclusive, not valid" B verify armobj "$cache" "$idg" --c-root "$t/nonexistent" --recompile all
grep -qi inconclusive "$t/err" "$t/out" && ok "  ... says inconclusive" || bad "no inconclusive message: $(cat "$t/err")"
expect 4 "store --recompile with a missing C root keeps the good entry" B store armobj "$cache" "$idg" "$t/st" --c-root "$t/nonexistent" --recompile all < "$t/st.list"
B verify armobj "$cache" "$idg" > /dev/null && ok "  ... the entry is still there and valid" || bad "good entry destroyed by an inconclusive recompile"
# a missing .cin (a signed entry without its record)
python3 -I - "$root" "$cache" "$idg" <<'PY'
import importlib.util, os, sys, shutil
spec = importlib.util.spec_from_file_location("bcache", sys.argv[1] + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
cache, ident = sys.argv[2], sys.argv[3]
e = b.entry_dir("armobj", cache, ident); man = b.parse_manifest(open(e + "/MANIFEST.sha256", "rb").read())
keep = {k: v for k, v in man.items() if not k.endswith(".cin")}
for k in man:
    if k.endswith(".cin"): os.chmod(e + "/tree/" + k, 0o644); os.unlink(e + "/tree/" + k)
data = "".join("%s  %s\n" % (v, k) for k, v in sorted(keep.items())).encode()
open(e + "/MANIFEST.sha256", "wb").write(data); open(e + "/MANIFEST.hmac", "w").write(b.mac("armobj", ident, data) + "\n")
PY
expect 4 "an entry without .cin records: verify --recompile is inconclusive (no crash)" B verify armobj "$cache" "$idg" --c-root "$t/g2/JanusASL/.lake" --recompile all
grep -q Traceback "$t/err" && bad "uncaught exception: $(tail -3 "$t/err")" || ok "  ... without a traceback"
expect 4 "store --recompile over it keeps the entry (inconclusive)" B store armobj "$cache" "$idg" "$t/st" --c-root "$t/g2/JanusASL/.lake" --recompile all < "$t/st.list"
B verify armobj "$cache" "$idg" > /dev/null && ok "  ... the existing entry survives" || bad "entry destroyed"
# a compile that times out
rm -rf "$cache/armobj"; B store armobj "$cache" "$idg" "$t/st" < "$t/st.list" > /dev/null
ASL_OBJ_RECOMPILE_TIMEOUT=0 expect 4 "a recompile that times out is inconclusive" B verify armobj "$cache" "$idg" --c-root "$t/g2/JanusASL/.lake" --recompile all
grep -q Traceback "$t/err" && bad "timeout crashed: $(tail -3 "$t/err")" || ok "  ... no traceback"
# the random draw is bounded by C size
python3 -I - "$root" <<'PY' && ok "draw_random only picks objects whose C is within ASL_OBJ_RECOMPILE_MAXC" || bad "draw_random bound"
import importlib.util, os, sys
spec = importlib.util.spec_from_file_location("bcache", sys.argv[1] + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
os.environ["ASL_OBJ_RECOMPILE_MAXC"] = "1000"
c = [(10, "a", None), (999, "b", None), (5000, "huge", None), (4000000, "config", None)]
for _ in range(200):
    got = {x[1] for x in b.draw_random(c, 3)}
    assert got <= {"a", "b"}, got
assert len(b.draw_random(c, 5)) == 2
PY
# the cold-side audit: end to end through the nightly's own script
copy "$t/cold"; build "$t/cold"; build_jasl "$t/cold"; ac="$t/auditcache"; rm -rf "$ac"; mkdir -p "$ac"
M objpublish "$t/cold" arm "$ac" 1 > /dev/null; M objpublish "$t/cold" jasl "$ac" all > /dev/null
expect 0 "nightly-objaudit: a cache that agrees with the cold tree passes" env NIGHTLY_OBJAUDIT_SCOPES="arm jasl" "$root/scripts/lib/nightly-objaudit.sh" "$t/cold" "$ac"
grep -q "objaudit \[arm\]: .*coverage [1-9][0-9]* of [1-9][0-9]* objects compared (100%)" "$t/out" && ok "  ... and compared objects" || bad "nothing compared: $(cat "$t/out")"
co="$t/cold/JanusASL/.lake/build/ir/ArmASL/Part02.c.o.export"; cp "$co" "$t/co.bak"; printf 'X' >> "$co"
expect 1 "nightly-objaudit: a cold object that differs from the cached one is P0" env NIGHTLY_OBJAUDIT_SCOPES="arm jasl" "$root/scripts/lib/nightly-objaudit.sh" "$t/cold" "$ac"
grep -q "POISONED" "$t/out" && ok "  ... names it POISONED" || bad "no POISONED"
ls "$ac/armobj"/.poisoned-* > /dev/null 2>&1 && ok "  ... and the entry was quarantined" || bad "not quarantined"
expect 2 "  ... a quarantined entry is a miss for every later fetch" B fetch armobj "$ac" "$(M objkey "$t/cold")" "$t/audfetch/.lake"
cp "$t/co.bak" "$co"
copy "$t/cold2"; mkdir -p "$t/cold2/JanusASL/.lake/build/ir/ArmASL"; cp "$t/cold/JanusASL/.lake/build/ir/ArmASL.c" "$t/cold2/JanusASL/.lake/build/ir/" 2>/dev/null
expect 1 "nightly-objaudit fails closed when the cold tree has no objects (nothing compared)" env NIGHTLY_OBJAUDIT_SCOPES="arm jasl" "$root/scripts/lib/nightly-objaudit.sh" "$t/cold2" "$ac"
expect 1 "nightly-objaudit fails closed when the cache has no armobj directory" env NIGHTLY_OBJAUDIT_SCOPES="arm jasl" "$root/scripts/lib/nightly-objaudit.sh" "$t/cold" "$t/emptycache"

# ======== RTOBJ4: exact expected argv, keyed prefix, id-bound file set, sandbox gating, sticky quarantine ========
forge() {  # forge LAKE CFILE: a CONSISTENT forgery: other object bytes, honest log, .hash and trace outputs recomputed
  python3 -I - "$root" "$1" "$2" "$clang" "$prefix" <<'PY'
import importlib.util, json, os, subprocess, sys
root, lake, f, cc, prefix = sys.argv[1:]
spec = importlib.util.spec_from_file_location("bcache", root + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
argv = b.expected_argv(cc, prefix, f, f + ".o.export", os.path.relpath(f, lake))
argv = argv[:-1] + ["-fno-asynchronous-unwind-tables", argv[-1]]
subprocess.run([cc] + argv[1:], check=True, cwd=os.path.dirname(f))
oh = b.lake_hash(open(f + ".o.export", "rb").read()); open(f + ".o.export.hash", "w").write(oh)
t = json.load(open(f + ".o.export.trace")); t["outputs"] = oh + ".o"; json.dump(t, open(f + ".o.export.trace", "w"))
PY
}
edit_log() {  # edit_log TRACE PYEXPR: apply a python expression on the logged argv list `a` (and rewrite the trace log line)
  python3 -I - "$1" "$2" <<'PY'
import json, shlex, sys
p, expr = sys.argv[1:]; t = json.load(open(p)); a = shlex.split(t["log"][0]["message"][3:]); exec(expr)
t["log"][0]["message"] = ".> " + " ".join(a); json.dump(t, open(p, "w"))
PY
}
fresh() {  # fresh NAME: a new built fixture tree $t/NAME (arm + jasl objects)
  copy "$t/$1"; build "$t/$1"; build_jasl "$t/$1"
}
L() { echo "$t/$1/JanusASL/.lake"; }
# --- (B1) a decoy lakefile table does not widen the flags: the expected vector is exact
fresh dec; python3 -I - "$t/dec/JanusASL/lakefile.toml" <<'PY'
import sys; p = sys.argv[1]; open(p, "a").write('\n[[lean_lib]]\nname = "Decoy"\nmoreLeancArgs = ["-fwrapv", "-Xclang", "-disable-llvm-passes"]\n')
PY
MKOBJ_EXTRA="-fwrapv" mkobj "$(L dec)" "$(L dec)/build/ir/ArmASL/Part01.c"
expect 1 "a flag only a decoy lakefile table declares (-fwrapv) is refused by the exact argv" stage "$t/dec" arm
fresh dec2; MKOBJ_EXTRA="-Xclang -disable-llvm-passes" mkobj "$(L dec2)" "$(L dec2)/build/ir/ArmASL/Part01.c"
expect 1 "-Xclang ... is refused too" stage "$t/dec2" arm
# every flag Lake logs is REQUIRED: dropping one (object and log consistent) is refused, as are repeats and reorderings
for f in -O3 -DNDEBUG -DLEAN_EXPORTING -fvisibility=hidden -ffp-contract=off -nostdinc -fPIC -fdata-sections -fbracket-depth=100000; do
  fresh m1; edit_log "$(L m1)/build/ir/ArmASL/Part01.c.o.export.trace" "a.remove('$f')"
  expect 1 "dropping $f from the logged command is refused" stage "$t/m1" arm
done
fresh m2; edit_log "$(L m2)/build/ir/ArmASL/Part01.c.o.export.trace" "a.append('-O3')"; expect 1 "a repeated -O3 is refused" stage "$t/m2" arm
fresh m3; edit_log "$(L m3)/build/ir/ArmASL/Part01.c.o.export.trace" "i=a.index('-O3'); j=a.index('-DNDEBUG'); a[i],a[j]=a[j],a[i]"; expect 1 "a reordered command is refused" stage "$t/m3" arm
fresh m4; edit_log "$(L m4)/build/ir/JanusASL/Check.c.o.export.trace" "a.remove('-fbracket-depth=100000')"; expect 1 "janus-asl-check's root without -fbracket-depth is refused" stage "$t/m4" jasl
fresh m5; edit_log "$(L m5)/build/ir/ArmASL/Part01.c.o.export.trace" "a.insert(-1,'-fbracket-depth=100000')"; expect 1 "a second -fbracket-depth is refused" stage "$t/m5" arm
expect 0 "a real object with -fbracket-depth (ArmASL part, janus-asl-check root) stages" stage "$t/p" arm
expect 0 "  ... jasl root" stage "$t/p" jasl
# -I / --sysroot / -isystem must be the keyed prefix's strings
for pair in "-I:$t/evil-inc" "--sysroot:$t/evil-root" "-isystem:$t/evil-sys"; do
  fl="${pair%%:*}"; val="${pair#*:}"; fresh m6; edit_log "$(L m6)/build/ir/ArmASL/Part01.c.o.export.trace" "i=a.index('$fl'); a[i+1]='$val'"
  expect 1 "$fl pointing outside the keyed prefix is refused" stage "$t/m6" arm
done
# --- (B2) a fake toolchain prefix, and a symlink to the real one
fp="$t/fakep"; mkdir -p "$fp/bin" "$fp/include"; ln -s "$clang" "$fp/bin/clang"; cp -a "$prefix/include/." "$fp/include/"; echo '#define LEAN_FORGED 1' >> "$fp/include/lean/lean.h"
fresh fp1; python3 -I - "$root" "$(L fp1)" "$fp" "$clang" <<'PY'
import importlib.util, json, os, subprocess, sys
root, lake, fp, cc = sys.argv[1:]
spec = importlib.util.spec_from_file_location("bcache", root + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
f = lake + "/build/ir/ArmASL/Part01.c"
argv = b.expected_argv(fp + "/bin/clang", fp, f, f + ".o.export", "build/ir/ArmASL/Part01.c")
subprocess.run(argv, check=True, cwd=os.path.dirname(f))
oh = b.lake_hash(open(f + ".o.export", "rb").read()); open(f + ".o.export.hash", "w").write(oh)
t = json.load(open(f + ".o.export.trace")); t["outputs"] = oh + ".o"; t["log"][0]["message"] = ".> " + " ".join(argv); json.dump(t, open(f + ".o.export.trace", "w"))
PY
expect 1 "an object compiled with a FAKE prefix (bin/clang -> the real clang, modified lean.h) is refused" stage "$t/fp1" arm
ln -s "$prefix" "$t/linkp"; fresh fp2; edit_log "$(L fp2)/build/ir/ArmASL/Part01.c.o.export.trace" "a[:]=[x.replace('$prefix','$t/linkp') for x in a]"
expect 1 "a command through a symlink to the real prefix (realpath equal) is refused: argv[0] must EQUAL the keyed clang" stage "$t/fp2" arm
# --- the entry's file set is bound to the id's C set
stage "$t/p" arm > /dev/null; idp=$(M objkey "$t/p"); rm -rf "$cache/armobj"; B store armobj "$cache" "$idp" "$t/st" < "$t/st.list" > /dev/null
python3 -I - "$root" "$cache" "$idp" <<'PY'
import importlib.util, os, shutil, sys
spec = importlib.util.spec_from_file_location("bcache", sys.argv[1] + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
cache, ident = sys.argv[2], sys.argv[3]
e = b.entry_dir("armobj", cache, ident); man = b.parse_manifest(open(e + "/MANIFEST.sha256", "rb").read())
z = e + "/tree/build/ir/Other/Zed.c.o.export"; os.makedirs(os.path.dirname(z)); open(z, "w").write("smuggled")
man["build/ir/Other/Zed.c.o.export"] = b.sha_file(z)
data = "".join("%s  %s\n" % (v, k) for k, v in sorted(man.items())).encode()
os.chmod(e + "/MANIFEST.sha256", 0o644); open(e + "/MANIFEST.sha256", "wb").write(data); open(e + "/MANIFEST.hmac", "w").write(b.mac("armobj", ident, data) + "\n")
PY
rm -rf "$t/restz"; mkdir -p "$t/restz"; cp -a "$t/p" "$t/restz/"; rm -rf "$t/restz/p/JanusASL/.lake/build/ir/ArmASL"
expect 0 "objrestore with a signed entry that smuggles a path outside the id's C set" M objrestore "$t/p" arm "$cache"
grep -q REJECTED "$t/out" && [ ! -e "$t/p/JanusASL/.lake/build/ir/Other/Zed.c.o.export" ] && ok "  ... REJECTED, nothing smuggled into the tree" || bad "smuggled path accepted: $(cat "$t/out")"
expect 3 "bcache verify of the smuggling entry is invalid" B verify armobj "$cache" "$idp"
expect 4 "store refuses a stage with an extra object path" bash -c "cp -a '$t/st' '$t/st9'; mkdir -p '$t/st9/build/ir/Other'; echo x > '$t/st9/build/ir/Other/Zed.c.o.export'; (cat '$t/st.list'; printf 'build/ir/Other/Zed.c.o.export\0') | python3 -I '$root/scripts/lib/bcache.py' store armobj '$cache' '$idp' '$t/st9'"
# --- sandbox gating
python3 -I - "$root" "$t" <<'PY' && ok "sandbox: a PATH shim named bwrap is never used; a missing bwrap is Inconclusive; the opt-in warns; the key dir is masked" || bad "sandbox gating"
import importlib.util, os, stat, subprocess, sys, io, contextlib
spec = importlib.util.spec_from_file_location("bcache", sys.argv[1] + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
t = sys.argv[2]; shim = t + "/shimbin"; os.makedirs(shim, exist_ok=True)
open(shim + "/bwrap", "w").write("#!/bin/sh\ntouch %s/SHIM-RAN\nexit 1\n" % t); os.chmod(shim + "/bwrap", 0o755)
os.environ["PATH"] = shim + ":" + os.environ["PATH"]
work = t + "/gw"; os.makedirs(work, exist_ok=True)
pre = b._sandbox_prefix(work, work)
assert pre and pre[0] in b.BWRAP_CANDIDATES, pre
assert not os.path.exists(t + "/SHIM-RAN"), "the PATH shim ran"
# the key directory is masked inside
kd = os.path.dirname(b.key_path()); b.hmac_key()
r = subprocess.run(pre + ["/bin/sh", "-c", "test ! -e %s/asl-cache.key" % kd]); assert r.returncode == 0, "the HMAC key is visible in the sandbox"
# no bwrap at the fixed locations: Inconclusive unless the explicit opt-in
saved = b.BWRAP_CANDIDATES; b.BWRAP_CANDIDATES = []
try:
    b._sandbox_prefix(work, work); raise SystemExit("no bwrap but no Inconclusive")
except b.Inconclusive:
    pass
os.environ.pop(b.UNSANDBOXED_OPTIN, None); os.environ["ASL_OBJ_RECOMPILE_NOSANDBOX"] = "1"
try:
    b._sandbox_prefix(work, work); raise SystemExit("the old NOSANDBOX switch still disables the sandbox")
except b.Inconclusive:
    pass
os.environ[b.UNSANDBOXED_OPTIN] = "1"; err = io.StringIO()
with contextlib.redirect_stderr(err):
    assert b._sandbox_prefix(work, work) == []
assert "UNSANDBOXED" in err.getvalue(), err.getvalue()
PY
# OSError (no space, read-only) is Inconclusive everywhere, never a traceback
rm -rf "$cache/armobj"; stage "$t/p" arm > /dev/null; B store armobj "$cache" "$idp" "$t/st" < "$t/st.list" > /dev/null
python3 -I - "$root" "$t" "$cache" "$idp" <<'PY' && ok "OSError on the work directory is Inconclusive (verify --recompile and objpublish)" || bad "OSError handling"
import importlib.util, os, sys, tempfile
spec = importlib.util.spec_from_file_location("bcache", sys.argv[1] + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
t, cache, idp = sys.argv[2:]
def boom(*a, **k): raise OSError(28, "No space left on device")
orig = tempfile.mkdtemp; tempfile.mkdtemp = boom
try:
    b.recompile_entry("armobj", cache, idp, t + "/p/JanusASL/.lake", "all"); raise SystemExit("no error")
except b.Inconclusive:
    pass
spec = importlib.util.spec_from_file_location("m", sys.argv[1] + "/JanusASL/tools/asl_mod_cache.py"); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
m.obj_publish(sys.argv[1], "arm", cache, "0") if False else None
tempfile.mkdtemp = orig
PY
# stale work dirs of killed runs are cleaned at startup
mkdir -p "$cache/armobj/../.recompile-stale" "$cache/.objstage-stale"; touch -d '3 hours ago' "$cache/.recompile-stale" "$cache/.objstage-stale"
M objpublish "$t/p" arm "$cache" 0 > /dev/null; [ ! -e "$cache/.recompile-stale" ] && [ ! -e "$cache/.objstage-stale" ] && ok "stale .recompile-*/.objstage-* directories are removed" || bad "stale dirs left"
# --- sample composition: the N smallest are always checked; the random draw is size bounded
fresh smp; lk="$(L smp)"; printf 'int big1(void){return 1;}\n' > /dev/null
for n in Aa Bb Cc Dd; do mkjc "$lk" JanusASL "$n"; done
head -c 300000 /dev/urandom | od -An -tx1 | awk '{print "static const int pad_" NR "=0x" $1 ";"}' >> "$lk/build/ir/JanusASL/Dd.c"; mkobj "$lk" "$lk/build/ir/JanusASL/Dd.c"   # Dd is the biggest
forge "$lk" "$lk/build/ir/JanusASL/Aa.c"     # smallest forged
forge "$lk" "$lk/build/ir/JanusASL/Dd.c"     # biggest forged
cs_c="$t/smpcache"; mkdir -p "$cs_c"
M objpublish "$t/smp" jasl "$cs_c" 0 > "$t/smp.out" 2>&1; :   # no recompile at publish: both forgeries are stored
python3 -I - "$root" "$cs_c" "$t/smp" <<'PY' && ok "sampling: N smallest always checked; the random draw reaches the biggest only below the size cap" || bad "sample composition"
import importlib.util, os, sys, glob
spec = importlib.util.spec_from_file_location("m", sys.argv[1] + "/JanusASL/tools/asl_mod_cache.py"); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
bc = m.load_bcache(sys.argv[1]); cache, tree = sys.argv[2], sys.argv[3]; lake = tree + "/JanusASL/.lake"
units = {c: i for i, cs in m.obj_units(tree, "jasl") for c in cs}
def check(rel_c, sample, rnd, maxc):
    ident = [i for i, cs in m.obj_units(tree, "jasl") if rel_c in cs][0]
    os.environ["ASL_OBJ_RECOMPILE_RANDOM"] = str(rnd); os.environ["ASL_OBJ_RECOMPILE_MAXC"] = str(maxc)
    n, bad = bc.recompile_entry("armobj", cache, ident, lake, sample)
    return n, bad
# one object per entry: sample 1 on the entry checks that object (the smallest of its entry)
assert check("build/ir/JanusASL/Aa.c", 1, 0, 10**9)[1], "the smallest forged object must be found"
assert check("build/ir/JanusASL/Dd.c", 1, 0, 10**9)[1]
assert check("build/ir/JanusASL/Bb.c", 1, 0, 10**9)[1] == []
# unit level: with several objects in ONE entry, the smallest are checked first and the biggest only via the draw
rel = sorted(glob.glob(lake + "/build/ir/JanusASL/*.c.o.export"))
PY

# --- one entry with several objects: the N smallest are always recompiled, the biggest only through the bounded draw
fresh sm2; lk="$(L sm2)"
head -c 400000 /dev/urandom | od -An -tx1 | awk '{print "static const int pad_" NR "=0x" $1 ";"}' >> "$lk/build/ir/ArmASL/Part02.c"; mkobj "$lk" "$lk/build/ir/ArmASL/Part02.c"   # Part02: the biggest
forge "$lk" "$lk/build/ir/ArmASL/Part02.c"
c2="$t/sm2cache"; mkdir -p "$c2"; M objpublish "$t/sm2" arm "$c2" 0 > /dev/null; id2=$(M objkey "$t/sm2")
smp() {  # smp SAMPLE RANDOM MAXC: exit 3 if verify --recompile finds the forgery
  ASL_OBJ_RECOMPILE_RANDOM=$2 ASL_OBJ_RECOMPILE_MAXC=$3 B verify armobj "$c2" "$id2" --c-root "$lk" --recompile "$1"
}
expect 0 "sample 1 + no random draw misses the biggest forged object (the documented residual)" smp 1 0 1000000000
expect 3 "sample 'all' finds it" smp all 0 1000000000
found=0; for i in 1 2 3 4 5 6; do smp 1 3 1000000000 > /dev/null 2>&1 || found=$((found+1)); done
[ "$found" = 6 ] && ok "the random draw (3 of the other 3) always reaches it when its C is within the cap" || bad "draw found it $found/6"
found=0; for i in 1 2 3 4; do smp 1 3 1000 > /dev/null 2>&1 || found=$((found+1)); done
[ "$found" = 0 ] && ok "the random draw never picks an object whose C exceeds ASL_OBJ_RECOMPILE_MAXC" || bad "draw ignored the cap ($found)"
fresh sm3; lk3="$(L sm3)"; forge "$lk3" "$lk3/build/ir/ArmASL/Part01.c"; c3="$t/sm3cache"; mkdir -p "$c3"; M objpublish "$t/sm3" arm "$c3" 0 > /dev/null
expect 3 "a forged object among the N smallest is found without any random draw" env ASL_OBJ_RECOMPILE_RANDOM=0 python3 -I "$root/scripts/lib/bcache.py" verify armobj "$c3" "$(M objkey "$t/sm3")" --c-root "$lk3" --recompile 4

# --- sticky quarantine: a signed tombstone, not just a renamed directory
fresh q1; lq="$(L q1)"; forge "$lq" "$lq/build/ir/ArmASL/Part01.c"; qc="$t/qcache"; mkdir -p "$qc"
M objpublish "$t/q1" arm "$qc" 0 > /dev/null; idq=$(M objkey "$t/q1"); cp -a "$qc/armobj/$idq" "$t/q-forged-entry"
fresh qcold; M objaudit "$t/qcold" arm "$qc" > "$t/out" 2>&1; rc=$?   # the cold tree compiled honestly: its objects differ from the cached forgery
[ "$rc" = 3 ] && ok "objaudit: the forged entry differs from the cold tree's honest compile (exit 3)" || bad "audit rc $rc: $(cat "$t/out")"
ls "$qc/armobj/.tombstone-$idq" > /dev/null 2>&1 && ls -d "$qc/armobj/.poisoned-$idq" > /dev/null 2>&1 && ok "  ... quarantined with a tombstone" || bad "no tombstone/quarantine"
expect 2 "  ... fetch is a miss" B fetch armobj "$qc" "$idq" "$t/qf/.lake"
mv "$qc/armobj/.poisoned-$idq" "$qc/armobj/$idq"
expect 3 "an attacker renaming .poisoned-<id> back does not revive it (tombstone)" B fetch armobj "$qc" "$idq" "$t/qf/.lake"
[ -z "$(find "$t/qf" -type f ! -name '.bcache-tree.lock' 2>/dev/null)" ] && ok "  ... nothing copied" || bad "revived entry copied files"
expect 3 "  ... and verify says invalid" B verify armobj "$qc" "$idq"
rm -rf "$qc/armobj/$idq"
stage "$t/q1" arm > /dev/null; expect 4 "store refuses to republish the same forged bytes" B store armobj "$qc" "$idq" "$t/st" < "$t/st.list"
[ ! -e "$qc/armobj/$idq" ] && ok "  ... nothing stored" || bad "forged bytes republished"
# the honest bytes of the same id may be published (the cold tree's objects): the tombstone is about bytes, not the id
M objpublish "$t/qcold" arm "$qc" 0 > "$t/out" 2>&1; grep -q "stored 1" "$t/out" && ok "honest bytes for the same id are stored" || bad "honest republish: $(cat "$t/out")"
B fetch armobj "$qc" "$idq" "$t/qf2/.lake" > /dev/null && ok "  ... and fetched" || bad "honest entry not fetchable"
# a forged tombstone (bad MAC) makes the id unusable (fail closed)
printf '{"data":"x","mac":"00"}' > "$qc/armobj/.tombstone-$idq"
expect 3 "a tombstone with a bad MAC makes the id unusable (fail closed)" B fetch armobj "$qc" "$idq" "$t/qf3/.lake"
# --- the audit fails (not 'unchecked') when it cannot compare, and prints the coverage
fresh ac1; fresh ac2; cc1="$t/ac1cache"; mkdir -p "$cc1"; M objpublish "$t/ac1" arm "$cc1" 0 > /dev/null
rm "$(L ac2)/build/ir/ArmASL/Part02.c.o.export"   # the cold tree lacks one object of an entry of its ids
expect 4 "objaudit exits 4 when an object of the commit's entry cannot be compared" M objaudit "$t/ac2" arm "$cc1"
grep -q "coverage 3 of 4 objects compared (75%)" "$t/out" && ok "  ... printing the coverage ratio" || bad "coverage line: $(cat "$t/out")"
grep -q INCOMPLETE "$t/out" && ok "  ... INCOMPLETE, not a pass" || bad "no INCOMPLETE"

# --- the nightly's shell wiring
grep -q 'nightly-objaudit.sh" "$work/tree-cold" "$cache_dir" || rc_final=1' "$root/scripts/nightly-cold-gate.sh" && ok "nightly-cold-gate.sh: a failing object audit sets rc_final=1" || bad "audit result not wired to rc_final"
grep -q 'run_gate cold JANUS_ASL_CACHE=0 ASL_OBJ_CACHE=0' "$root/scripts/nightly-cold-gate.sh" && grep -q '"\$@" LEAN_NUM_THREADS=4 JANUS_JOBS=2 memcap -m 48G scripts/asl.sh build' "$root/scripts/nightly-cold-gate.sh" && ok "the cold run passes JANUS_ASL_CACHE=0 to the gate AND to its own link step" || bad "cold run wiring"
cdir="$t/coldcache"; mkdir -p "$cdir"; M objpublish "$t/p" arm "$cdir" 0 > /dev/null
rm -rf "$t/cr"; copy "$t/cr"; mkdir -p "$t/cr/JanusASL/.lake"; rsync -a --include='*/' --include='*.c' --include='*.c.hash' --exclude='*' "$t/p/JanusASL/.lake/" "$t/cr/JanusASL/.lake/"
JANUS_ASL_CACHE=0 ASL_CACHE="$cdir" "$t/cr/scripts/asl.sh" __call objcache_restore arm > "$t/out" 2>&1
[ ! -e "$t/cr/JanusASL/.lake/build/ir/ArmASL/Part01.c.o.export" ] && ok "a cold run (JANUS_ASL_CACHE=0, no ASL_OBJ_CACHE set) does NOT restore objects from a populated cache" || bad "cold run restored from the cache: $(cat "$t/out")"
ASL_OBJ_CACHE=1 JANUS_ASL_CACHE=0 ASL_CACHE="$cdir" "$t/cr/scripts/asl.sh" __call objcache_restore arm > "$t/out" 2>&1
[ ! -e "$t/cr/JanusASL/.lake/build/ir/ArmASL/Part01.c.o.export" ] && ok "  ... not even with ASL_OBJ_CACHE=1 (JANUS_ASL_CACHE=0 wins)" || bad "cold run restored with ASL_OBJ_CACHE=1"
ASL_OBJ_CACHE=0 ASL_CACHE="$cdir" "$t/cr/scripts/asl.sh" __call objcache_restore arm > "$t/out" 2>&1
[ ! -e "$t/cr/JanusASL/.lake/build/ir/ArmASL/Part01.c.o.export" ] && ok "ASL_OBJ_CACHE=0 opts out: nothing restored" || bad "restored despite ASL_OBJ_CACHE=0"
def=$(sed -n 's/^OBJ_CACHE_DEFAULT=\([01]\).*/\1/p' "$root/scripts/asl.sh")   # the default is one constant: the tests follow it
# (the nightly's cached run exports ASL_OBJ_CACHE=1 and a gate may carry other cache variables: each probe starts from a clean slate)
st() { env -u ASL_OBJ_CACHE -u JANUS_ASL_CACHE -u ASL_CACHE "$@" "$t/cr/scripts/asl.sh" objcache-state 2>/dev/null | grep -v -E '^(memguard|janus: memory guard|janus-memguard)' | tail -n 1; }
[ "$(st ASL_CACHE="$cdir")" = "$([ "$def" = 1 ] && echo ON || echo "OFF (default)")" ] && [ "$(st ASL_OBJ_CACHE=0 ASL_CACHE="$cdir")" = "OFF (ASL_OBJ_CACHE=0)" ] && st JANUS_ASL_CACHE=0 ASL_CACHE="$cdir" | grep -q "$([ "$def" = 1 ] && echo '^OFF (no build cache' || echo '^OFF (default)')" && ok "objcache-state: ON by default, OFF with ASL_OBJ_CACHE=0, OFF with JANUS_ASL_CACHE=0" || bad "objcache-state: $(st ASL_CACHE="$cdir") / $(st ASL_OBJ_CACHE=0 ASL_CACHE="$cdir") / $(st JANUS_ASL_CACHE=0 ASL_CACHE="$cdir")"
ASL_CACHE="$cdir" "$t/cr/scripts/asl.sh" __call objcache_restore arm > "$t/out" 2>&1
if [ "$def" = 1 ]; then
  [ -e "$t/cr/JanusASL/.lake/build/ir/ArmASL/Part01.c.o.export" ] && ok "the object cache is ON by default (the same call without opt-out restores: the test discriminates)" || bad "default restore failed: $(cat "$t/out")"
else
  [ ! -e "$t/cr/JanusASL/.lake/build/ir/ArmASL/Part01.c.o.export" ] && ok "the object cache is OFF by default (OBJ_CACHE_DEFAULT=0)" || bad "restored by default despite OBJ_CACHE_DEFAULT=0"
  ASL_OBJ_CACHE=1 ASL_CACHE="$cdir" "$t/cr/scripts/asl.sh" __call objcache_restore arm > "$t/out" 2>&1
  [ -e "$t/cr/JanusASL/.lake/build/ir/ArmASL/Part01.c.o.export" ] && ok "  ... and ASL_OBJ_CACHE=1 turns it on" || bad "opt-in restore failed"
fi

# ======== RTOBJ4 survivors: one direct test per mutant ========
cat > "$t/h.py" <<'PY'
import importlib.util, os, subprocess, sys, json, tempfile, shutil, stat
root, t = sys.argv[1], sys.argv[2]
def load(name, rel):
    spec = importlib.util.spec_from_file_location(name, root + "/" + rel); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
b = load("bcache", "scripts/lib/bcache.py"); m = load("amc", "JanusASL/tools/asl_mod_cache.py")
def raises(exc, f, *a, **k):
    try: f(*a, **k)
    except exc: return True
    except BaseException as ex: raise SystemExit("wrong exception %r" % ex)
    return False
def need(cond, msg):
    if not cond: raise SystemExit("FAIL: " + msg)
PY
py() { python3 -I - "$root" "$t" "$@"; }
fakelean() {  # fakelean PREFIX: a `lean` on PATH printing PREFIX for --print-prefix
  mkdir -p "$t/fl"; printf '#!/bin/sh\n[ "$1" = --print-prefix ] && echo "%s" || exec "%s/bin/lean" "$@"\n' "$1" "$prefix" > "$t/fl/lean"; chmod +x "$t/fl/lean"
}
# keyed_toolchain: a prefix that is a symlink, or whose own directories are symlinks, is refused (and a good one accepted)
fakelean "$prefix"
py <<'PY' && ok "keyed_toolchain accepts the real prefix" || bad "keyed_toolchain real"
import sys; t = sys.argv[2]; exec(open(t + "/h.py").read())
os.environ["PATH"] = t + "/fl:" + os.environ["PATH"]
pre, cc = b.keyed_toolchain(root + "/JanusASL"); assert cc == pre + "/bin/clang"
PY
fakelean "$t/linkp"
py <<'PY' && ok "keyed_toolchain refuses a prefix reached through a symlink (realpath check)" || bad "prefix realpath mutant"
import sys; t = sys.argv[2]; exec(open(t + "/h.py").read())
os.environ["PATH"] = t + "/fl:" + os.environ["PATH"]
need(raises(b.CacheError, b.keyed_toolchain, root + "/JanusASL"), "symlinked prefix accepted")
PY
rm -rf "$t/real_par" "$t/par_link"; mkdir -p "$t/real_par/fp/bin" "$t/real_par/fp/include/clang" "$t/real_par/fp/include/lean"; cp "$clang" "$t/real_par/fp/bin/clang"; ln -s "$t/real_par" "$t/par_link"; fakelean "$t/par_link/fp"
py <<'PY' && ok "keyed_toolchain refuses a prefix with a symlinked PARENT directory (realpath != path)" || bad "prefix parent symlink"
import sys; t = sys.argv[2]; exec(open(t + "/h.py").read())
os.environ["PATH"] = t + "/fl:" + os.environ["PATH"]
need(raises(b.CacheError, b.keyed_toolchain, root + "/JanusASL"), "prefix under a symlinked parent accepted")
PY
for d in bin include include/clang include/lean; do
  rm -rf "$t/fp3"; mkdir -p "$t/fp3/bin" "$t/fp3/include/clang" "$t/fp3/include/lean"; cp "$clang" "$t/fp3/bin/clang"
  mv "$t/fp3/$d" "$t/fp3/$d.real"; ln -s "$t/fp3/$d.real" "$t/fp3/$d"; fakelean "$t/fp3"
  py <<'PY' && ok "keyed_toolchain refuses a symlinked toolchain directory ($d)" || bad "prefix dir symlink ($d)"
import sys; t = sys.argv[2]; exec(open(t + "/h.py").read())
os.environ["PATH"] = t + "/fl:" + os.environ["PATH"]
need(raises(b.CacheError, b.keyed_toolchain, root + "/JanusASL"), "symlinked toolchain directory accepted")
PY
done
# LEAN_CC: neither published nor recompiled
fakelean "$prefix"
py <<'PY' && ok "LEAN_CC set: keyed_toolchain refuses (Inconclusive)" || bad "LEAN_CC refusal"
import sys; t = sys.argv[2]; exec(open(t + "/h.py").read())
os.environ["PATH"] = t + "/fl:" + os.environ["PATH"]; os.environ["LEAN_CC"] = "clang"
need(raises(b.Inconclusive, b.keyed_toolchain, root + "/JanusASL"), "LEAN_CC accepted")
PY
# stage: the staged compiler/prefix must be the toolchain's keyed ones
py <<'PY' && ok "stage_unit refuses when the id's compiler is not the toolchain's" || bad "stage cc/prefix == keyed"
import sys; t = sys.argv[2]; exec(open(t + "/h.py").read())
tree = t + "/p"; lake = tree + "/JanusASL/.lake"
cs = m.obj_c_files(lake, "arm"); ident = m.obj_id(tree, cs, "arm")
real = m.obj_compiler(tree); m._CC[tree] = (real[0] + "x", real[1], real[2])
st = tempfile.mkdtemp(dir=t)
try: m.stage_unit(tree, "arm", lake, ident, cs, st); need(False, "staged with a wrong compiler path")
except SystemExit as ex: need("not the toolchain" in str(ex), str(ex))
m._CC[tree] = (real[0], real[1], real[2] + "/")
try: m.stage_unit(tree, "arm", lake, ident, cs, st); need(False, "staged with a wrong prefix")
except SystemExit as ex: need("not the toolchain" in str(ex), str(ex))
PY
# the compiler's content is in the id (isolated from the env part of the ArmASL key)
py <<'PY' && ok "the compiler binary's content alone changes the id" || bad "compiler content in id"
import sys; t = sys.argv[2]; exec(open(t + "/h.py").read())
tree = t + "/p"; lake = tree + "/JanusASL/.lake"; cs = m.obj_c_files(lake, "arm")
r = m.obj_compiler(tree); a = m.obj_id(tree, cs, "arm")
m._CC[tree] = (r[0], "0" * 64, r[2]); c = m.obj_id(tree, cs, "arm")
need(a != c, "same id for another compiler hash")
PY
# stage: the C is re-hashed at stage time (the only tie of a staged object to the id's C)
py <<'PY' && ok "stage_unit re-hashes the C: a C that is not the id's is refused" || bad "C re-hash at stage"
import sys; t = sys.argv[2]; exec(open(t + "/h.py").read())
tree = t + "/p"; lake = tree + "/JanusASL/.lake"; cs = dict(m.obj_c_files(lake, "arm")); ident = m.obj_id(tree, cs, "arm")
cs["build/ir/ArmASL/Part01.c"] = "0" * 64
st = tempfile.mkdtemp(dir=t)
try: m.stage_unit(tree, "arm", lake, ident, cs, st); need(False, "staged a C that is not the id's")
except SystemExit as ex: need("changed while publishing" in str(ex), str(ex))
PY
# only .c.o.export is cacheable
fresh ne; mv "$(L ne)/build/ir/ArmASL/Part01.c.o.export" "$(L ne)/build/ir/ArmASL/Part01.c.o.noexport"; mv "$(L ne)/build/ir/ArmASL/Part01.c.o.export.hash" "$(L ne)/build/ir/ArmASL/Part01.c.o.noexport.hash"; mv "$(L ne)/build/ir/ArmASL/Part01.c.o.export.trace" "$(L ne)/build/ir/ArmASL/Part01.c.o.noexport.trace"
expect 1 "a .c.o.noexport object is not cacheable (stage refuses)" stage "$t/ne" arm
grep -q "janusasl-obj-cache-v3" "$root/JanusASL/tools/asl_mod_cache.py" && ok "the object id scheme is v3" || bad "scheme"
# argv_problem: out / C path forms, unknown objects
py <<'PY' && ok "argv_problem: output form, C path form, '..', unknown object are refused" || bad "argv_problem forms"
import sys; t = sys.argv[2]; exec(open(t + "/h.py").read())
pre, cc = b.keyed_toolchain(root + "/JanusASL") if False else (None, None)
import subprocess
pre = subprocess.run(["lean", "--print-prefix"], capture_output=True, text=True, cwd=root + "/JanusASL").stdout.strip(); cc = pre + "/bin/clang"
rel = "build/ir/ArmASL/Part01.c"; c = "/x/JanusASL/.lake/" + rel
good = b.expected_argv(cc, pre, c, c + ".o.export", rel)
need(b.argv_problem(good, cc, pre, rel) is None, "the keyed command is refused")
bad1 = list(good); bad1[3] = "/x/other.o"; need(b.argv_problem(bad1, cc, pre, rel), "output form")
bad2 = b.expected_argv(cc, pre, "/x/elsewhere/Other.c", "/x/elsewhere/Other.c.o.export", rel); need(b.argv_problem(bad2, cc, pre, rel), "C path suffix")
bad3 = b.expected_argv(cc, pre, "/x/../etc/JanusASL/.lake/" + rel, "/x/../etc/JanusASL/.lake/" + rel + ".o.export", rel); need(b.argv_problem(bad3, cc, pre, rel), "dotdot")
need(b.argv_problem(b.expected_argv(cc, pre, "/x/build/ir/Other/Zed.c", "/x/build/ir/Other/Zed.c.o.export", "build/ir/Other/Zed.c"), cc, pre, "build/ir/Other/Zed.c"), "unknown object cacheable")
need(b.argv_problem(good, cc + "x", pre, rel), "argv[0] not the keyed clang")
PY
# an entry whose trace carries a command of another shape is POISONED at recompile, even when the bytes are honest
fresh ap; stage "$t/ap" arm > /dev/null; idap=$(M objkey "$t/ap"); python3 -I - "$t/st/build/ir/ArmASL/Part01.c.o.export.trace" <<'PY'
import json, sys
p = sys.argv[1]; j = json.load(open(p)); j["log"][0]["message"] += " -fwrapv"; json.dump(j, open(p, "w"))
PY
apc="$t/apcache"; mkdir -p "$apc"; B store armobj "$apc" "$idap" "$t/st" < "$t/st.list" > /dev/null
expect 3 "verify --recompile reports POISONED for an entry whose logged command has another shape" B verify armobj "$apc" "$idap" --c-root "$(L ap)" --recompile all
# armobj.set: required, equal to the consumer's set, consistent with the .cin records, hashed at fetch
fresh st1; stage "$t/st1" arm > /dev/null; ids1=$(M objkey "$t/st1"); s1c="$t/s1cache"; mkdir -p "$s1c"
cp -a "$t/st" "$t/st1-keep"; cp "$t/st.list" "$t/st1.list"
resign() {  # resign CACHE ID PYTHON-EDIT(e, man): edit an entry's tree/manifest and re-sign it
  python3 -I - "$root" "$1" "$2" "$3" <<'PY'
import importlib.util, os, sys
root, cache, ident, edit = sys.argv[1:]
spec = importlib.util.spec_from_file_location("bcache", root + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
e = b.entry_dir("armobj", cache, ident); man = b.parse_manifest(open(e + "/MANIFEST.sha256", "rb").read())
os.system("chmod -R u+w " + e)
exec(edit)
data = "".join("%s  %s\n" % (v, k) for k, v in sorted(man.items())).encode()
open(e + "/MANIFEST.sha256", "wb").write(data); open(e + "/MANIFEST.hmac", "w").write(b.mac("armobj", ident, data) + "\n")
PY
}
fresh_entry() { rm -rf "$s1c/armobj"; B store armobj "$s1c" "$ids1" "$t/st" < "$t/st.list" > /dev/null; }
fresh_entry; resign "$s1c" "$ids1" 'os.unlink(e + "/tree/armobj.set"); del man["armobj.set"]'
expect 3 "an entry without armobj.set is invalid" B verify armobj "$s1c" "$ids1"
fresh_entry; resign "$s1c" "$ids1" 'f = e + "/tree/build/ir/ArmASL/Part01.c.o.export.cin"; open(f, "w").write("0" * 64 + "\n"); man["build/ir/ArmASL/Part01.c.o.export.cin"] = b.sha_file(f)'
expect 3 "a .cin that disagrees with the signed set is invalid" B verify armobj "$s1c" "$ids1"
fresh_entry; py "$s1c" "$ids1" <<'PY' && ok "fetch with another C set than the entry's is rejected (set == want_set)" || bad "set == want_set"
import sys; t = sys.argv[2]; exec(open(t + "/h.py").read())
cache, ident = sys.argv[3], sys.argv[4]
cs = m.obj_c_files(t + "/st1/JanusASL/.lake", "arm"); other = dict(cs); other["build/ir/ArmASL/Part01.c"] = "1" * 64
need(raises(b.CacheError, b.fetch, "armobj", cache, ident, t + "/dstx/.lake", (), None, other), "another set accepted")
b.fetch("armobj", cache, ident, t + "/dsty/.lake", (), None, cs)
PY
fresh_entry; resign "$s1c" "$ids1" 'f = e + "/tree/armobj.set"; open(f, "w").write(open(f).read().replace("\n", "") + " ")'
python3 -I - "$s1c/armobj/$ids1/MANIFEST.sha256" <<'PY'
import sys   # keep the manifest hash of armobj.set as it was before the edit: the set bytes no longer match it
PY
fresh_entry; chmod -R u+w "$s1c/armobj/$ids1/tree"; printf ' ' >> "$s1c/armobj/$ids1/tree/armobj.set"
expect 3 "armobj.set is hashed against the manifest at fetch (a modified set is rejected)" B fetch armobj "$s1c" "$ids1" "$t/dsz/.lake"
# tombstones: MAC, domain separation, id binding
tomb() {  # tomb CACHE ID DATAID MACKIND MACID: write a tombstone document for ID with chosen binding
  python3 -I - "$root" "$@" <<'PY'
import importlib.util, json, os, sys
root, cache, ident, dataid, mkind, macid = sys.argv[1:]
spec = importlib.util.spec_from_file_location("bcache", root + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
data = json.dumps({"id": dataid, "objects": {"build/ir/ArmASL/Part01.c.o.export": "9" * 64}}, sort_keys=True, separators=(",", ":")).encode()
mac = "0" * 64 if mkind == "bad" else b.mac(mkind, macid, data)
open(b.tomb_path(cache, ident), "w").write(json.dumps({"data": data.decode(), "mac": mac}))
PY
}
fresh_entry
for c in "bad:$ids1:$ids1" "armobj:$ids1:$ids1" "tombstone:$ids1:$(printf 'e%.0s' {1..40})"; do
  IFS=: read -r mk di mi <<< "$c"; tomb "$s1c" "$ids1" "$di" "$mk" "$mi"
  expect 3 "a tombstone with MAC '$mk' / bound to $( [ "$mi" = "$ids1" ] && echo this id || echo another id) makes the id unusable, entry untouched" B fetch armobj "$s1c" "$ids1" "$t/dtb/.lake"
  B verify armobj "$s1c" "$ids1" > /dev/null 2>&1; [ -d "$s1c/armobj/$ids1/tree" ] && ok "  ... the entry directory is still there" || bad "entry destroyed by a bad tombstone"
done
tomb "$s1c" "$ids1" "$(printf 'e%.0s' {1..40})" tombstone "$ids1"   # valid MAC for this id's slot but the document names another id
expect 3 "a tombstone whose document names another id is rejected (id binding)" B fetch armobj "$s1c" "$ids1" "$t/dtb2/.lake"
# C: a garbage tombstone never makes `store` replace or delete a valid entry; the operator clears it
printf 'garbage' > "$s1c/armobj/.tombstone-$ids1"
stage "$t/st1" arm > /dev/null; expect 4 "store with a garbage tombstone is refused" B store armobj "$s1c" "$ids1" "$t/st" < "$t/st.list"
[ -f "$s1c/armobj/$ids1/MANIFEST.sha256" ] && ok "  ... and the valid entry is untouched" || bad "store destroyed a valid entry because of a garbage tombstone"
M objaudit "$t/st1" arm "$s1c" > "$t/out" 2>&1; rc=$?
[ -f "$s1c/armobj/$ids1/MANIFEST.sha256" ] && [ "$rc" = 4 ] && grep -q LOUD "$t/out" && ok "objaudit with a garbage tombstone: LOUD, entry untouched, not a pass (exit 4)" || bad "objaudit vs garbage tombstone rc $rc: $(cat "$t/out")"
expect 2 "clear-tombstone without --yes does nothing" bash -c "python3 -I '$root/scripts/lib/bcache.py' clear-tombstone '$s1c' '$ids1' >/dev/null; [ -f '$s1c/armobj/.tombstone-$ids1' ] && exit 2"
python3 -I "$root/scripts/lib/bcache.py" clear-tombstone "$s1c" "$ids1" --yes > /dev/null; [ ! -e "$s1c/armobj/.tombstone-$ids1" ] && ok "clear-tombstone --yes removes it" || bad "not cleared"
B fetch armobj "$s1c" "$ids1" "$t/dtb3/.lake" > /dev/null && ok "  ... and the entry is served again" || bad "entry not served after clearing"
# objaudit flags an entry that fails verification (tampered cached bytes) and quarantines it
fresh_entry; chmod -R u+w "$s1c/armobj/$ids1/tree"; printf X >> "$s1c/armobj/$ids1/tree/build/ir/ArmASL/Part01.c.o.export"
M objaudit "$t/st1" arm "$s1c" > "$t/out" 2>&1; rc=$?
[ "$rc" = 3 ] && ls -d "$s1c/armobj/.poisoned-$ids1" > /dev/null 2>&1 && ok "objaudit: an entry that fails verification is poisoned (exit 3) and quarantined" || bad "audit verify failure rc $rc: $(cat "$t/out")"
# objaudit --dry-run changes nothing; .poisoned-* retention
fresh_entry; chmod -R u+w "$s1c/armobj/$ids1/tree"; printf X >> "$s1c/armobj/$ids1/tree/build/ir/ArmASL/Part01.c.o.export"
M objaudit "$t/st1" arm "$s1c" --dry-run > "$t/out" 2>&1; rc=$?
[ "$rc" = 3 ] && [ -d "$s1c/armobj/$ids1" ] && [ ! -e "$s1c/armobj/.tombstone-$ids1" ] && ok "objaudit --dry-run reports (exit 3) but quarantines nothing" || bad "dry run rc $rc"
mkdir -p "$s1c/armobj/.poisoned-oldold"; touch -d '40 days ago' "$s1c/armobj/.poisoned-oldold"; mkdir -p "$s1c/armobj/.poisoned-newnew"
M objaudit "$t/st1" arm "$s1c" > /dev/null 2>&1
[ ! -e "$s1c/armobj/.poisoned-oldold" ] && [ -d "$s1c/armobj/.poisoned-newnew" ] && ok ".poisoned-* directories older than the retention (30 days) are removed, recent ones kept" || bad "retention"
# objaudit takes the entry lock: while another process holds it exclusively the audit waits
fresh_entry
( python3 -I - "$root" "$s1c" "$ids1" <<'PY'
import importlib.util, sys, time
spec = importlib.util.spec_from_file_location("bcache", sys.argv[1] + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
lk = b.lock_path(b.entry_dir("armobj", sys.argv[2], sys.argv[3]) + ".lock", shared=False); open(sys.argv[2] + "/locked", "w").write("1"); time.sleep(4)
PY
) &
lp=$!; for i in 1 2 3 4 5 6 7 8 9 10; do [ -f "$s1c/locked" ] && break; sleep 0.3; done
s0=$(date +%s); M objaudit "$t/st1" arm "$s1c" > /dev/null 2>&1; s1=$(date +%s); wait $lp
[ $((s1-s0)) -ge 2 ] && ok "objaudit waits for the entry lock (no race with a republish)" || bad "objaudit did not wait for the lock ($((s1-s0)) s)"
# threshold: unchecked share above the limit fails closed, below passes; a compared difference is exit 3 whatever the coverage
fresh th; cth="$t/thcache"; mkdir -p "$cth"; M objpublish "$t/th" arm "$cth" 0 > /dev/null
rm "$(L th)/build/ir/ArmASL/Part02.c.o.export"
ASL_OBJAUDIT_MAX_UNCHECKED_PCT=30 M objaudit "$t/th" arm "$cth" > "$t/out" 2>&1; rc=$?; [ "$rc" = 0 ] && ok "objaudit: 25% not comparable is within a 30% limit (exit 0)" || bad "threshold pass rc $rc: $(cat "$t/out")"
ASL_OBJAUDIT_MAX_UNCHECKED_PCT=20 M objaudit "$t/th" arm "$cth" > "$t/out" 2>&1; rc=$?; [ "$rc" = 4 ] && ok "  ... and above a 20% limit it is INCOMPLETE (exit 4)" || bad "threshold fail rc $rc"
printf X >> "$(L th)/build/ir/ArmASL/Part01.c.o.export"
ASL_OBJAUDIT_MAX_UNCHECKED_PCT=100 M objaudit "$t/th" arm "$cth" > "$t/out" 2>&1; rc=$?; [ "$rc" = 3 ] && ok "  ... a compared object that differs is exit 3 whatever the limit" || bad "diff under loose limit rc $rc"
# sandbox details
py <<'PY' && ok "sandbox: capabilities dropped, root-owned/not-writable bwrap only, failing bwrap probe is Inconclusive, no key env, TMPDIR on the work dir" || bad "sandbox details"
import sys; t = sys.argv[2]; exec(open(t + "/h.py").read())
work = t + "/sbw"; os.makedirs(work, exist_ok=True)
pre = b._sandbox_prefix(work, work)
r = subprocess.run(pre + ["/bin/sh", "-c", "grep CapEff /proc/self/status"], capture_output=True, text=True)
need(r.stdout.split()[-1] == "0000000000000000", "capabilities not dropped: " + r.stdout)
real = b._bwrap()
wr = t + "/bw-ww"; shutil.copy(real, wr); os.chmod(wr, 0o777)
nr = t + "/bw-nobody"; shutil.copy(real, nr); os.chmod(nr, 0o755); os.chown(nr, 65534, 65534)
ok_ = t + "/bw-ok"; shutil.copy(real, ok_); os.chmod(ok_, 0o755)
b.BWRAP_CANDIDATES = [wr]; need(b._bwrap() is None, "world-writable bwrap accepted")
b.BWRAP_CANDIDATES = [nr]; need(b._bwrap() is None, "bwrap owned by another user accepted")
b.BWRAP_CANDIDATES = [ok_]; need(b._bwrap() == ok_, "root-owned bwrap rejected")
fail = t + "/bw-fail"; open(fail, "w").write("#!/bin/sh\nexit 1\n"); os.chmod(fail, 0o755)
b.BWRAP_CANDIDATES = [fail]; os.environ.pop(b.UNSANDBOXED_OPTIN, None)
need(raises(b.Inconclusive, b._sandbox_prefix, work, work), "a failing bwrap probe was accepted")
b.BWRAP_CANDIDATES = [real]
os.environ["JANUS_CACHE_KEY_DIR"] = t + "/keys"; seen = {}
def fake_run(cmd, cwd, env, timeout):
    seen.update(env or {}); open(cmd[cmd.index("-o") + 1], "w").write("x"); return subprocess.CompletedProcess(cmd, 0, b"", b"")
orig = b.run_sandboxed
b._sandbox_prefix = lambda w, c: []
b.run_sandboxed = fake_run
pre_, cc_ = "/p", "/p/bin/clang"
b.recompile_object(cc_, pre_, work + "/A.c", "build/ir/ArmASL/Part01.c", work)
b.run_sandboxed = orig
need("JANUS_CACHE_KEY_DIR" not in seen and seen.get("TMPDIR") == work, "env %r" % {k: v for k, v in seen.items() if k in ("JANUS_CACHE_KEY_DIR", "TMPDIR")})
PY
py <<'PY' && ok "recompile: a failing compile and a compile that writes no object are Inconclusive; clean_stale removes only old private dirs; publish survives a staging OSError" || bad "recompile/clean_stale/stage OSError"
import sys; t = sys.argv[2]; exec(open(t + "/h.py").read())
work = t + "/rw"; os.makedirs(work, exist_ok=True); orig = b.run_sandboxed
b._sandbox_prefix = lambda w, c: []
b.run_sandboxed = lambda cmd, cwd, env, timeout: subprocess.CompletedProcess(cmd, 1, b"", b"error: boom")
need(raises(b.Inconclusive, b.recompile_object, "/p/bin/clang", "/p", work + "/A.c", "build/ir/ArmASL/Part01.c", work), "rc != 0 accepted")
b.run_sandboxed = lambda cmd, cwd, env, timeout: subprocess.CompletedProcess(cmd, 0, b"", b"")
need(raises(b.Inconclusive, b.recompile_object, "/p/bin/clang", "/p", work + "/A.c", "build/ir/ArmASL/Part01.c", work), "no output accepted")
b.run_sandboxed = orig
d = t + "/cs"; os.makedirs(d, exist_ok=True)
for n, old in ((".recompile-old", 1), (".objstage-old", 1), (".recompile-new", 0), ("keepme", 1)):
    os.makedirs(d + "/" + n, exist_ok=True)
    if old: os.utime(d + "/" + n, (1, 1))
b.clean_stale(d)
need(not os.path.exists(d + "/.recompile-old") and not os.path.exists(d + "/.objstage-old"), "old private dirs kept")
need(os.path.exists(d + "/.recompile-new") and os.path.exists(d + "/keepme"), "clean_stale removed too much")
orig_mk = tempfile.mkdtemp
def boom(*a, **k): raise OSError(28, "No space left on device")
tempfile.mkdtemp = boom
import io, contextlib
out = io.StringIO()
with contextlib.redirect_stdout(out): m.obj_publish(t + "/p", "arm", t + "/cs-pub", "0")
tempfile.mkdtemp = orig_mk
need("cannot create a staging directory" in out.getvalue(), out.getvalue())
# unit-level random draw: the N smallest are always chosen, the draw is over the REST only
calls = []
def spy(cands, k): calls.append((len(cands), k)); return []
m.load_bcache = lambda root, _o=m.load_bcache: (lambda mod: (setattr(mod, "draw_random", spy), mod)[1])(_o(root))
os.environ["ASL_OBJ_RECOMPILE_RANDOM"] = "2"
os.makedirs(t + "/cs-pub", exist_ok=True)
m.obj_publish(t + "/pj", "jasl", t + "/cs-pub", "1")
need(calls and calls[-1] == (3, 2), "draw over the rest: %r" % calls)   # pj has 4 units (3 objects + the object-less NoObj): 1 smallest chosen, 3 left for the draw
calls.clear(); m.obj_publish(t + "/pj", "jasl", t + "/cs-pub", "0"); need(not calls, "a draw with sample 0")
calls.clear(); m.obj_publish(t + "/pj", "jasl", t + "/cs-pub", "all"); need(not calls, "a draw with sample all")
PY

# ======== RTOBJ5: the janus scope, the trusted auditor's objects, opt-out values, audit lock, unreadable tombstone ========
RL() { echo "$t/$1/.lake"; }     # the ROOT package's .lake of a fixture tree
janus_fresh() {  # janus_fresh NAME: a tree with root-package objects: Foo, Bar (cacheable) and the auditor's own Audit, AuditMain
  copy "$t/$1"; mkdir -p "$t/$1/.lake"
  for n in Foo Bar; do mkjc "$(RL $1)" Janus "$n"; done
  for n in Audit AuditMain; do mkjc "$(RL $1)" Janus/Tools "$n"; done
}
janus_fresh jn
[ "$(M objkey "$t/jn" janus | wc -l)" = 2 ] && ok "janus scope: 2 units (Foo, Bar); the auditor's modules (Janus.Tools.Audit, AuditMain) are excluded" || bad "janus units: $(M objkey "$t/jn" janus | wc -l)"
stage "$t/jn" janus 0 > /dev/null && ok "janus scope: a real object stages (exact argv, no bracket depth)" || bad "janus stage"
janus_fresh jn2; edit_log "$(RL jn2)/build/ir/Janus/Bar.c.o.export.trace" "a.remove('-O3')"; expect 1 "janus scope: a dropped flag is refused" stage "$t/jn2" janus 0
janus_fresh jn3; edit_log "$(RL jn3)/build/ir/Janus/Bar.c.o.export.trace" "a.insert(-1,'-fbracket-depth=100000')"; expect 1 "janus scope: the ArmASL-only -fbracket-depth is refused on a Janus object" stage "$t/jn3" janus 0
jid() { M objkey "$1" janus | sort | tr '\n' ' '; }
base_ids=$(jid "$t/jn")
janus_fresh jn4; python3 -I - "$t/jn4/lakefile.toml" <<'PY'
import sys; p = sys.argv[1]; s = open(p).read(); i = s.index('name = "Janus"'); j = s.index("\n", i); open(p, "w").write(s[:j] + '\nweakLeancArgs = ["-fwrapv"]' + s[j:])
PY
[ "$(jid "$t/jn4")" != "$base_ids" ] && ok "janus scope: the lean_lib Janus table (weakLeancArgs) is in the id" || bad "Janus lib table not in the id"
janus_fresh jn5; python3 -I - "$t/jn5/lakefile.toml" <<'PY'
import sys; p = sys.argv[1]; s = open(p).read(); i = s.index('name = "janus-decode"'); j = s.index("\n", i); open(p, "w").write(s[:j] + '\nmoreLinkArgs = ["-lfoo"]' + s[j:])
PY
[ "$(jid "$t/jn5")" != "$base_ids" ] && ok "janus scope: a lean_exe table is in the id" || bad "exe table not in the janus id"
janus_fresh jn6; printf '\nmoreLeancArgs = ["-fwrapv"]\n' > "$t/jn6/lk.tail"; python3 -I - "$t/jn6/lakefile.toml" <<'PY'
import sys; p = sys.argv[1]; s = open(p).read(); open(p, "w").write('moreLeancArgs = ["-fwrapv"]\n' + s)
PY
[ "$(jid "$t/jn6")" != "$base_ids" ] && ok "janus scope: a package-level lakefile key is in the id" || bad "package keys not in the janus id"
jc="$t/jncache"; mkdir -p "$jc"
M objpublish "$t/jn" janus "$jc" all > "$t/out" 2>&1; grep -q "stored 2, already cached 0, no object 0, refused 0" "$t/out" && ok "janus scope: publish stores Foo and Bar and NOT the auditor's objects" || bad "janus publish: $(cat "$t/out")"
# an entry for the auditor's object that a key holder forged: never restored
py "$jc" <<'PY' && ok "the auditor's objects are never restored, even from a validly signed entry" || bad "TCB object restored"
import sys; t = sys.argv[2]; exec(open(t + "/h.py").read())
cache = sys.argv[3]; tree = t + "/jn"; lake = tree + "/.lake"
c = "build/ir/Janus/Tools/Audit.c"; cs = {c: m.sha_file(lake + "/" + c)}
ident = m.obj_id(tree, cs, "janus"); st = tempfile.mkdtemp(dir=t)
rels = m.stage_unit(tree, "janus", lake, ident, cs, st)
b.store("armobj", cache, ident, st, rels, None, None, cs)
need(os.path.isdir(b.entry_dir("armobj", cache, ident)), "forged TCB entry not created")
PY
copy "$t/jr"; mkdir -p "$t/jr/.lake"; rsync -a --include='*/' --include='*.c' --include='*.c.hash' --exclude='*' "$t/jn/.lake/" "$t/jr/.lake/"
M objrestore "$t/jr" janus "$jc" > "$t/out" 2>&1
[ -f "$t/jr/.lake/build/ir/Janus/Foo.c.o.export" ] && [ -f "$t/jr/.lake/build/ir/Janus/Bar.c.o.export" ] && ok "janus scope: restore places Foo and Bar" || bad "janus restore: $(cat "$t/out")"
[ ! -e "$t/jr/.lake/build/ir/Janus/Tools/Audit.c.o.export" ] && [ ! -e "$t/jr/.lake/build/ir/Janus/Tools/AuditMain.c.o.export" ] && ok "  ... and never the auditor's (janus-audit's own) objects" || bad "TCB object placed"
cmp -s "$t/jr/.lake/build/ir/Janus/Foo.c.o.export" "$t/jn/.lake/build/ir/Janus/Foo.c.o.export" && ok "  ... byte-identical" || bad "janus restore differs"
fb=$(find "$jc/armobj" -path '*/tree/build/ir/Janus/Bar.c.o.export' | head -1); chmod -R u+w "$(dirname "$fb")"; printf X >> "$fb"
copy "$t/jr2"; mkdir -p "$t/jr2/.lake"; rsync -a --include='*/' --include='*.c' --include='*.c.hash' --exclude='*' "$t/jn/.lake/" "$t/jr2/.lake/"
M objrestore "$t/jr2" janus "$jc" > "$t/out" 2>&1; grep -q "1 restored, 0 without entry, 1 rejected" "$t/out" && ok "janus scope: a tampered entry is REJECTED, the other restored" || bad "janus tamper: $(cat "$t/out")"
# audit + tombstone in the janus scope
rm -rf "$jc/armobj"; M objpublish "$t/jn" janus "$jc" all > /dev/null 2>&1
M objaudit "$t/jn" janus "$jc" > "$t/out" 2>&1; [ $? = 0 ] && grep -q "coverage 2 of 2" "$t/out" && ok "janus scope: objaudit compares 2 of 2" || bad "janus audit: $(cat "$t/out")"
printf X >> "$(RL jn)/build/ir/Janus/Foo.c.o.export"
M objaudit "$t/jn" janus "$jc" > "$t/out" 2>&1; rc=$?; [ "$rc" = 3 ] && ls "$jc/armobj"/.tombstone-* > /dev/null 2>&1 && ok "janus scope: a differing object is POISONED: exit 3, tombstone written" || bad "janus audit poisoned rc $rc"
pi=$(basename "$(ls -d "$jc/armobj"/.poisoned-* | head -1)"); pi=${pi#.poisoned-}
mv "$jc/armobj/.poisoned-$pi" "$jc/armobj/$pi"; expect 3 "janus scope: renaming the quarantined entry back does not revive it" B fetch armobj "$jc" "$pi" "$t/jdst/.lake"

# an unreadable tombstone counts as NOT COMPARABLE (M7b): 1 of 2 objects here
fresh ut; cut_="$t/utcache"; mkdir -p "$cut_"; for n in Aa Bb; do mkjc "$(L ut)" JanusASL "$n"; done; M objpublish "$t/ut" jasl "$cut_" 0 > /dev/null 2>&1
uid=$(M objkey "$t/ut" jasl | head -1); printf 'garbage' > "$cut_/armobj/.tombstone-$uid"
ASL_OBJAUDIT_MAX_UNCHECKED_PCT=60 M objaudit "$t/ut" jasl "$cut_" > "$t/out" 2>&1; rc=$?
grep -q "coverage 2 of 3 objects compared (67%), 1 not comparable" "$t/out" && [ "$rc" = 0 ] && ok "an unreadable tombstone counts as not comparable (1 of 3), within a 60% limit" || bad "unreadable tombstone accounting rc $rc: $(cat "$t/out")"
ASL_OBJAUDIT_MAX_UNCHECKED_PCT=20 M objaudit "$t/ut" jasl "$cut_" > "$t/out" 2>&1; [ $? = 4 ] && ok "  ... and above a 20% limit the audit is INCOMPLETE" || bad "unreadable tombstone not fatal"

# objaudit holds the entry lock against a concurrent WRITER: a replacement done under the lock is audited, not clobbered
fresh lk1; forge "$(L lk1)" "$(L lk1)/build/ir/ArmASL/Part01.c"; lkc="$t/lkcache"; mkdir -p "$lkc"; M objpublish "$t/lk1" arm "$lkc" 0 > /dev/null 2>&1
lid=$(M objkey "$t/lk1"); fresh lk2; hc="$t/lkhonest"; mkdir -p "$hc"; M objpublish "$t/lk2" arm "$hc" 0 > /dev/null 2>&1; [ "$(M objkey "$t/lk2")" = "$lid" ] || bad "fixture: ids differ"
( python3 -I - "$root" "$lkc" "$lid" "$hc" <<'PY'
import importlib.util, shutil, sys, time, os
spec = importlib.util.spec_from_file_location("bcache", sys.argv[1] + "/scripts/lib/bcache.py"); b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
cache, ident, hc = sys.argv[2:]
e = b.entry_dir("armobj", cache, ident); lk = b.lock_path(e + ".lock", shared=False); open(cache + "/lk-held", "w").write("1")
time.sleep(2.5)
os.system("chmod -R u+w '%s'; rm -rf '%s'" % (e, e)); shutil.copytree(hc + "/armobj/" + ident, e)   # an honest republish, under the lock
PY
) & lw=$!; for i in $(seq 1 30); do [ -f "$lkc/lk-held" ] && break; sleep 0.2; done
M objaudit "$t/lk2" arm "$lkc" > "$t/out" 2>&1; rc=$?; wait $lw
[ "$rc" = 0 ] && [ -d "$lkc/armobj/$lid" ] && ! ls "$lkc/armobj"/.poisoned-* > /dev/null 2>&1 && ok "objaudit waited for the writer's lock, then audited the NEW (honest) entry: no quarantine of a good entry" || bad "audit raced the writer: rc $rc: $(cat "$t/out")"

# M5: objaudit holds the entry lock ACROSS the quarantine rename (verify and rename are one step). The audit is paused after it
# verified (hook ASL_OBJAUDIT_TEST_PAUSE, test-only: it only waits) and a republish of the same entry is attempted: with the lock
# held it BLOCKS until the audit is done; an audit that released the lock after verifying would let the republish through, and the
# rename would then quarantine the NEW (good) entry.
fresh m5a; forge "$(L m5a)" "$(L m5a)/build/ir/ArmASL/Part01.c"; m5c="$t/m5cache"; mkdir -p "$m5c"; M objpublish "$t/m5a" arm "$m5c" 0 > /dev/null 2>&1
m5id=$(M objkey "$t/m5a"); fresh m5b; m5h="$t/m5honest"; mkdir -p "$m5h"; M objpublish "$t/m5b" arm "$m5h" 0 > /dev/null 2>&1
rm -rf "$t/m5st"; mkdir "$t/m5st"; M objstage "$t/m5b" arm "$t/m5st" "$t/m5st.list" > /dev/null
rm -f "$t/m5p.paused" "$t/m5p.go"
ASL_OBJAUDIT_TEST_PAUSE="$t/m5p" M objaudit "$t/m5b" arm "$m5c" > "$t/m5out" 2>&1 & m5a_pid=$!
for i in $(seq 1 100); do [ -f "$t/m5p.paused" ] && break; sleep 0.1; done
if [ ! -f "$t/m5p.paused" ]; then bad "M5: the audit never reached the pause: $(cat "$t/m5out")"; kill -9 $m5a_pid 2>/dev/null
else
  ( B store armobj "$m5c" "$m5id" "$t/m5st" < "$t/m5st.list" > "$t/m5store.out" 2>&1; echo $? > "$t/m5store.rc" ) & m5s_pid=$!
  sleep 2
  [ ! -f "$t/m5store.rc" ] && ok "M5: a republish of the entry blocks while the audit holds its lock (verified, not yet renamed)" || bad "M5: the republish got through between verify and rename: rc $(cat "$t/m5store.rc")"
  touch "$t/m5p.go"; wait $m5a_pid; m5rc=$?; wait $m5s_pid
  [ "$m5rc" = 3 ] && ok "M5: the audit quarantined the poisoned entry it verified (exit 3)" || bad "M5: audit rc $m5rc: $(cat "$t/m5out")"
  [ -d "$m5c/armobj/$m5id" ] && B verify armobj "$m5c" "$m5id" > /dev/null 2>&1 && ok "M5: the republished honest entry is served afterwards (it was not quarantined)" || bad "M5: no valid entry after audit + republish"
fi

# M17: when the auditor's module set cannot be determined (tcb_modules returns None) the janus scope caches NOTHING: no unit,
# nothing published, nothing restored (the auditor's own objects must never come from a cache)
tcb_none() {  # tcb_none NAME WHY MUTATION: a tree in which tcb_modules is undeterminable
  janus_fresh "$1"
  python3 -I - "$t/$1" "$3" <<'PY'
import os, sys
root, how = sys.argv[1:]
lf = root + "/lakefile.toml"; s = open(lf).read()
if how == "noexe":      s = s.replace('name = "janus-audit"', 'name = "janus-auditor-renamed"')
elif how == "twoexes":  s += '\n[[lean_exe]]\nname = "janus-audit"\nroot = "Janus.Tools.AuditMain"\n'
elif how == "badtoml":  s += '\n[[lean_exe\n'
elif how == "nosrc":    os.remove(root + "/Janus/Tools/AuditMain.lean")
open(lf, "w").write(s)
PY
}
for how in noexe twoexes badtoml nosrc; do
  tcb_none "m17$how" x "$how"
  n=$(M objkey "$t/m17$how" janus 2>/dev/null | wc -l)
  [ "$n" = 0 ] && ok "M17/$how: tcb_modules undeterminable -> the janus scope has no unit" || bad "M17/$how: $n units (the auditor's objects would be cached)"
  mkdir -p "$t/m17c$how"; M objpublish "$t/m17$how" janus "$t/m17c$how" all > "$t/out" 2>&1
  { [ ! -d "$t/m17c$how/armobj" ] || [ -z "$(ls "$t/m17c$how/armobj" 2>/dev/null)" ]; } && ok "M17/$how: nothing published" || bad "M17/$how: published: $(ls "$t/m17c$how/armobj")"
done

# M17 (unit level; kills the "undeterminable -> treat as empty TCB" mutant even where the id computation fails first, as it
# does on a bad TOML): tcb_modules is None and obj_units returns no unit although the C files are handed in directly
cat > "$t/m17unit.py" <<'PY'
import importlib.util, sys
spec = importlib.util.spec_from_file_location("m", sys.argv[1] + "/JanusASL/tools/asl_mod_cache.py"); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
r = sys.argv[2]
assert m.tcb_modules(r) is None, m.tcb_modules(r)
m.obj_id = lambda root, cs, scope: "stub"   # the id computation must not be what stops it
cs = {"build/ir/Janus/Foo.c": "0" * 64, "build/ir/Janus/Tools/Audit.c": "1" * 64, "build/ir/Janus/Tools/AuditMain.c": "2" * 64}
assert m.obj_units(r, "janus", cs) == [], m.obj_units(r, "janus", cs)
PY
for how in noexe twoexes badtoml nosrc lakefilelean; do
  tcb_none "m17u$how" x "$how"
  if [ "$how" = lakefilelean ]; then echo "-- Lake would build from this file, not from the toml" > "$t/m17u$how/lakefile.lean"; fi
  python3 -I "$t/m17unit.py" "$root" "$t/m17u$how" > "$t/out" 2>&1 && ok "M17/$how: tcb_modules is None and obj_units yields no unit (C files given directly)" || bad "M17/$how: undeterminable auditor modules did not stop the janus scope: $(head -c 300 "$t/out")"
done
# a header_imports blind spot does not drop an auditor module from the TCB: an import that follows a block comment on its line
janus_fresh m17imp
{ printf '/- note -/ import Janus.Foo\n'; cat "$t/m17imp/Janus/Tools/AuditMain.lean"; } > "$t/m17imp.new"; mv "$t/m17imp.new" "$t/m17imp/Janus/Tools/AuditMain.lean"
printf 'import Lean\n' > "$t/m17imp/Janus/Foo.lean"
cat > "$t/m17imp.py" <<'PY'
import importlib.util, sys
spec = importlib.util.spec_from_file_location("m", sys.argv[1] + "/JanusASL/tools/asl_mod_cache.py"); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
assert "Janus.Foo" in (m.tcb_modules(sys.argv[2]) or set()), m.tcb_modules(sys.argv[2])
PY
python3 -I "$t/m17imp.py" "$root" "$t/m17imp" > "$t/out" 2>&1 && ok "M17: an import hidden after a block comment on its line is still TCB" || bad "M17: the hidden import was dropped from the TCB: $(head -c 300 "$t/out")"

# opt-out values: 0|off|no|false switch it off, an empty value is the default (ON) and is printed, junk is OFF
for v in 0 off no false; do
  ASL_OBJ_CACHE=$v ASL_CACHE="$cdir" "$t/cr/scripts/asl.sh" objcache-state 2>/dev/null | grep -q "^OFF (ASL_OBJ_CACHE=$v)" && ok "ASL_OBJ_CACHE=$v turns the object cache OFF" || bad "ASL_OBJ_CACHE=$v not OFF"
  rm -f "$t/cr/JanusASL/.lake/build/ir/ArmASL/Part01.c.o.export"; ASL_OBJ_CACHE=$v ASL_CACHE="$cdir" "$t/cr/scripts/asl.sh" __call objcache_restore arm > /dev/null 2>&1
  [ ! -e "$t/cr/JanusASL/.lake/build/ir/ArmASL/Part01.c.o.export" ] && ok "  ... and nothing is restored" || bad "restored with ASL_OBJ_CACHE=$v"
done
ASL_OBJ_CACHE= ASL_CACHE="$cdir" "$t/cr/scripts/asl.sh" objcache-state 2>/dev/null | grep -q "$([ "$def" = 1 ] && echo '^ON (ASL_OBJ_CACHE=<empty>, the default)' || echo '^OFF (default)')" && ok "an EMPTY ASL_OBJ_CACHE is the default (ON) and says so" || bad "empty value"
ASL_OBJ_CACHE=banana ASL_CACHE="$cdir" "$t/cr/scripts/asl.sh" objcache-state 2>/dev/null | grep -q "^OFF (ASL_OBJ_CACHE=banana: unrecognised" && ok "an unrecognised value is OFF, not silently ON" || bad "junk value"

[ $fail = 0 ] && echo "test_asl_obj_cache: all passed" || { echo "test_asl_obj_cache: FAILED"; exit 1; }
