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
# a built-looking tree: emitted C, and an object + hash + trace for each (compiled by Lake's clang when present)
clang=""; for c in "$HOME"/.elan/toolchains/*/bin/clang; do [ -x "$c" ] && clang="$c"; done
build() {  # build DIR: fake .lake/build/ir with the same C in any directory
  local lake="$1/JanusASL/.lake" d f
  for d in "$lake/build/ir/ArmASL" "$lake/packages/Sail/.lake/build/ir/Sail" "$lake/build/ir/JanusASL"; do mkdir -p "$d"; done
  for f in "$lake/build/ir/ArmASL.c" "$lake/build/ir/ArmASL/Part01.c" "$lake/build/ir/ArmASL/Part02.c" \
           "$lake/packages/Sail/.lake/build/ir/Sail/Attr.c" "$lake/build/ir/JanusASL/Check.c"; do
    printf '// Lean compiler output\nint f_%s(void){return %d;}\n' "$(basename "$f" .c)" "$(basename "$f" .c | wc -c)" > "$f"
    case "$f" in */ir/JanusASL/*) continue ;; esac   # not in scope (the module entries hold those)
    if [ -n "$clang" ]; then (cd "$(dirname "$f")" && "$clang" -c -O3 -fPIC -o "$f.o.export" "$f"); else printf 'obj-of-%s\n' "$(sha256sum < "$f")" > "$f.o.export"; fi
    sha256sum < "$f" | cut -c1-16 > "$f.o.export.hash"
    printf '{"inputs":[["%s","%s"]]}\n' "$(basename "$f")" "$(sha256sum < "$f" | cut -c1-16)" > "$f.o.export.trace"
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
build_jasl() {  # the objects of ir/JanusASL/Check.c (build() made only its C)
  local f="$1/JanusASL/.lake/build/ir/JanusASL/Check.c"
  if [ -n "$clang" ]; then (cd "$(dirname "$f")" && "$clang" -c -O3 -fPIC -o "$f.o.export" "$f"); else printf 'obj\n' > "$f.o.export"; fi
  sha256sum < "$f" | cut -c1-16 > "$f.o.export.hash"; echo '{}' > "$f.o.export.trace"
}
build_jasl "$t/a"; build_jasl "$t/deep/er/b"
ja=$(M objkey "$t/a" jasl); jb=$(M objkey "$t/deep/er/b" jasl)
[ -n "$ja" ] && [ "$ja" = "$jb" ] && [ "$ja" != "$ida" ] && ok "the jasl scope has its own id, path independent" || bad "jasl id: $ja $jb $ida"
M objfiles "$t/a" jasl | tr '\0' '\n' | grep -c . | grep -qx 3 && ok "jasl scope = 1 C file x 3" || bad "jasl objfiles"
M objfiles "$t/a" | tr "\0" "\n" | { grep -c JanusASL/Check || true; } | grep -qx 0 && ok "arm scope still excludes JanusASL C" || bad "arm scope leaks"
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

[ $fail = 0 ] && echo "test_asl_obj_cache: all passed" || { echo "test_asl_obj_cache: FAILED"; exit 1; }
