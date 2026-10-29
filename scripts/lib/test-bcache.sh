#!/usr/bin/env bash
# Tests of the build-cache integrity layer (scripts/lib/bcache.py), the per-module cache
# (JanusASL/tools/asl_mod_cache.py) and the cache keys (asl_cache_key.py, oracle-sail/cache_key.py):
# a tampered file, manifest or HMAC is rejected and rebuilt, a changed input changes the key, a
# concurrent double build stays consistent. Seconds; everything happens in mktemp directories.
#
#   scripts/lib/test-bcache.sh
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
bc="$root/scripts/lib/bcache.py"
t=$(mktemp -d "${TMPDIR:-/tmp}/test-bcache.XXXXXX")
trap 'rm -rf "$t"' EXIT
export JANUS_CACHE_KEY_DIR="$t/keys"
fail=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fail=1; }
B() { python3 -I "$bc" "$@"; }
expect() {  # expect RC DESCRIPTION CMD...
  local want=$1 d=$2 rc=0; shift 2
  "$@" > "$t/out" 2> "$t/err" || rc=$?
  if [ "$rc" = "$want" ]; then ok "$d (rc $rc)"; else bad "$d: rc $rc, wanted $want: $(head -c 300 "$t/out" "$t/err" | tr '\n' ' ')"; fi
}

K=$(printf 'a%.0s' {1..40})
mkdir -p "$t/src/sub" "$t/cache"
echo one > "$t/src/a.bin"; echo two > "$t/src/sub/b.olean"; printf '#!/bin/sh\necho hi\n' > "$t/src/sub/run"; chmod +x "$t/src/sub/run"
store() { printf 'a.bin\0sub/b.olean\0sub/run\0' | B store "${1:-sail}" "$t/cache" "${2:-$K}" "$t/src"; }
entry="$t/cache/sail/$K"

expect 2 "an empty cache is a miss" B fetch sail "$t/cache" "$K" "$t/d0"
expect 0 "store" store
[ "$(stat -c %a "$t/keys")" = 700 ] && [ "$(stat -c %a "$t/keys/asl-cache.key")" = 600 ] && [ "$(stat -c %s "$t/keys/asl-cache.key")" = 32 ] && ok "the key is 32 bytes, mode 0600, in a 0700 directory" || bad "key file modes"
[ "$(stat -c %a "$entry/tree/a.bin")" = 444 ] && [ "$(stat -c %a "$entry/tree/sub/run")" = 555 ] && ok "cached files are read-only" || bad "cached file modes"
expect 0 "fetch hits" B fetch sail "$t/cache" "$K" "$t/d1"
cmp -s "$t/src/sub/b.olean" "$t/d1/sub/b.olean" && [ -x "$t/d1/sub/run" ] && [ -w "$t/d1/a.bin" ] && ok "the copy is identical, the executable bit kept, the consumer's copy writable" || bad "copy differs"
echo mutated >> "$t/d1/a.bin"
expect 0 "the cache is unchanged by a consumer mutating its copy (verify)" B verify sail "$t/cache" "$K"
B fetch sail "$t/cache" "$K" "$t/d1" > "$t/o"; [ "$(cat "$t/o")" = hit ] && cmp -s "$t/src/a.bin" "$t/d1/a.bin" && ok "a mutated working copy is restored from the cache" || bad "mutated copy not repaired"
B fetch sail "$t/cache" "$K" "$t/d1" > "$t/o"; [ "$(cat "$t/o")" = current ] && ok "an identical working copy is 'current'" || bad "current"
expect 2 "another key is a miss" B fetch sail "$t/cache" "$(printf 'b%.0s' {1..40})" "$t/d1"
expect 3 "an invalid id is refused (rejected: build from source)" B fetch sail "$t/cache" "../x" "$t/d1"

tamper_case() {  # tamper_case DESC COMMAND: run COMMAND on a fresh entry, then fetch must reject and copy nothing
  rm -rf "$t/cache/sail" "$t/dx"; store > /dev/null
  eval "$2"
  local rc=0; B fetch sail "$t/cache" "$K" "$t/dx" > "$t/out" 2> "$t/err" || rc=$?
  if [ "$rc" = 3 ] && [ -z "$(find "$t/dx" -type f ! -name .bcache-tree.lock 2>/dev/null)" ]; then ok "rejected, nothing copied: $1"
  else bad "$1: rc $rc, files copied: $(find "$t/dx" -type f ! -name .bcache-tree.lock 2>/dev/null | tr '\n' ' ')"; fi
  expect 3 "  ... and verify says invalid: $1" B verify sail "$t/cache" "$K"
  # a rebuild then replaces the invalid entry
  store > "$t/out" 2> "$t/err"; B verify sail "$t/cache" "$K" > /dev/null && ok "  ... and the next store replaces it with a valid one" || bad "  ... not replaced: $(cat "$t/err")"
}
tamper_case "a tampered binary" 'chmod u+w "$entry/tree/sub/run"; echo "evil" >> "$entry/tree/sub/run"'
tamper_case "a tampered .olean" 'chmod u+w "$entry/tree/sub/b.olean"; printf X | dd of="$entry/tree/sub/b.olean" bs=1 count=1 conv=notrunc 2>/dev/null'
tamper_case "a missing file" 'rm "$entry/tree/sub/b.olean"'
tamper_case "a file replaced by a symlink" 'rm "$entry/tree/a.bin"; ln -s /etc/passwd "$entry/tree/a.bin"'
tamper_case "a tampered manifest (hash edited)" 'sed -i "1s/^./f/" "$entry/MANIFEST.sha256"'
tamper_case "a tampered manifest and a recomputed sha256 for the binary" 'echo evil > "$entry/tree/a.bin"; h=$(sha256sum "$entry/tree/a.bin" | cut -d" " -f1); sed -i "s/^[0-9a-f]*  a.bin/$h  a.bin/" "$entry/MANIFEST.sha256"'
tamper_case "a manifest with an extra path" 'echo "$(printf 0%.0s {1..64})  ../../x" >> "$entry/MANIFEST.sha256"'
tamper_case "a bad HMAC" 'echo 0000000000000000000000000000000000000000000000000000000000000000 > "$entry/MANIFEST.hmac"'
tamper_case "a missing HMAC (an unsigned entry)" 'rm "$entry/MANIFEST.hmac"'
tamper_case "an empty HMAC file" ': > "$entry/MANIFEST.hmac"'
tamper_case "an entry signed under another key" 'JANUS_CACHE_KEY_DIR="$t/other" B store sail "$t/cache" "$K" "$t/src" < /dev/null >/dev/null 2>&1; rm -rf "$entry"; printf "a.bin\0sub/b.olean\0sub/run\0" | JANUS_CACHE_KEY_DIR="$t/other" B store sail "$t/cache" "$K" "$t/src" >/dev/null'
tamper_case "an entry moved to another id (HMAC binds the id)" 'rm -rf "$t/cache/sail/bbbb"; cp -a "$entry" "$t/cache/sail/bbbb"; rm -rf "$entry"; mv "$t/cache/sail/bbbb" "$entry"; sed -i "s/^/&/" "$entry/MANIFEST.sha256"; printf "a.bin\0" | B store armasl "$t/cache" "$K" "$t/src" >/dev/null; cp "$t/cache/$K/MANIFEST.hmac" "$entry/MANIFEST.hmac"; rm -rf "$t/cache/$K"'
rm -rf "$t/cache/sail"
echo; echo "-- kinds are separate"
store armasl > /dev/null; expect 3 "an armasl entry copied as a sail entry is rejected" bash -c "mkdir -p '$t/cache/sail' && cp -a '$t/cache/$K' '$t/cache/sail/$K' && python3 -I '$bc' fetch sail '$t/cache' '$K' '$t/dk'"
rm -rf "$t/cache"; mkdir -p "$t/cache"

echo; echo "-- an unusable key is never silently skipped"
mkdir -p "$t/badkeys"; chmod 755 "$t/badkeys"
expect 4 "a group-accessible key directory: not used" env JANUS_CACHE_KEY_DIR="$t/badkeys" python3 -I "$bc" fetch sail "$t/cache" "$K" "$t/dn"
mkdir -p "$t/lk"; chmod 700 "$t/lk"; ln -s "$t/keys/asl-cache.key" "$t/lk/asl-cache.key"
expect 4 "a symlinked key: not used" env JANUS_CACHE_KEY_DIR="$t/lk" python3 -I "$bc" fetch sail "$t/cache" "$K" "$t/dn"

echo; echo "-- concurrent double build"
rm -rf "$t/cache"; mkdir -p "$t/cache"
pids=()
for i in 1 2 3 4 5 6 7 8; do
  ( for j in 1 2 3; do store > /dev/null 2>&1 || echo "store failed $i.$j" >> "$t/conc.err"
      B fetch sail "$t/cache" "$K" "$t/cd$i" > /dev/null 2>> "$t/conc.err" || [ $? = 2 ] || echo "fetch failed $i.$j" >> "$t/conc.err"; done ) &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done
[ ! -s "$t/conc.err" ] && ok "8 concurrent store+fetch loops: no failure" || bad "concurrent: $(cat "$t/conc.err")"
B verify sail "$t/cache" "$K" > /dev/null && ok "the entry is valid after the race" || bad "entry invalid after the race"
[ -z "$(find "$t/cache/sail" -maxdepth 1 -name '.tmp-*' -o -maxdepth 1 -name '.bad-*')" ] && ok "no temporary or quarantine directories left" || bad "leftovers: $(ls -a "$t/cache/sail")"
[ "$(ls "$t/cache/sail" | grep -c '^a*$')" = 1 ] && ok "exactly one entry" || bad "entries: $(ls "$t/cache/sail")"
# a reader during a replacement of an invalid entry sees a whole entry or none
rm -rf "$t/cache/sail/$K"/MANIFEST.hmac
( for i in 1 2 3 4 5 6; do store > /dev/null 2>&1 & done; wait )
( for i in 1 2 3 4 5 6; do B fetch sail "$t/cache" "$K" "$t/cr$i" > "$t/cr$i.out" 2>&1; echo $? >> "$t/cr$i.out"; done )
bad_rc=$(cat "$t"/cr*.out | grep -E '^[0-9]+$' | grep -vE '^(0|2)$' || true)
[ -z "$bad_rc" ] && B verify sail "$t/cache" "$K" >/dev/null && ok "an invalid entry replaced by 6 concurrent publishers ends valid; readers saw hit or miss only" || bad "replace race: $bad_rc"

echo; echo "-- many fetchers into ONE tree (the gate's lanes share an isolated tree)"
rm -rf "$t/cache" "$t/shared"; mkdir -p "$t/cache" "$t/shared"
# a bigger entry, so the copies overlap
mkdir -p "$t/big/sub"; for i in $(seq 1 40); do head -c 1500000 /dev/urandom > "$t/big/sub/f$i.olean"; done; echo meta > "$t/big/m"
(cd "$t/big" && find . -type f -printf '%P\0') | B store sail "$t/cache" "$K" "$t/big" > /dev/null
pids=()
for i in 1 2 3 4 5 6 7 8; do
  ( B fetch sail "$t/cache" "$K" "$t/shared" > "$t/sf$i.out" 2> "$t/sf$i.err"; echo $? >> "$t/sf$i.out" ) &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done
badf=$(cat "$t"/sf*.out | grep -E '^[0-9]+$' | grep -vc '^0$'); rej=$(cat "$t"/sf*.err | grep -c REJECTED)
[ "$badf" = 0 ] && [ "$rej" = 0 ] && ok "8 concurrent fetches into one tree: all succeed, none REJECTED" || bad "concurrent fetches: $badf failed, $rej rejected: $(cat "$t"/sf*.err | head -3)"
n=0; for f in $(cd "$t/big" && find . -type f -printf '%P\n'); do cmp -s "$t/big/$f" "$t/shared/$f" && n=$((n+1)); done
[ "$n" = 41 ] && ok "every one of the 41 files is present and identical" || bad "only $n of 41 files identical"
[ -z "$(find "$t/shared" -name '*.bcache-tmp*')" ] && ok "no temporary files left" || bad "temporaries left: $(find "$t/shared" -name '*.bcache-tmp*' | head -3)"
hits=$(cat "$t"/sf*.out | grep -c '^hit$'); cur=$(cat "$t"/sf*.out | grep -c '^current$')
[ "$hits" = 1 ] && [ "$cur" = 7 ] && ok "exactly one fetch materialised (hit), the 7 others found the finished tree and verified it (current)" || bad "hit=$hits current=$cur"

echo; echo "-- a rejected fetch leaves the tree as it was"
rm -rf "$t/pre"; mkdir -p "$t/pre/sub"; echo mine > "$t/pre/sub/f1.olean"; echo other > "$t/pre/unrelated"; echo "partial" > "$t/pre/m"
snap() { (cd "$t/pre" && find . -type f ! -name .bcache-tree.lock -print0 | sort -z | xargs -0 sha256sum); }
b0=$(snap)
e="$t/cache/sail/$K"; chmod u+w "$e/tree/sub/f20.olean"; printf X | dd of="$e/tree/sub/f20.olean" bs=1 count=1 seek=100 conv=notrunc 2>/dev/null
expect 3 "a tampered entry is rejected" B fetch sail "$t/cache" "$K" "$t/pre"
[ "$(snap)" = "$b0" ] && ok "the tree is byte-for-byte what it was before (nothing partially populated, nothing deleted)" || bad "the rejected fetch changed the tree"
[ -z "$(find "$t/pre" -name '*.bcache-tmp*')" ] && ok "and no temporaries remain" || bad "temporaries remain"
rm -rf "$t/cache/sail"; (cd "$t/big" && find . -type f -printf '%P\0') | B store sail "$t/cache" "$K" "$t/big" > /dev/null

echo; echo "-- a materialiser killed mid-way is repaired by the next fetch"
for when in 0.05 0.15 0.3; do
  rm -rf "$t/kill"; mkdir -p "$t/kill"
  python3 -I "$bc" fetch sail "$t/cache" "$K" "$t/kill" > /dev/null 2>&1 & kp=$!
  sleep "$when"; kill -9 "$kp" 2>/dev/null; wait "$kp" 2>/dev/null
  B fetch sail "$t/cache" "$K" "$t/kill" > "$t/kf.out" 2>&1; rc=$?
  n=0; for f in $(cd "$t/big" && find . -type f -printf '%P\n'); do cmp -s "$t/big/$f" "$t/kill/$f" && n=$((n+1)); done
  [ "$rc" = 0 ] && [ "$n" = 41 ] && [ -z "$(find "$t/kill" -name '*.bcache-tmp*')" ] && ok "killed after ${when}s: the next fetch ($(cat "$t/kf.out")) leaves 41 verified files and no temporaries" || bad "killed after ${when}s: next fetch rc=$rc, $n/41 files, $(cat "$t/kf.out")"
done
# stale temporaries from a dead process are swept, and a half-replaced tree is repaired
rm -rf "$t/kill"; B fetch sail "$t/cache" "$K" "$t/kill" >/dev/null; echo junk > "$t/kill/sub/f3.olean.bcache-tmp.1.deadbeef"; echo garbage > "$t/kill/sub/f7.olean"
B fetch sail "$t/cache" "$K" "$t/kill" > "$t/kf.out"; cmp -s "$t/big/sub/f7.olean" "$t/kill/sub/f7.olean" && [ -z "$(find "$t/kill" -name '*.bcache-tmp*')" ] && ok "a stale temporary is swept and a half-replaced file repaired ($(cat "$t/kf.out"))" || bad "stale state not repaired"

echo; echo "-- keys: a changed input is a different key"
cp_tree() { rm -rf "$1"; mkdir -p "$1"; rsync -a --exclude=.git --exclude=.lake --exclude=artifacts --exclude=target --exclude=ArmASL --exclude=ArmASL.lean --exclude=bin "$root/" "$1/"; }
cp_tree "$t/k"
skey() { python3 -I "$1/oracle-sail/cache_key.py" "$1" --pins crate_rev=x sail_model=vendored; }
akey() { python3 -I "$1/JanusASL/tools/asl_cache_key.py" "$1"; }
sk0=$(skey "$t/k"); ak0=$(akey "$t/k")
[ "$sk0" = "$(skey "$t/k")" ] && ok "sail key is deterministic" || bad "sail key unstable"
chk() {  # chk DESC KEYFN EDIT-CMD
  cp_tree "$t/k2"; (cd "$t/k2" && eval "$3")
  local a b; a=$($2 "$t/k") ; b=$($2 "$t/k2")
  if [ "$a" != "$b" ]; then ok "key changes: $1"; else bad "key unchanged: $1"; fi
}
chk "sail driver source" skey 'echo "// x" >> oracle-sail/src/main.rs'
chk "Cargo.lock" skey 'echo "# x" >> oracle-sail/Cargo.lock'
chk "Cargo.toml" skey 'echo "# x" >> oracle-sail/Cargo.toml'
chk "the model instrumenter" skey 'echo "# x" >> oracle-sail/instrument_model.py'
chk "a cargo config" skey 'mkdir -p oracle-sail/.cargo; echo "[build]" > oracle-sail/.cargo/config.toml'
chk_env() { local a b; a=$($2 "$t/k"); b=$(export "$3"; $2 "$t/k"); [ "$a" != "$b" ] && ok "key changes: $1" || bad "key unchanged: $1"; }
chk_env "RUSTFLAGS" skey RUSTFLAGS=-Cdebuginfo=2
chk_env "CXXFLAGS" skey CXXFLAGS=-O0
chk_env "CXX" skey CXX=g++
chk "ArmASL model tarball digest" akey 'python3 -c "p=\"JanusASL/vendor/ArmASL.tar.gz.sha256\"; s=open(p).read(); open(p,\"w\").write((\"0\" if s[0]!=\"0\" else \"1\")+s[1:])"'
chk "the splitter" akey 'echo "# x" >> JanusASL/sail/split_lean.py'
chk "ArmASL lib options" akey 'sed -i "s/--tstack=400000/--tstack=400001/" JanusASL/lakefile.toml'
chk "lean-sail manifest entry" akey 'sed -i "s/01bb54c7c8a69e52ba11863c67e7c403a6cd198a/01bb54c7c8a69e52ba11863c67e7c403a6cd198b/" JanusASL/lake-manifest.json'
chk_env "the compiler environment (CC)" akey CC=gcc
chk_env "LEAN_CC" akey LEAN_CC=gcc
modk() { python3 -I "$1/JanusASL/tools/asl_mod_cache.py" keys "$1" | sort | sha256sum; }
chk "a JanusASL proof module" modk 'echo "-- x" >> JanusASL/JanusASL/Proofs/Madd.lean'
chk "a framework module imported by the proofs" modk 'echo "-- x" >> Janus/Arm64/State.lean'
chk_env "CFLAGS (mod keys)" modk CFLAGS=-O0

echo; echo "-- the per-module cache: tampering is rejected"
cp_tree "$t/m"
M=JanusASL.Audit
fake_build() { mkdir -p "$t/m/JanusASL/.lake/build/lib/lean/JanusASL"
  for x in olean:OLEAN-bytes ilean:{} trace:{} hash:1; do printf '%s' "${x#*:}" > "$t/m/JanusASL/.lake/build/lib/lean/JanusASL/Audit.${x%%:*}"; done; }
fake_build
mk=$(python3 -I "$t/m/JanusASL/tools/asl_mod_cache.py" keys "$t/m" | awk '$1=="JanusASL.Audit"{print $2}')
mc="$t/modcache"; mp="python3 -I $t/m/JanusASL/tools/asl_mod_cache.py"
$mp publish "$t/m" "$mc" JanusASL.Audit > "$t/pub.out" 2>&1; grep -q 'stored 1 modules' "$t/pub.out" && ok "publish stores the built module" || bad "publish: $(cat "$t/pub.out")"
e="$mc/mods/${mk:0:2}/$mk"
[ -f "$e/MANIFEST.hmac" ] && ok "the module entry carries an HMAC" || bad "no HMAC on the module entry"
out="$t/m/JanusASL/.lake/build/lib/lean/JanusASL/Audit.olean"
mrestore() { rm -f "$t"/m/JanusASL/.lake/build/lib/lean/JanusASL/Audit.*; $mp restore "$t/m" "$mc" 2>&1; }
mrestore | grep -q 'restored 1 modules' && cmp -s <(printf OLEAN-bytes) "$out" && ok "restore copies the module back" || bad "restore"
r=$(mrestore); echo "$r" | grep -q 'restored 1 modules' && ok "restore (again) hits" || bad "second restore: $r"
# eight concurrent restores into the same tree (the gate's lanes share one): all succeed, the module is intact
rm -f "$t"/m/JanusASL/.lake/build/lib/lean/JanusASL/Audit.*
pids=(); for i in 1 2 3 4 5 6 7 8; do ( $mp restore "$t/m" "$mc" > "$t/mr$i.out" 2>&1 ) & pids+=($!); done; for p in "${pids[@]}"; do wait "$p"; done
rej=$(cat "$t"/mr?.out | grep -c '[1-9][0-9]* rejected'); okc=$(cat "$t"/mr?.out | grep -c 'rejected (')
cmp -s <(printf OLEAN-bytes) "$out" && [ "$rej" = 0 ] && [ -z "$(find "$t/m/JanusASL/.lake" -name '*.asl-cache-tmp*' -o -name '*.bcache-tmp*')" ] && ok "8 concurrent module restores into one tree: none rejected, the module is intact, no temporaries" || bad "concurrent module restores: rejected=$rej: $(cat "$t"/mr1.out | head -3)"
chmod u+w "$e/tree/janusasl/.lake/build/lib/lean/JanusASL/Audit.olean"; printf EVIL >> "$e/tree/janusasl/.lake/build/lib/lean/JanusASL/Audit.olean"
r=$(mrestore); if echo "$r" | grep -q '1 rejected' && [ -z "$(ls "$t"/m/JanusASL/.lake/build/lib/lean/JanusASL/Audit.* 2>/dev/null)" ]; then ok "a tampered cached .olean is rejected and no output is left (Lake builds it)"; else bad "tampered olean: $r"; fi
[ ! -d "$e" ] && ok "the rejected entry is quarantined" || bad "rejected entry still in place"
$mp publish "$t/m" "$mc" JanusASL.Audit > "$t/pub.out" 2>&1
# republish needs the build outputs again
fake_build
$mp publish "$t/m" "$mc" JanusASL.Audit > "$t/pub.out" 2>&1; grep -q 'stored 1 modules' "$t/pub.out" && ok "the next publish stores a fresh entry" || bad "republish: $(cat "$t/pub.out")"
rm -f "$e/MANIFEST.hmac"; r=$(mrestore); echo "$r" | grep -q '1 rejected' && ok "an unsigned module entry is rejected" || bad "unsigned: $r"
fake_build
$mp publish "$t/m" "$mc" JanusASL.Audit > /dev/null 2>&1
sed -i '1s/^./f/' "$e/MANIFEST.sha256"; r=$(mrestore); echo "$r" | grep -q '1 rejected' && ok "a tampered module manifest is rejected" || bad "manifest: $r"
cp_tree "$t/m2"; echo "-- x" >> "$t/m2/JanusASL/JanusASL/Audit.lean"
[ "$(python3 -I "$t/m2/JanusASL/tools/asl_mod_cache.py" keys "$t/m2" | awk '$1=="JanusASL.Audit"{print $2}')" != "$mk" ] && ok "an edited module has another key, so the old entry is not even looked at" || bad "edited module kept its key"

[ "$fail" = 0 ] && echo "bcache tests: all passed" || { echo "bcache tests: FAILED"; exit 1; }
