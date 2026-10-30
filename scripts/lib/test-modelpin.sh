#!/usr/bin/env bash
# Self-test of the ISA model pin of the cold gate (scripts/lib/modelpin.py, scripts/model-pin.sh, scripts/gate.sh --cold,
# the pin steps of scripts/asl.sh and scripts/oracle-sail.sh). Every damaged pin must FAIL the gate, never pass:
#   a tampered artifact, a missing artifact, a stale pin (a model input changed), a corrupt manifest, a corrupt or forged
#   record, a manifest re-signed with the real key (the record binds the pinned manifest), an artifact changed after the build.
# And: only the nightly truly-cold run may write a pin; a pin that is not reproduced is not replaced.
# Seconds; everything happens in a mktemp directory on disk (the real pin store and the real build tree are never touched).
#
#   scripts/lib/test-modelpin.sh
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
mp="$root/scripts/lib/modelpin.py"
mkdir -p "$root/artifacts"
t=$(mktemp -d "${TMPDIR:-$root/artifacts}/test-modelpin.XXXXXX")
trap 'chmod -R u+w "$t" 2>/dev/null; rm -rf "$t"' EXIT
export JANUS_CACHE_KEY_DIR="$t/keys"
unset JANUS_MODEL_PIN JANUS_MODEL_PIN_DIR JANUS_MODEL_PIN_STALE JANUS_PIN_WRITER JANUS_COLD_PIN_CHECKED JANUS_COLD_DONE
fail=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fail=1; }
expect() {  # expect RC DESCRIPTION CMD...
  local want=$1 d=$2 rc=0; shift 2
  "$@" > "$t/out" 2> "$t/err" || rc=$?
  if [ "$rc" = "$want" ]; then ok "$d (rc $rc)"; else bad "$d: rc $rc, wanted $want: $(head -c 400 "$t/out" "$t/err" | tr '\n' ' ')"; fi
}
P() { python3 -I "$mp" "$@"; }
W() { JANUS_PIN_WRITER=nightly-cold-gate P write "$@"; }   # W KIND PIN KEY SRC --commit C < rels

# ---------------------------------------------------------------- unit level: modelpin.py on a fake model
K=$(printf 'c%.0s' {1..32}); K2=$(printf 'd%.0s' {1..32})
src="$t/src"; mkdir -p "$src/build/lib/lean/ArmASL" "$src/packages/Sail"
echo olean-one > "$src/build/lib/lean/ArmASL/Part01.olean"; echo olean-two > "$src/build/lib/lean/ArmASL/Part02.olean"
echo trace > "$src/build/lib/lean/ArmASL/Part01.trace"; echo sail > "$src/packages/Sail/Sail.olean"
rels() { printf 'build/lib/lean/ArmASL/Part01.olean\0build/lib/lean/ArmASL/Part02.olean\0build/lib/lean/ArmASL/Part01.trace\0packages/Sail/Sail.olean\0'; }
newpin() { rm -rf "$t/pin"; rels | W armasl "$t/pin" "$K" "$src" --commit abc123 > /dev/null; }
entry="$t/pin/$K"; rec="$t/pin/records/armasl-$K.json"
corrupt_byte() { chmod u+w "$1" "$(dirname "$1")" 2>/dev/null; printf 'X' | dd of="$1" bs=1 seek=0 conv=notrunc status=none; }

rc=0; rels | P write armasl "$t/pin" "$K" "$src" --commit c > /dev/null 2>&1 || rc=$?
[ "$rc" = 2 ] && [ ! -e "$t/pin/records" ] && ok "a pin cannot be written outside the nightly run (rc 2, nothing written)" || bad "write without JANUS_PIN_WRITER: rc $rc"
rc=0; rels | JANUS_MODEL_PIN=1 JANUS_PIN_WRITER=nightly-cold-gate P write armasl "$t/pin" "$K" "$src" --commit c > /dev/null 2>&1 || rc=$?
[ "$rc" = 2 ] && ok "a pin cannot be written from inside a cold gate (rc 2)" || bad "write inside a cold gate: rc $rc"
expect 2 "no pin yet is STALE (not a pass)" P check armasl "$t/pin" "$K"

newpin
expect 0 "a written pin checks (record, manifest, every file)" P check armasl "$t/pin" "$K"
rm -rf "$t/d"; expect 0 "restore into an empty tree" P restore armasl "$t/pin" "$K" "$t/d"
(cd "$src" && find . -type f ! -name .bcache-tree.lock | sort | xargs sha256sum) > "$t/h1"; (cd "$t/d" && find . -type f ! -name .bcache-tree.lock | sort | xargs sha256sum) > "$t/h2"
cmp -s "$t/h1" "$t/h2" && ok "the restored tree is byte-identical to the pinned build" || bad "restored tree differs"
expect 0 "restore again is 'current'" P restore armasl "$t/pin" "$K" "$t/d"
expect 0 "verify-tree on the restored tree" P verify-tree armasl "$t/pin" "$K" "$t/d"
echo changed > "$t/d/build/lib/lean/ArmASL/Part02.olean"
expect 3 "an artifact changed in the tree after the build FAILS verify-tree" P verify-tree armasl "$t/pin" "$K" "$t/d"
rm -f "$t/d/build/lib/lean/ArmASL/Part02.olean"
expect 3 "an artifact missing from the tree after the build FAILS verify-tree" P verify-tree armasl "$t/pin" "$K" "$t/d"

# reproduction: the same inputs rebuilt identically are confirmed; a different .olean is NOT REPRODUCED and the pin is kept
rels | W armasl "$t/pin" "$K" "$src" --commit def456 > "$t/out" 2>&1; grep -q "reproduced, unchanged" "$t/out" && ok "a second truly-cold build with identical files confirms the pin" || bad "reproduction: $(cat "$t/out")"
echo other > "$src/build/lib/lean/ArmASL/Part02.olean"
rc=0; rels | W armasl "$t/pin" "$K" "$src" --commit def456 > "$t/out" 2>&1 || rc=$?
[ "$rc" = 1 ] && grep -q "NOT REPRODUCED" "$t/out" && ok "a differing .olean is NOT REPRODUCED (rc 1)" || bad "non-reproduction: rc $rc $(cat "$t/out")"
expect 0 "the old pin is kept after a non-reproduction" P check armasl "$t/pin" "$K"
echo olean-two > "$src/build/lib/lean/ArmASL/Part02.olean"
echo trace2 > "$src/build/lib/lean/ArmASL/Part01.trace"
rc=0; rels | W armasl "$t/pin" "$K" "$src" --commit def456 > "$t/out" 2>&1 || rc=$?
[ "$rc" = 0 ] && grep -q "only non-semantic" "$t/out" && ok "a differing trace file alone keeps the pin (rc 0, reported)" || bad "trace difference: rc $rc $(cat "$t/out")"
echo trace > "$src/build/lib/lean/ArmASL/Part01.trace"

# 1. a tampered artifact
newpin; corrupt_byte "$entry/tree/build/lib/lean/ArmASL/Part01.olean"
expect 3 "TAMPERED artifact: check FAILS" P check armasl "$t/pin" "$K"
rm -rf "$t/d"; expect 3 "TAMPERED artifact: restore FAILS" P restore armasl "$t/pin" "$K" "$t/d"
[ -z "$(find "$t/d" -type f ! -name .bcache-tree.lock 2>/dev/null)" ] && ok "a rejected restore leaves nothing behind" || bad "files left after a rejected restore"
# 2. a missing artifact
newpin; rm -f "$entry/tree/packages/Sail/Sail.olean"
expect 3 "MISSING artifact: check FAILS" P check armasl "$t/pin" "$K"
rm -rf "$t/d"; expect 3 "MISSING artifact: restore FAILS" P restore armasl "$t/pin" "$K" "$t/d"
newpin; chmod -R u+w "$entry"; rm -rf "$entry"
expect 3 "MISSING pinned entry (record kept): restore FAILS" P restore armasl "$t/pin" "$K" "$t/d"
expect 3 "MISSING pinned entry (record kept): check FAILS" P check armasl "$t/pin" "$K"
# 3. a stale pin: a model input changed, so the key changed
newpin
expect 2 "STALE pin (the key of the changed inputs has no pin): check is STALE, not OK" P check armasl "$t/pin" "$K2"
rm -rf "$t/d"; expect 2 "STALE pin: restore is STALE and copies nothing" P restore armasl "$t/pin" "$K2" "$t/d"
[ -z "$(find "$t/d" -type f ! -name .bcache-tree.lock 2>/dev/null)" ] && ok "a stale pin restores nothing" || bad "stale restore copied files"
cp "$rec" "$t/rec-K"; sed "s/$K/$K2/g" "$t/rec-K" > "$t/pin/records/armasl-$K2.json"
expect 3 "a pin record moved to another key FAILS (the HMAC binds the key)" P check armasl "$t/pin" "$K2"
# 4. a corrupt manifest
newpin; chmod u+w "$entry"; echo "$(printf '0%.0s' {1..64})  evil.olean" >> "$entry/MANIFEST.sha256"
expect 3 "CORRUPT manifest (extra line): check FAILS" P check armasl "$t/pin" "$K"
newpin; chmod u+w "$entry"; printf 'garbage\n' > "$entry/MANIFEST.sha256"
expect 3 "CORRUPT manifest (garbage): restore FAILS" P restore armasl "$t/pin" "$K" "$t/d"
newpin; chmod u+w "$entry"; echo "deadbeef" > "$entry/MANIFEST.hmac"
expect 3 "CORRUPT manifest HMAC: check FAILS" P check armasl "$t/pin" "$K"
newpin; chmod u+w "$entry"; rm -f "$entry/MANIFEST.hmac"
expect 3 "unsigned manifest: check FAILS" P check armasl "$t/pin" "$K"
newpin; chmod u+w "$entry"; rm -f "$entry/MANIFEST.sha256"
expect 3 "missing manifest: restore FAILS" P restore armasl "$t/pin" "$K" "$t/d"
# a manifest re-signed with the real key (an attacker holding it) and matching files is still not THE pin
newpin; chmod -R u+w "$entry"
echo evil > "$entry/tree/build/lib/lean/ArmASL/Part01.olean"
python3 -I - "$mp" "$entry" "$K" <<'PY'
import hashlib, os, sys
sys.path.insert(0, os.path.dirname(sys.argv[1])); import bcache
e, k = sys.argv[2], sys.argv[3]
lines = []
for d, _, fs in os.walk(os.path.join(e, "tree")):
    for f in fs:
        p = os.path.join(d, f); lines.append("%s  %s\n" % (bcache.sha_file(p), os.path.relpath(p, os.path.join(e, "tree"))))
data = "".join(sorted(lines, key=lambda l: l.split("  ")[1])).encode()
open(os.path.join(e, "MANIFEST.sha256"), "wb").write(data)
open(os.path.join(e, "MANIFEST.hmac"), "w").write(bcache.mac("armasl", k, data) + "\n")
PY
expect 3 "a manifest RE-SIGNED over swapped files is not the pinned manifest: check FAILS" P check armasl "$t/pin" "$K"
rm -rf "$t/d"; expect 3 "a re-signed manifest: restore FAILS and copies nothing" P restore armasl "$t/pin" "$K" "$t/d"
# the record
newpin; printf '{"record": {"scheme"' > "$rec"
expect 3 "CORRUPT (truncated) pin record: check FAILS" P check armasl "$t/pin" "$K"
newpin; sed -i 's/"files": 4/"files": 3/' "$rec"
expect 3 "an edited pin record (HMAC) FAILS" P check armasl "$t/pin" "$K"
newpin; : > "$rec"
expect 3 "an empty pin record FAILS" P check armasl "$t/pin" "$K"
newpin; rm -f "$rec"
expect 2 "an entry without a record is not pinned (STALE)" P check armasl "$t/pin" "$K"
# the HMAC key lost: nothing verifies
newpin; mv "$t/keys" "$t/keys.off"; mkdir -m 700 "$t/keys"
expect 3 "a pin written under another HMAC key FAILS" P check armasl "$t/pin" "$K"
rm -rf "$t/keys"; mv "$t/keys.off" "$t/keys"
newpin; expect 0 "(control) the pin holds again" P check armasl "$t/pin" "$K"
# concurrent writers: the second is refused while the first holds the lock
( exec 9> "$t/pin/.pin-write.lock"; flock -n 9 && { rc=0; rels | W armasl "$t/pin" "$K" "$src" --commit x > /dev/null 2>&1 || rc=$?; [ "$rc" = 2 ] && echo locked-ok; } ) > "$t/lk" 2>&1
grep -q locked-ok "$t/lk" && ok "a second pin writer is refused while the lock is held" || bad "pin write lock: $(cat "$t/lk")"
[ -z "$(find "$t/pin" -name '.rec.tmp-*' -o -name '.tmp-*' -o -name '.bad-*' 2>/dev/null)" ] && ok "no temporary files left in the pin store" || bad "temporaries left"

# ---------------------------------------------------------------- gate level: scripts/gate.sh --cold on the REAL keys of this checkout
# (the pins hold fake files: only the checks run, nothing is built; --cold-preflight-only stops after the pin check)
ak=$("$root/scripts/asl.sh" key 2>/dev/null) && sk=$("$root/scripts/oracle-sail.sh" key 2>/dev/null) || { bad "cannot compute the model keys"; ak=""; }
if [ -n "$ak" ]; then
  mkdir -p "$t/gsrc/build/lib/lean/ArmASL" "$t/gsrc/packages/Sail" "$t/ssrc/target/release"
  echo o > "$t/gsrc/build/lib/lean/ArmASL/Part01.olean"; echo s > "$t/gsrc/packages/Sail/Sail.olean"; echo drv > "$t/ssrc/target/release/janus-oracle-sail"
  gpin() { rm -rf "$t/gp"; printf 'build/lib/lean/ArmASL/Part01.olean\0packages/Sail/Sail.olean\0' | W armasl "$t/gp" "$ak" "$t/gsrc" --commit abc > /dev/null &&
           printf 'target/release/janus-oracle-sail\0' | W sail "$t/gp" "$sk" "$t/ssrc" --commit abc > /dev/null; }
  G() { JANUS_MODEL_PIN_DIR="$t/gp" "$root/scripts/gate.sh" --cold --cold-preflight-only "$@"; }
  gpin; expect 0 "gate --cold: a valid pin passes the preflight" G
  grep -q "cold preflight OK" "$t/out" && ok "gate --cold: says the pin holds" || bad "no preflight OK line"
  gpin; chmod u+w "$t/gp/$ak/tree/packages/Sail/Sail.olean" "$t/gp/$ak/tree/packages/Sail"; echo X >> "$t/gp/$ak/tree/packages/Sail/Sail.olean"
  expect 1 "gate --cold: a TAMPERED ArmASL artifact FAILS the gate" G;  grep -q "GATE FAIL (cold)" "$t/out" && ok "  ... with GATE FAIL (cold) and nothing built" || bad "no GATE FAIL line"
  gpin; chmod u+w "$t/gp/sail/$sk/tree/target/release"; rm -f "$t/gp/sail/$sk/tree/target/release/janus-oracle-sail"
  expect 1 "gate --cold: a MISSING Sail driver FAILS the gate" G
  gpin; rm -f "$t/gp/records/armasl-$ak.json"
  expect 1 "gate --cold: a STALE/absent ArmASL pin FAILS the gate" G
  expect 0 "gate --cold --rebuild-stale-model: a stale pin is built inside the gate (preflight passes)" G --rebuild-stale-model
  gpin; mv "$t/gp/records/armasl-$ak.json" "$t/gp/records/armasl-$(printf 'e%.0s' {1..32}).json"
  expect 1 "gate --cold: a pin for OTHER inputs (changed model input) FAILS the gate" G
  gpin; chmod u+w "$t/gp/$ak"; printf 'garbage\n' > "$t/gp/$ak/MANIFEST.sha256"
  expect 1 "gate --cold: a CORRUPT manifest FAILS the gate" G
  expect 1 "gate --cold --rebuild-stale-model: a corrupt manifest still FAILS (only stale may be rebuilt)" G --rebuild-stale-model
  gpin; printf 'x' > "$t/gp/records/sail-$sk.json"
  expect 1 "gate --cold: a CORRUPT Sail pin record FAILS the gate" G
  rm -rf "$t/gp"
  expect 1 "gate --cold: no pin store at all FAILS the gate" G
  expect 2 "gate --cold --incremental is refused" env JANUS_MODEL_PIN_DIR="$t/gp" "$root/scripts/gate.sh" --cold --incremental
  expect 2 "gate --wipe without --cold is refused" "$root/scripts/gate.sh" --wipe
fi

# ---------------------------------------------------------------- build-script level: the pin steps of asl.sh / oracle-sail.sh
# A fake checkout whose scripts and model inputs are the real ones (symlinks), with its own build directories.
fr="$t/fake"; mkdir -p "$fr/JanusASL" "$fr/oracle-sail" "$fr/artifacts"
ln -s "$root/scripts" "$fr/scripts"; ln -s "$root/lean-toolchain" "$fr/lean-toolchain"; ln -s "$root/lakefile.toml" "$fr/lakefile.toml"
[ ! -e "$root/lakefile.lean" ] || ln -s "$root/lakefile.lean" "$fr/lakefile.lean"
for x in vendor tools sail lake-manifest.json lakefile.toml lean-toolchain; do ln -s "$root/JanusASL/$x" "$fr/JanusASL/$x"; done
for x in Cargo.lock Cargo.toml cache_key.py instrument_model.py src; do ln -s "$root/oracle-sail/$x" "$fr/oracle-sail/$x"; done
if [ -n "$ak" ]; then
  A() { JANUS_MODEL_PIN=1 JANUS_MODEL_PIN_DIR="$t/gp" "$fr/scripts/asl.sh" restore; }
  S() { JANUS_MODEL_PIN=1 JANUS_MODEL_PIN_DIR="$t/gp" "$fr/scripts/oracle-sail.sh" build; }
  fresh() { rm -rf "$fr/JanusASL/.lake" "$fr/oracle-sail/target"; }
  gpin; fresh; expect 0 "asl.sh restore from a valid pin" A
  [ "$(cat "$fr/JanusASL/.lake/packages/Sail/Sail.olean" 2>/dev/null)" = s ] && ok "  ... the pinned files are in JanusASL/.lake" || bad "pinned files not restored"
  gpin; chmod u+w "$t/gp/$ak/tree/build/lib/lean/ArmASL/Part01.olean" "$t/gp/$ak/tree/build/lib/lean/ArmASL"; echo X >> "$t/gp/$ak/tree/build/lib/lean/ArmASL/Part01.olean"
  fresh; expect 1 "asl.sh restore: a TAMPERED pinned artifact FAILS (no build around it)" A
  gpin; chmod u+w "$t/gp/$ak/tree/packages/Sail"; rm -f "$t/gp/$ak/tree/packages/Sail/Sail.olean"
  fresh; expect 1 "asl.sh restore: a MISSING pinned artifact FAILS" A
  gpin; rm -f "$t/gp/records/armasl-$ak.json"
  fresh; expect 1 "asl.sh restore: a STALE pin FAILS" A
  fresh; expect 0 "asl.sh restore: a stale pin with JANUS_MODEL_PIN_STALE=rebuild goes on to build from source" env JANUS_MODEL_PIN_STALE=rebuild JANUS_MODEL_PIN=1 JANUS_MODEL_PIN_DIR="$t/gp" "$fr/scripts/asl.sh" restore
  gpin; chmod u+w "$t/gp/$ak"; printf 'garbage\n' > "$t/gp/$ak/MANIFEST.sha256"
  fresh; expect 1 "asl.sh restore: a CORRUPT manifest FAILS" A
  fresh; expect 1 "asl.sh restore: a corrupt manifest FAILS also with JANUS_MODEL_PIN_STALE=rebuild" env JANUS_MODEL_PIN_STALE=rebuild JANUS_MODEL_PIN=1 JANUS_MODEL_PIN_DIR="$t/gp" "$fr/scripts/asl.sh" restore
  gpin; chmod u+w "$t/gp/sail/$sk/tree/target/release"; echo X >> "$t/gp/sail/$sk/tree/target/release/janus-oracle-sail"
  fresh; expect 1 "oracle-sail.sh build: a TAMPERED pinned driver FAILS (no cargo build)" S
  gpin; chmod u+w "$t/gp/sail/$sk/tree/target/release"; rm -f "$t/gp/sail/$sk/tree/target/release/janus-oracle-sail"
  fresh; expect 1 "oracle-sail.sh build: a MISSING pinned driver FAILS" S
  gpin; rm -f "$t/gp/records/sail-$sk.json"
  fresh; expect 1 "oracle-sail.sh build: a STALE pin FAILS" S
  gpin; chmod u+w "$t/gp/sail/$sk"; printf 'garbage\n' > "$t/gp/sail/$sk/MANIFEST.sha256"
  fresh; expect 1 "oracle-sail.sh build: a CORRUPT manifest FAILS" S
  [ ! -e "$fr/oracle-sail/target/release/janus-oracle-sail" ] && ok "  ... no driver was produced" || bad "a driver exists after a failed pin"
fi

[ "$fail" = 0 ] && echo "model pin tests: all passed" || { echo "model pin tests: FAILED"; exit 1; }
