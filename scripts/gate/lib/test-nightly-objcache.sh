#!/usr/bin/env bash
# The nightly cold gate's object-cache wiring, end to end on a STUB repository (scripts/gate/nightly-cold-gate.sh is the real
# script; gate.sh, asl.sh, model-pin.sh and the object audit are stubs that log how they were called):
#   - the cached run turns the object cache ON and does not set JANUS_ASL_CACHE; the cold run gets JANUS_ASL_CACHE=0 and
#     ASL_OBJ_CACHE=0, both for the gate AND for the link step that makes the compiled objects exist to be hashed;
#   - a failing object audit makes the nightly exit 1 and no model pin is written;
#   - compiled objects that differ between the cached and the cold run are P0 (exit 1), no pin;
#   - everything agreeing writes the pin; the summary labels the object-cache setting of each run.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
t=$(mktemp -d "${TMPDIR:-/tmp}/test-nightly-objcache.XXXXXX"); trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
repo="$t/repo"; mkdir -p "$repo/scripts/gate/lib" "$repo/scripts/build" "$repo/validation/reference-models/sail-arm"; cd "$repo"
git init -q . && git config user.email t@t && git config user.name t
cp "$root/scripts/gate/nightly-cold-gate.sh" scripts/gate/; cp "$root/scripts/gate/gate-cachecmp.py" scripts/gate/
cat > scripts/gate/gate.sh <<'S'
#!/usr/bin/env bash
out=""; while [ $# -gt 0 ]; do case "$1" in --out) out="$2"; shift 2 ;; *) shift ;; esac; done
echo "gate cwd=$(basename "$PWD") JANUS_ASL_CACHE=${JANUS_ASL_CACHE-unset} ASL_OBJ_CACHE=${ASL_OBJ_CACHE-unset}" >> "$STUB/calls.log"
mkdir -p "$out"; c=$(git rev-parse HEAD)
printf '{"kind":"gate","commit":"%s","jobs":2}\n{"kind":"stage","name":"asl-build","rc":0}\n' "$c" > "$out/timeline.jsonl"
S
cat > scripts/build/asl.sh <<'S'
#!/usr/bin/env bash
echo "asl $* cwd=$(basename "$PWD") JANUS_ASL_CACHE=${JANUS_ASL_CACHE-unset} ASL_OBJ_CACHE=${ASL_OBJ_CACHE-unset}" >> "$STUB/calls.log"
mkdir -p .lake/build/ir/Janus models/asl/.lake/build/lib/lean models/asl/.lake/build/ir/ArmASL
echo c > .lake/build/ir/Janus/Foo.c
case "$(cat "$STUB/mode")" in same) echo obj > .lake/build/ir/Janus/Foo.c.o.export ;; *) echo "obj-${JANUS_ASL_CACHE-unset}" > .lake/build/ir/Janus/Foo.c.o.export ;; esac
S
cat > scripts/gate/model-pin.sh <<'S'
#!/usr/bin/env bash
echo "pin $*" >> "$STUB/calls.log"
S
cat > scripts/gate/lib/nightly-objaudit.sh <<'S'
#!/usr/bin/env bash
echo "objaudit $*" >> "$STUB/calls.log"; exit "$(cat "$STUB/audit.rc")"
S
chmod +x scripts/gate/*.sh scripts/build/*.sh scripts/gate/lib/*.sh
git add -A; git commit -qm stub
run() {  # run MODE AUDIT_RC
  export STUB="$t/stub"; rm -rf "$STUB" "$t/work"; mkdir -p "$STUB"; echo "$1" > "$STUB/mode"; echo "$2" > "$STUB/audit.rc"
  ASL_CACHE="$t/cache" scripts/gate/nightly-cold-gate.sh --commit HEAD --work "$t/work" --keep > "$t/out" 2>&1; echo $? > "$t/rc"
}
run same 0
[ "$(cat "$t/rc")" = 0 ] && ok "all agree + audit passes: exit 0" || bad "agree: rc $(cat "$t/rc"): $(tail -5 "$t/out")"
grep -q "^pin write" "$STUB/calls.log" && ok "  ... the model pin is written" || bad "no pin"
grep -q "^gate cwd=tree-cached JANUS_ASL_CACHE=unset ASL_OBJ_CACHE=1" "$STUB/calls.log" && ok "the cached gate runs with the object cache ON and JANUS_ASL_CACHE unset" || bad "cached gate env: $(cat "$STUB/calls.log")"
grep -q "^gate cwd=tree-cold JANUS_ASL_CACHE=0 ASL_OBJ_CACHE=0" "$STUB/calls.log" && ok "the cold gate runs with JANUS_ASL_CACHE=0 and the object cache OFF" || bad "cold gate env"
grep -q "^asl build cwd=tree-cold JANUS_ASL_CACHE=0 ASL_OBJ_CACHE=0" "$STUB/calls.log" && ok "the cold link step (compiles the objects from source) also gets JANUS_ASL_CACHE=0 and the object cache OFF" || bad "cold link env"
grep -q "^asl build cwd=tree-cached JANUS_ASL_CACHE=unset ASL_OBJ_CACHE=1" "$STUB/calls.log" && ok "the cached link step runs with the object cache ON" || bad "cached link env"
grep -q "^objaudit $t/work/tree-cold $t/cache" "$STUB/calls.log" && ok "the object audit runs on the COLD tree against the cache" || bad "audit args"
grep -q "object cache: ON (cached run), OFF (cold run" "$t/out" && ok "the summary labels the object-cache setting of each run" || bad "no object-cache label: $(head -5 "$t/out")"
run same 1
[ "$(cat "$t/rc")" = 1 ] && ok "a failing object audit makes the nightly exit 1" || bad "audit failure rc $(cat "$t/rc")"
grep -q "^pin write" "$STUB/calls.log" && bad "the pin was written despite a failing audit" || ok "  ... and no pin is written"
run differ 0
[ "$(cat "$t/rc")" = 1 ] && grep -q "P0 CACHE BUG" "$t/out" && ok "compiled objects that differ between the cached and the cold run: P0, exit 1" || bad "differ: rc $(cat "$t/rc"): $(tail -5 "$t/out")"
grep -q "^pin write" "$STUB/calls.log" && bad "pin written on P0" || ok "  ... and no pin is written"
[ "$fail" = 0 ] && echo "nightly object-cache wiring tests: all passed" || { echo "nightly object-cache wiring tests: FAILED"; exit 1; }
