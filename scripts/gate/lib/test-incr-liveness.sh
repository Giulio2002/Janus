#!/usr/bin/env bash
# Self-test of scripts/gate/lib/incr-liveness.sh (the gate-side liveness check of the incremental keys), then the check itself on the
# environment it runs in (the gate's, inside lane cachekeys). Mutation style: a gate environment is simulated (GATE_ENV0_NAMES = the
# names present now) and a variable is then ADDED, as a gate script would export it; the check must name it when it is keyed and
# run-specific, and stay quiet when it is skipped, a keyed constant, or not part of any key. A few seconds with the build.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH
mkdir -p "$root/artifacts"
t="$(mktemp -d "$root/artifacts/test-incr-liveness.XXXXXX")" || exit 2
trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
go build -o "$t/janus" ./cmd/janus || { echo "cannot build cmd/janus"; exit 2; }
export LIVENESS_BIN="$t/janus"
# a gate-like environment: the names present at the start of the run
env0="$(compgen -e | sort | tr '\n' ' ')"
# the three runs are independent: they go side by side (each result is reported in order below)
mkdir -p "$t/tmp0"
chk() { # NUMBER NAME=value...   (exported AFTER the start of the simulated gate)
  local n=$1; shift
  env GATE_ENV0_NAMES="$env0" "$@" scripts/gate/lib/incr-liveness.sh > "$t/out$n" 2>&1; echo $? > "$t/rc$n"
}
# 1: run-specific and keyed: MUST be caught, whatever the way it got exported (all at once, each must be named)
LEAKS=(JANUS_LEAK_RUN="$RANDOM" GOFLAGS="-count=$RANDOM" TMPDIR="$t/tmp0" LEAN_LEAK_RUN="$RANDOM" MEMGUARD_LEAK="$RANDOM")
chk 1 "${LEAKS[@]}" &
# 2: skipped bookkeeping, a keyed constant and a variable no key reads: quiet
chk 2 JANUS_GATE_TREE0="stamp$RANDOM" JANUS_LAKEGUARD_PIN="/out/run$RANDOM/.pinned" JANUS_GATE_AUTO_WHY="load $RANDOM" LEAN_NUM_THREADS=4 SOME_OTHER_RUN_VAR="$RANDOM" &
# 3: the check itself, in the environment it runs in (inside the gate: the gate's real exports)
( scripts/gate/lib/incr-liveness.sh > "$t/out3" 2>&1; echo $? > "$t/rc3" ) &
# 4: an ASL_CACHE above the key size limits (a forced miss by design: a random digest per call) is not a leaked variable
mkdir -p "$t/aslc"; for i in 1 2 3; do echo "$i" > "$t/aslc/f$i"; done
( IH_MAX_FILES=1 ASL_CACHE="$t/aslc" scripts/gate/lib/incr-liveness.sh > "$t/out4" 2>&1; echo $? > "$t/rc4" ) &
wait
[ "$(cat "$t/rc4")" = 0 ] && grep -q 'forced miss by design' "$t/out4" && ok "an oversized ASL_CACHE (random digest by design): noted, not a false alarm" || bad "oversized ASL_CACHE: $(cat "$t/out4")"
[ "$(cat "$t/rc1")" = 1 ] && ok "leaked keyed variables: the check fails" || bad "leaked keyed variables not caught: $(cat "$t/out1")"
for kv in "${LEAKS[@]}"; do
  grep -q "keyed and run-specific: ${kv%%=*} " "$t/out1" && ok "  ${kv%%=*} is named" || bad "  ${kv%%=*} is not named: $(cat "$t/out1")"
done
grep -q 'item key differs' "$t/out1" && grep -q 'lane key differs' "$t/out1" && ok "  both the item key and the lane key are checked" || bad "  item/lane keys: $(cat "$t/out1")"
[ "$(cat "$t/rc2")" = 0 ] && ok "skipped bookkeeping, a keyed constant, an unkeyed variable: passes" || bad "false alarm: $(cat "$t/out2")"
[ "$(cat "$t/rc3")" = 0 ] && ok "the live check passes here: $(tail -1 "$t/out3")" || bad "the live check fails here: $(cat "$t/out3")"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
