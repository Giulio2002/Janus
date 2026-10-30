#!/usr/bin/env bash
# Self-test of scripts/lib/incr-liveness.sh (the gate-side liveness check of the incremental keys), then the check itself on the
# environment it runs in (the gate's, inside lane cachekeys). Mutation style: a gate environment is simulated (GATE_ENV0_NAMES = the
# names present now) and a variable is then ADDED, as a gate script would export it; the check must name it when it is keyed and
# run-specific, and stay quiet when it is skipped, a keyed constant, or not part of any key. A few seconds with the build.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH
mkdir -p "$root/artifacts"
t="$(mktemp -d "$root/artifacts/test-incr-liveness.XXXXXX")" || exit 2
trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
go build -o "$t/janus" ./cmd/janus || { echo "cannot build cmd/janus"; exit 2; }
export JANUS_LIVENESS_BIN="$t/janus"
# a gate-like environment: the names present at the start of the run
env0="$(compgen -e | sort | tr '\n' ' ')"
case_() { # WANT(0|1) DESCRIPTION NAME=value...   (the variables are exported AFTER the start of the simulated gate)
  local want=$1 what=$2 out rc kv; shift 2
  out="$(env GATE_ENV0_NAMES="$env0" "$@" scripts/lib/incr-liveness.sh 2>&1)"; rc=$?
  if [ "$rc" != "$want" ]; then bad "$what: rc $rc, wanted $want: $out"; return; fi
  if [ "$want" = 1 ]; then
    for kv in "$@"; do
      grep -q "keyed and run-specific: ${kv%%=*} " <<<"$out" && ok "$what: ${kv%%=*} reported" || bad "$what: failed but did not name ${kv%%=*}: $out"
    done
  else ok "$what: passes"; fi
}
# run-specific and keyed: MUST be caught, whatever the way it got exported (all at once, each must be named)
mkdir -p "$t/tmp0"
case_ 1 "leaked keyed variables" JANUS_LEAK_RUN="$RANDOM" GOFLAGS="-count=$RANDOM" TMPDIR="$t/tmp0" LEAN_LEAK_RUN="$RANDOM" MEMGUARD_LEAK="$RANDOM"
# skipped bookkeeping, keyed constants and variables that are not part of a key: quiet
case_ 0 "skipped bookkeeping, a keyed constant, an unkeyed variable" JANUS_GATE_TREE0="stamp$RANDOM" JANUS_LAKEGUARD_PIN="/out/run$RANDOM/.pinned" \
  JANUS_GATE_AUTO_WHY="load $RANDOM" LEAN_NUM_THREADS=4 SOME_OTHER_RUN_VAR="$RANDOM"
# the check itself, in the environment it runs in
if scripts/lib/incr-liveness.sh; then ok "the live check passes here"; else bad "the live check fails here"; fi
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
