#!/usr/bin/env bash
# The self-tests that use the work queue run with a private out dir and timeline, whatever the environment: run each
# with POOL_TIMELINE / JANUS_POOL_DIR pointing at "the running gate's" files and check nothing was written there.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-isolation.XXXXXX")"; trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
mkdir -p "$t/gate-pool"
for s in test-pool test-poolmem test-pgcancel; do
  : > "$t/gate-timeline.jsonl"; rm -rf "$t/gate-pool"/*
  POOL_TIMELINE="$t/gate-timeline.jsonl" JANUS_POOL_DIR="$t/gate-pool" POOL_BUDGET_KB=1 JANUS_GATE_AUTO_WHY=x \
    bash "$here/$s.sh" > "$t/$s.out" 2>&1; rc=$?
  if [ "$rc" = 0 ] && [ ! -s "$t/gate-timeline.jsonl" ] && [ -z "$(ls -A "$t/gate-pool")" ]; then ok "$s wrote nothing to the inherited timeline / pool dir"
  else bad "$s: rc=$rc timeline=$(wc -c < "$t/gate-timeline.jsonl") bytes pool dir: $(ls "$t/gate-pool" | head -2)"; fi
done
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
