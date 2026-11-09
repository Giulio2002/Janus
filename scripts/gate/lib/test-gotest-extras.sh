#!/usr/bin/env bash
# The gotest lane's nightly extras (scripts/gotest-shards.sh): the mathlib and pressure extras stay on; the ASL extra is OPT-IN
# (JANUS_TEST_ASL_EXTRA=1) until it is private-copy based and heavy-lock aware (QUEUE.md), and its gap stays visible.
#   scripts/lib/test-gotest-extras.sh      (milliseconds)
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
f="$here/scripts/gotest-shards.sh"
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
bash -n "$f" && ok "gotest-shards.sh parses" || bad "gotest-shards.sh syntax"
grep -qF '[ "$lab" = asl ] && [ "${JANUS_TEST_ASL_EXTRA:-}" != 1 ] && continue' "$f" || grep -qF 'if [ "$lab" = asl ] && [ "${JANUS_TEST_ASL_EXTRA:-}" != 1 ]; then continue; fi' "$f" \
  && ok "the ASL extra is skipped unless JANUS_TEST_ASL_EXTRA=1" || bad "the ASL extra is not opt-in"
# the opt-out line must come before the line that queues the deferred ASL run
a=$(grep -n 'JANUS_TEST_ASL_EXTRA:-}" != 1 \]; then continue' "$f" | head -1 | cut -d: -f1); b=$(grep -n 'asl_deferred=("\$lab"' "$f" | head -1 | cut -d: -f1)
[ -n "$a" ] && [ -n "$b" ] && [ "$a" -lt "$b" ] && ok "the opt-in check precedes the deferred ASL run" || bad "ordering of the opt-in check ($a) and the ASL queueing ($b)"
grep -q '"pressure|TestReplayUnderMemoryPressure|' "$f" && grep -q '"mathlib|TestConsumerMathlib|' "$f" && ok "the pressure and mathlib extras are still defined" || bad "pressure/mathlib extras missing"
grep -q 'the ASL extra is opt-in' "$f" && grep -q 'SKIPPED-COVERAGE' "$f" && ok "the SKIPPED-COVERAGE summary names the ASL gap" || bad "the ASL gap would be silent"
exit $fail
