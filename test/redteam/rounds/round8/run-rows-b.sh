#!/usr/bin/env bash
# Part b of round 8 (test/redteam/rounds/round8/run-round8.sh): the I1 control rows and N1. A separate lane (r8b) of test/redteam/run-rounds.sh.
export R8_ROWS="ctl"
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/run-round8.sh" "$@"
