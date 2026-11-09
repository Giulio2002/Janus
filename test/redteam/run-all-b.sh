#!/usr/bin/env bash
# Part b of test/redteam/run-all.sh (row group "r1"). A separate lane (allb) of test/redteam/run-rounds.sh.
export ALL_ROWS="r1"
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/run-all.sh" "$@"
