#!/usr/bin/env bash
# Part a of test/redteam/run-all.sh (row group "base"). A separate lane (alla) of test/redteam/run-rounds.sh.
export ALL_ROWS="base"
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/run-all.sh" "$@"
