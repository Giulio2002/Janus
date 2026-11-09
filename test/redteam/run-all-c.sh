#!/usr/bin/env bash
# Part c of test/redteam/run-all.sh (row group "root"). A separate lane (allc) of test/redteam/run-rounds.sh.
export ALL_ROWS="root"
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/run-all.sh" "$@"
