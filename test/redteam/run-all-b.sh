#!/usr/bin/env bash
# Part b of audit/run-all.sh (row group "r1"). A separate lane (allb) of audit/run-rounds.sh.
export ALL_ROWS="r1"
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/run-all.sh" "$@"
