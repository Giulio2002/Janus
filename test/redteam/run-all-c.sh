#!/usr/bin/env bash
# Part c of audit/run-all.sh (row group "root"). A separate lane (allc) of audit/run-rounds.sh.
export ALL_ROWS="root"
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/run-all.sh" "$@"
