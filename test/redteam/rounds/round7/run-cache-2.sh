#!/usr/bin/env bash
# Part 2 of the round-7 cache rows (audit/round7/run-cache.sh): row rc2. A separate lane of audit/run-rounds.sh.
export R7C_ROWS="rc2" R7C_WORK=2
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/run-cache.sh" "$@"
