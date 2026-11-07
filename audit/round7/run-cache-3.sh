#!/usr/bin/env bash
# Part 3 of the round-7 cache rows (audit/round7/run-cache.sh): rows rc56. A separate lane of audit/run-rounds.sh.
export R7C_ROWS="rc56" R7C_WORK=3
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/run-cache.sh" "$@"
