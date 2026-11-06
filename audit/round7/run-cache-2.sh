#!/usr/bin/env bash
# Part 2 of the round-7 cache rows (audit/round7/run-cache.sh): rows rc2 rc4. A separate lane of audit/run-rounds.sh.
export R7C_ROWS="rc2 rc4"
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/run-cache.sh" "$@"
