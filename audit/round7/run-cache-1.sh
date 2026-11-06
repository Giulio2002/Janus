#!/usr/bin/env bash
# Part 1 of the round-7 cache rows (audit/round7/run-cache.sh): rows priming rc1 rc3. A separate lane of audit/run-rounds.sh.
export R7C_ROWS="priming rc1 rc3"
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/run-cache.sh" "$@"
