#!/usr/bin/env bash
# Part c of round 8 (audit/round8/run-round8.sh): G3, M1, C1 and the unit rows. A separate lane (r8c) of audit/run-rounds.sh.
export R8_ROWS="rest"
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/run-round8.sh" "$@"
