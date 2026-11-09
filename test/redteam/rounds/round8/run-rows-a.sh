#!/usr/bin/env bash
# Part a of round 8 (audit/round8/run-round8.sh): the --fresh I1 attack rows. A separate lane (r8a) of audit/run-rounds.sh.
export R8_ROWS="fresh"
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/run-round8.sh" "$@"
