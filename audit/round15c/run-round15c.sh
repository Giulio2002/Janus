#!/usr/bin/env bash
# Round-15c rows (RT15C). Every row must be REJECTED, with the reason checked:
#   R2  a module-data file that is a symlink / non-regular file: pinLib refuses it ("not a regular file", fail
#       closed) and planReplayPinned never puts a non-digest pin into a replay key (Go test
#       TestRound15cSymlinkOleanRefused). Before the fix a symlinked olean got one replay key whatever its target.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"; cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
broken=()
. "$root/audit/lib/gotest-row.sh"
gotest_row round15c-R2 memcap go test -count=1 -timeout 60m -run 'TestRound15c' ./cmd/janus && echo "  R2 rejected (not a regular file; plan key follows content)" || broken+=("R2")
[ ${#broken[@]} -gt 0 ] && { echo "round 15c: BROKEN rows: ${broken[*]}"; exit 1; }
echo "round 15c: all rows as expected"
