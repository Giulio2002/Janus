#!/usr/bin/env bash
# Self-test of scripts/lib/autojobs.sh with fake nproc / MemAvailable / load / peak inputs.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
. "$here/autojobs.sh"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-autojobs.XXXXXX")"; trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
sz() { AUTOJOBS_NPROC=$1 AUTOJOBS_LOAD1=$2 AUTOJOBS_MEMKB=$(( $3 * 1048576 )) AUTOJOBS_PEAK_GIB=${4:-6.1} autojobs_size; }
exp() { # NAME "nproc load GiB [peak]" expected-jobs expected-lanes
  local r j l; r=$(sz $2); j=${r%% *}; r=${r#* }; l=${r%% *}
  [ "$j $l" = "$3 $4" ] && ok "$1: -j $j, $l lanes" || bad "$1: got '$j $l', want $3 $4"
}
exp "idle 48 cores / 170 GiB" "48 2 170" 10 13
exp "idle, small items (peak 2 GiB)" "48 2 170 2" 12 15
exp "idle, 96 cores / 400 GiB capped at 12" "96 0 400" 12 15
exp "half busy (load 21)" "48 21 170" 5 8
exp "memory bound (80 GiB)" "48 2 80" 2 5
exp "high load falls back to 2" "48 62 170" 2 5
exp "few free cores falls back to 2" "48 42 170" 2 5
exp "tiny box (4 cores / 16 GiB)" "4 0 16" 2 5
JANUS_GATE_MAX_JOBS=6 exp "cap from JANUS_GATE_MAX_JOBS" "48 2 170" 6 9
printf '# h\narm64:A\t5\t0.30\narm64:B\t9\t4.00\nlane:x\t7\t30.00\n' > "$t/base"
[ "$(autojobs_peak_gib "$t/base")" = 4.00 ] && ok "peak from the baseline ignores lanes" || bad "peak $(autojobs_peak_gib "$t/base")"
[ -z "$(autojobs_peak_gib "$t/none")" ] && ok "no baseline: no peak" || bad "peak without file"
sz 48 2 170 6.1 | grep -q 'memory:' && ok "reason names the binding limit" || bad "reason: $(sz 48 2 170)"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
