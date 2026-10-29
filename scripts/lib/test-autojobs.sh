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
exp "idle 48 cores / 170 GiB (per-item admission: cores bind)" "48 2 170" 12 15
exp "idle 48 cores / 250 GiB" "48 2 250" 12 15
exp "idle, small items (peak 2 GiB)" "48 2 170 2" 12 15
exp "idle, 96 cores / 400 GiB capped at 12" "96 0 400" 12 15
exp "half busy (load 21)" "48 21 170" 5 8
exp "memory tight (80 GiB): still 12 slots, items admitted by their own reservation" "48 2 80" 12 15
exp "high load falls back to 2" "48 62 170" 2 5
exp "few free cores falls back to 2" "48 42 170" 2 5
exp "tiny box (4 cores / 16 GiB)" "4 0 16" 2 5
JANUS_GATE_MAX_JOBS=6 exp "cap from JANUS_GATE_MAX_JOBS" "48 2 170" 6 9
printf '# h\narm64:A\t5\t0.30\narm64:B\t9\t4.00\nlane:x\t7\t30.00\n' > "$t/base"
[ "$(autojobs_peak_gib "$t/base")" = 4.00 ] && ok "peak from the baseline ignores lanes" || bad "peak $(autojobs_peak_gib "$t/base")"
[ -z "$(autojobs_peak_gib "$t/none")" ] && ok "no baseline: no peak" || bad "peak without file"
sz 48 2 170 6.1 | grep -q 'cap 12' && ok "reason names the binding limit" || bad "reason: $(sz 48 2 170)"
rl() { AUTOJOBS_NPROC=$1 AUTOJOBS_LOAD1=$2 AUTOJOBS_MEMKB=$(( $3 * 1048576 )) autojobs_rounds_lanes; }
rexp() { [ "$(rl $2)" = "$3" ] && ok "rounds lanes, $1: $3" || bad "rounds lanes, $1: got $(rl $2), want $3"; }
rexp "idle 48 cores / 170 GiB" "48 2 170" 5
rexp "idle 48 cores / 250 GiB" "48 2 250" 5
rexp "idle 96 cores / 400 GiB (cap 6)" "96 0 400" 6
rexp "memory bound (80 GiB): rounds cut to keep two worst-case items" "48 2 80" 2
rexp "half busy (load 21)" "48 21 170" 3
rexp "high load" "48 62 170" 2
rexp "few free cores" "48 42 170" 2
rexp "tiny box" "4 0 16" 2
# the verify budget + rounds + lanes + floor fits MemAvailable wherever it can (verify keeps room for two worst-case items)
for m in 100 120 140 160 170 200 250 400; do
  for c in 48 96; do
    p=$(AUTOJOBS_NPROC=$c AUTOJOBS_LOAD1=2 AUTOJOBS_MEMKB=$(( m * 1048576 )) autojobs_plan); r=${p%%|*}
    set -- $r; rl=$3; vb=${p##*|}
    tot=$(awk -v v=$vb -v r=$rl 'BEGIN { printf "%.1f", v + r * 15 + 25 + 30 }')
    if awk -v t=$tot -v m=$m 'BEGIN { exit !(t <= m) }' || awk -v v=$vb 'BEGIN { exit !(v <= 18.31) }'; then ok "budget at $c cores / $m GiB: verify $vb + rounds $rl x 15 + 55 = $tot GiB"; else bad "over budget at $c/$m: needs $tot"; fi
  done
done
b=$(AUTOJOBS_NPROC=48 AUTOJOBS_LOAD1=2 AUTOJOBS_MEMKB=$(( 170 * 1048576 )) autojobs_budget)
[ "$b" = "mem budget: verify 40 GiB (per-item admission, 12 slots) + rounds 75 GiB + lanes 25 GiB + floor 30 GiB of 170" ] && ok "budget line: $b" || bad "budget line: $b"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail
