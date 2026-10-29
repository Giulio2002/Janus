# shellcheck shell=bash
# Lane count and order of audit/run-rounds.sh (sourced; self-test: scripts/lib/test-roundslanes.sh).
#
# rounds_lane_count CORES LOAD1 MEMAVAIL_KB: how many audit lanes to run at once.
#   Each lane peaks at 8-15 GiB and uses several cores, so: lanes = min(free cores / 8, (MemAvailable -
#   40 GiB) / 15 GiB, 6), at least 2. Under load (1-minute load >= 40) or with MemAvailable <= 120 GiB the
#   answer is 2: the box is shared, and RULES.md caps what one gate may add.
rounds_lane_count() {
  local cores=$1 load=$2 mem_kb=$3 by_cpu by_mem n
  load=${load%%.*}; load=${load:-0}
  if [ "$load" -ge 40 ] || [ "$mem_kb" -le $((120 * 1024 * 1024)) ]; then echo 2; return; fi
  by_cpu=$(( (cores - load) / 8 ))
  by_mem=$(( (mem_kb - 40 * 1024 * 1024) / (15 * 1024 * 1024) ))
  n=$by_cpu; [ "$by_mem" -lt "$n" ] && n=$by_mem; [ "$n" -gt 6 ] && n=6; [ "$n" -lt 2 ] && n=2
  echo "$n"
}

# rounds_longest_first: the default lane order, longest first by measured time (the long cold consumer
# lanes first so they start at once). Lanes not listed are appended by the caller.
rounds_longest_first() { echo "r7c r7j all r5 r9 r10 r8 r7 r11 r6 rfw r2 r12 r3 r4"; }
