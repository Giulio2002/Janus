# shellcheck shell=bash
# Automatic sizing of the gate's pool (-j) and lane count (--lanes) when they are not given.
#
#   autojobs_size            prints "JOBS LANES REASON..." (one line) from the host state
#
# Inputs (each overridable for the self-test scripts/lib/test-autojobs.sh):
#   AUTOJOBS_NPROC     cores (default nproc)            AUTOJOBS_LOAD1   1-minute load (default /proc/loadavg)
#   AUTOJOBS_MEMKB     MemAvailable in kB (/proc/meminfo)
#   AUTOJOBS_PEAK_GIB  per-item peak memory, GiB: the largest recorded peak of a pool item in the speed
#                      baseline (scripts/speed-baseline.tsv, 3rd column) when given by the caller, else 6.1 (the
#                      measured maximum); a safety margin of x1.5 (at least 4 GiB per item) is added
# Knobs: JANUS_GATE_MAX_JOBS (cap, default 12), JANUS_GATE_MEM_FLOOR_GIB (MemAvailable kept free, default 30),
#   JANUS_GATE_LANE_CORES (cores reserved for the other lanes: go test, audit rounds, x86, asl; default 16),
#   JANUS_GATE_LANE_GIB (memory reserved for them: they have their own budgets, default 40),
#   JANUS_GATE_CORES_PER_ITEM (measured: one verify item uses ~2.1 cores, default 2.1)
# Memory: the verify pool gets a BUDGET (MemAvailable - floor - other lanes 25 GiB - round lanes x 15 GiB), shared by
#   its running items through per-item admission (scripts/lib/pool.sh), so -j is limited by cores, not by the worst case.
# Rules: fewer free cores than 8, or a 1-minute load of 60 or more (RULES.md), falls back to 2 jobs. Otherwise
#   jobs = min(cap, (free cores - reserved) / cores per item, (MemAvailable - floor - reserved) / item GiB), at
#   least 2; lanes = min(jobs + 3, 15). The memguard per-job limits are untouched.
autojobs_plan() { # prints: JOBS LANES ROUNDS|REASON|BUDGET
  local nproc=${AUTOJOBS_NPROC:-$(nproc 2>/dev/null || echo 4)} load memkb peak
  load=${AUTOJOBS_LOAD1:-$(awk '{ printf "%d", $1 }' /proc/loadavg 2>/dev/null || echo 0)}
  memkb=${AUTOJOBS_MEMKB:-$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo 2>/dev/null || echo 0)}
  peak=${AUTOJOBS_PEAK_GIB:-6.1}
  awk -v nproc="$nproc" -v ld="$load" -v memkb="$memkb" -v peak="$peak" \
      -v cap="${JANUS_GATE_MAX_JOBS:-12}" -v floor="${JANUS_GATE_MEM_FLOOR_GIB:-30}" \
      -v lcores="${JANUS_GATE_LANE_CORES:-16}" -v lgib="${JANUS_GATE_LANE_GIB:-25}" \
      -v rgib="${JANUS_GATE_ROUND_LANE_GIB:-15}" -v cpi="${JANUS_GATE_CORES_PER_ITEM:-2.1}" 'BEGIN {
    free = nproc - ld; if (free < 0) free = 0
    gib = memkb / 1048576
    item = peak * 1.5; if (item < 4) item = 4
    if (ld >= 60 || free < 8) {
      printf "2 5 2|host busy (load %d of %d cores, %.0f GiB available): fallback -j 2|mem budget: verify %.0f GiB + rounds %.0f GiB + lanes %d GiB + floor %d GiB of %.0f|%.2f\n", \
        ld, nproc, gib, 2 * item, 2 * rgib, lgib, floor, gib, 2 * item; exit
    }
    # independent limits (cores, cap), then the JOINT memory budget of the verify pool and the audit-round lanes
    j = int((free - lcores) / cpi); why = sprintf("cores: (%d free - %d reserved) / %.1f per item", free, lcores, cpi)
    if (cap < j) { j = cap; why = "cap " cap }
    r = int(free / 8); if (r > 6) r = 6
    if (j < 2) { j = 2; why = why " (raised to the minimum 2)" }
    if (r < 2) r = 2
    # The verify pool memory is a BUDGET shared by its running items (per-item admission, scripts/lib/pool.sh:
    # each item reserves its own recorded peak x1.3, the conservative item estimate when unknown), not a charge of
    # the worst case per slot. The round lanes keep 15 GiB each; the budget is what is left after them, the other
    # lanes and the floor. It must hold at least two worst-case items: round lanes are cut first if not.
    r0 = r
    vb = gib - floor - lgib - r * rgib
    while (vb < 2 * item && r > 2) { r--; vb = gib - floor - lgib - r * rgib }
    over = ""
    if (vb < 2 * item) { vb = 2 * item; over = " (OVER BUDGET even at the minimum: the admission floor throttles the pools)" }
    if (r < r0) why = sprintf("memory: round lanes cut %d -> %d to keep room for two worst-case items (after %s)", r0, r, why)
    l = j + 3; if (l > 15) l = 15
    printf "%d %d %d|%s; load %d of %d cores, %.0f GiB available|mem budget: verify %.0f GiB (per-item admission, %d slots) + rounds %.0f GiB + lanes %d GiB + floor %d GiB of %.0f%s|%.2f\n", \
      j, l, r, why, ld, nproc, gib, vb, j, r * rgib, lgib, floor, gib, over, vb
  }'
}

# autojobs_size: "JOBS LANES REASON..." (the verify pool and the lane count; the memory is budgeted jointly with
# the audit-round lanes, see autojobs_plan)
autojobs_size() {
  local p r; p=$(autojobs_plan); r=${p%%|*}
  printf '%s %s %s\n' "${r%% *}" "$(cut -d' ' -f2 <<<"$r")" "$(cut -d'|' -f2 <<<"$p")"
}

# autojobs_budget: the "mem budget: ..." line of the joint budget
autojobs_budget() { autojobs_plan | cut -d'|' -f3; }

# autojobs_verify_budget_gib: the verify pool's memory budget in GiB (for POOL_BUDGET_KB)
autojobs_verify_budget_gib() { autojobs_plan | cut -d'|' -f4; }

# autojobs_peak_gib BASELINE: the largest recorded peak (GiB) of a pool item in the baseline, or empty.
autojobs_peak_gib() {
  [ -f "$1" ] || return 0
  awk -F'\t' '!/^#/ && $1 !~ /^lane:/ && $3 + 0 > m { m = $3 + 0 } END { if (m > 0) printf "%.2f", m }' "$1"
}

# autojobs_rounds_lanes: the number of audit-round lanes (audit/run-rounds.sh JANUS_ROUNDS_LANES): min(6,
# free cores / 8), at least 2, reduced with the verify pool by the joint memory budget; 2 when the host is busy.
autojobs_rounds_lanes() { local p r; p=$(autojobs_plan); r=${p%%|*}; echo "${r##* }"; }
