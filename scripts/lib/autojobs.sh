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
# Rules: fewer free cores than 8, or a 1-minute load of 60 or more (RULES.md), falls back to 2 jobs. Otherwise
#   jobs = min(cap, (free cores - reserved) / cores per item, (MemAvailable - floor - reserved) / item GiB), at
#   least 2; lanes = min(jobs + 3, 15). The memguard per-job limits are untouched.
autojobs_size() {
  local nproc=${AUTOJOBS_NPROC:-$(nproc 2>/dev/null || echo 4)} load memkb peak
  load=${AUTOJOBS_LOAD1:-$(awk '{ printf "%d", $1 }' /proc/loadavg 2>/dev/null || echo 0)}
  memkb=${AUTOJOBS_MEMKB:-$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo 2>/dev/null || echo 0)}
  peak=${AUTOJOBS_PEAK_GIB:-6.1}
  awk -v nproc="$nproc" -v ld="$load" -v memkb="$memkb" -v peak="$peak" \
      -v cap="${JANUS_GATE_MAX_JOBS:-12}" -v floor="${JANUS_GATE_MEM_FLOOR_GIB:-30}" \
      -v lcores="${JANUS_GATE_LANE_CORES:-16}" -v lgib="${JANUS_GATE_LANE_GIB:-40}" \
      -v cpi="${JANUS_GATE_CORES_PER_ITEM:-2.1}" 'BEGIN {
    free = nproc - ld; if (free < 0) free = 0
    gib = memkb / 1048576
    item = peak * 1.5; if (item < 4) item = 4
    if (ld >= 60 || free < 8) {
      printf "2 5 host busy (load %d of %d cores, %.0f GiB available): fallback -j 2\n", ld, nproc, gib; exit
    }
    bycpu = int((free - lcores) / cpi); bymem = int((gib - floor - lgib) / item)
    j = cap; why = "cap " cap
    if (bycpu < j) { j = bycpu; why = sprintf("cores: (%d free - %d reserved) / %.1f per item", free, lcores, cpi) }
    if (bymem < j) { j = bymem; why = sprintf("memory: (%.0f GiB - %d floor - %d reserved) / %.1f GiB per item", gib, floor, lgib, item) }
    if (j < 2) { j = 2; why = why " (raised to the minimum 2)" }
    l = j + 3; if (l > 15) l = 15
    printf "%d %d %s; load %d of %d cores, %.0f GiB available\n", j, l, why, ld, nproc, gib
  }'
}

# autojobs_peak_gib BASELINE: the largest recorded peak (GiB) of a pool item in the baseline, or empty.
autojobs_peak_gib() {
  [ -f "$1" ] || return 0
  awk -F'\t' '!/^#/ && $1 !~ /^lane:/ && $3 + 0 > m { m = $3 + 0 } END { if (m > 0) printf "%.2f", m }' "$1"
}
