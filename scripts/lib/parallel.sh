# Shared by the example and audit runners: run independent blocks of a script as parallel jobs
# and print their output in the original order. Source it, call `par_init "$@"` (which consumes
# -j N / --jobs N / -jN from the arguments into PAR_ARGS), wrap each independent block in
# `par_run 'shell code'`, and call `par_wait` before the script's verdict.
#
#   -j N        run up to N blocks at once. Default: $JANUS_JOBS, else min(cores / 6,
#               (MemAvailable - 40 GiB) / 10 GiB, 8), at least 1. Before each launch MemAvailable is
#               checked again: while less than 10 GiB above the 40 GiB headroom is free, the next
#               block waits for a running one to finish (memory, not cores, is what concurrent
#               janus verifies exhaust).
#   -j 1        run every block inline, in order, exactly as a plain serial script.
#
# A block runs in a subshell: it sees every variable and function defined so far, its stdout and
# stderr are collected and printed when its turn comes, and anything it appends to the array
# `broken` is appended to the caller's `broken` by par_wait; a block that does not run to its end
# (it fails under `set -e`, or is killed) is recorded in `broken` too. Blocks must not depend on each
# other's side effects; a block that sets up and removes a shared directory does both itself.

# Memory budget per block: the largest measured janus verify peaks at 4.8 GiB (the ClearWords
# proof; a cold kernel replay of the framework 3.0 GiB, a warm verify 0.2-0.5 GiB; docs/TESTING.md
# "Measured peaks"), so a block is budgeted 10 GiB, which is also its cgroup limit under memguard
# ($JANUS_JOB_MEM, default 10G): slots x slot limit stays within MemAvailable minus the 40 GiB of
# headroom the host keeps for everything else.
PAR_JOB_MEM_KB=$((10 * 1024 * 1024))
PAR_HEADROOM_KB=$((40 * 1024 * 1024))
# At most this many jobs by default, and one per 6 cores (each Lean job runs several threads:
# LEAN_NUM_THREADS, the kernel replay's 2 threads); -j/JANUS_JOBS override.
PAR_MAX_DEFAULT_JOBS=8
PAR_CORES_PER_JOB=6

par_mem_available_kb() { awk '/^MemAvailable:/ { print $2 }' /proc/meminfo 2>/dev/null || echo 0; }

# min(cores / 6, (MemAvailable - 40 GiB) / 10 GiB, 8), at least 1.
par_default_jobs() {
  local n mem
  n=$(( $(nproc 2>/dev/null || echo 4) / PAR_CORES_PER_JOB ))
  [ "$n" -gt "$PAR_MAX_DEFAULT_JOBS" ] && n=$PAR_MAX_DEFAULT_JOBS
  mem=$(( ($(par_mem_available_kb) - PAR_HEADROOM_KB) / PAR_JOB_MEM_KB ))
  [ "$mem" -lt "$n" ] && n=$mem
  [ "$n" -lt 1 ] && n=1
  echo "$n"
}

par_init() {
  PAR_JOBS="${JANUS_JOBS:-}"
  PAR_ARGS=()
  while [ $# -gt 0 ]; do
    case "$1" in
      -j|--jobs) PAR_JOBS="${2:?-j needs a number}"; shift 2 ;;
      -j*) PAR_JOBS="${1#-j}"; shift ;;
      --jobs=*) PAR_JOBS="${1#--jobs=}"; shift ;;
      *) PAR_ARGS+=("$1"); shift ;;
    esac
  done
  [ -n "$PAR_JOBS" ] || PAR_JOBS=$(par_default_jobs)
  case "$PAR_JOBS" in ''|*[!0-9]*|0) echo "-j needs a positive number (got '$PAR_JOBS')" >&2; exit 2 ;; esac
  PAR_N=0
  PAR_DIR=""
  if [ "$PAR_JOBS" -gt 1 ]; then
    PAR_DIR="$(mktemp -d "${TMPDIR:-/tmp}/janus-par.XXXXXX")"
    # shellcheck disable=SC2064
    trap "rm -rf '$PAR_DIR'" EXIT
  fi
  declare -p broken >/dev/null 2>&1 || broken=()
  # With scripts/lib/memguard.sh (cgroup v2 memory limits) loaded, every parallel block runs under
  # a job limit of $JANUS_JOB_MEM (default 10G, the budget above); janus nests its per-process
  # limits inside it. A block that hits it is OOM-killed inside its cgroup only and counts as
  # broken. Without memguard the blocks run unguarded (the admission check still applies).
  PAR_GUARD=""
  PAR_JOB_MEM="${JANUS_JOB_MEM:-10G}"
  if [ "$PAR_JOBS" -gt 1 ] && type memguard_run >/dev/null 2>&1; then
    PAR_GUARD=1
  fi
}

# par_run CODE: run the shell code CODE as the next block.
par_run() {
  if [ "$PAR_JOBS" -le 1 ]; then
    eval "$1"
    return 0
  fi
  local __par_i=$PAR_N
  PAR_N=$((PAR_N + 1))
  while [ "$(jobs -rp | wc -l)" -ge "$PAR_JOBS" ]; do wait -n 2>/dev/null || true; done
  # memory check: with at least one block running, wait until a job's budget is free
  while [ "$(jobs -rp | wc -l)" -gt 0 ] &&
        [ "$(par_mem_available_kb)" -lt $((PAR_HEADROOM_KB + PAR_JOB_MEM_KB)) ]; do
    wait -n 2>/dev/null || sleep 2
  done
  (
    broken=()
    if [ -n "$PAR_GUARD" ]; then
      # The block runs in a child bash under the job's memory limit (scripts/lib/memguard.sh);
      # its `broken` rows come back through a file.
      export PAR_BLOCK="$1" PAR_BROKEN_FILE="$PAR_DIR/$__par_i.inner"
      # The child bash gets the caller's functions and its shell variables as they are now.
      # Exported variables are not re-declared: they reach the child through its environment,
      # as memguard_run sets them (e.g. JANUS_MEMGUARD_CGROUP: the slot's cgroup, not the
      # caller's). Readonly ones cannot be.
      PAR_PRELUDE="$(declare -f); $(declare -p 2>/dev/null | grep -vE '^declare -[a-zA-Z]*[rx]')"
      memguard_run -l "$PAR_JOB_MEM" -n "slot$__par_i" -- bash -c "$PAR_PRELUDE"'
        broken=(); eval "$PAR_BLOCK"; st=$?
        if [ ${#broken[@]} -gt 0 ]; then printf "%s\n" "${broken[@]}" > "$PAR_BROKEN_FILE"; fi
        exit $st' || { [ $? -eq 137 ] && broken+=("block-$__par_i-memory-limit"); }
      if [ -f "$PAR_DIR/$__par_i.inner" ]; then while IFS= read -r b; do broken+=("$b"); done < "$PAR_DIR/$__par_i.inner"; fi
    else
      eval "$1"
    fi
    # one entry per line; entries are row names (no newlines)
    if [ ${#broken[@]} -gt 0 ]; then printf '%s\n' "${broken[@]}" > "$PAR_DIR/$__par_i.broken"; fi
    : > "$PAR_DIR/$__par_i.done"
  ) > "$PAR_DIR/$__par_i.out" 2>&1 &
  return 0
}

# par_wait: wait for every block and print their output in order; merge their `broken` rows.
par_wait() {
  [ "$PAR_JOBS" -le 1 ] && return 0
  wait
  local i b
  for ((i = 0; i < PAR_N; i++)); do
    cat "$PAR_DIR/$i.out"
    if [ -f "$PAR_DIR/$i.broken" ]; then
      while IFS= read -r b; do broken+=("$b"); done < "$PAR_DIR/$i.broken"
    fi
    # A block that did not reach its end (an error under set -e, a kill) is a failure.
    if [ ! -f "$PAR_DIR/$i.done" ]; then
      echo "(parallel block $i did not complete)"
      broken+=("block-$i-incomplete")
    fi
    rm -f "$PAR_DIR/$i.out" "$PAR_DIR/$i.broken" "$PAR_DIR/$i.done"
  done
  PAR_N=0
}
