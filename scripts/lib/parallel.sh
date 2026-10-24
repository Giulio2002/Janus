# Shared by the example and audit runners: run independent blocks of a script as parallel jobs
# and print their output in the original order. Source it, call `par_init "$@"` (which consumes
# -j N / --jobs N / -jN from the arguments into PAR_ARGS), wrap each independent block in
# `par_run 'shell code'`, and call `par_wait` before the script's verdict.
#
#   -j N        run up to N blocks at once. Default: $JANUS_JOBS, else the number of cores,
#               capped at one job per 6 GiB of available memory (a janus verify holds the proof's
#               Lean process, the auditor and up to three leanchecker processes) and at least 1.
#   -j 1        run every block inline, in order, exactly as a plain serial script.
#
# A block runs in a subshell: it sees every variable and function defined so far, its stdout and
# stderr are collected and printed when its turn comes, and anything it appends to the array
# `broken` is appended to the caller's `broken` by par_wait; a block that does not run to its end
# (it fails under `set -e`, or is killed) is recorded in `broken` too. Blocks must not depend on each
# other's side effects; a block that sets up and removes a shared directory does both itself.

par_default_jobs() {
  local n mem
  n=$(nproc 2>/dev/null || echo 1)
  mem=$(awk '/^MemAvailable:/ { printf "%d", $2 / (6 * 1024 * 1024) }' /proc/meminfo 2>/dev/null || echo "$n")
  [ -n "$mem" ] && [ "$mem" -lt "$n" ] && n=$mem
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
}

# par_run CODE: run the shell code CODE as the next block.
par_run() {
  if [ "$PAR_JOBS" -le 1 ]; then
    eval "$1"
    return 0
  fi
  local i=$PAR_N
  PAR_N=$((PAR_N + 1))
  while [ "$(jobs -rp | wc -l)" -ge "$PAR_JOBS" ]; do wait -n 2>/dev/null || true; done
  (
    broken=()
    eval "$1"
    # one entry per line; entries are row names (no newlines)
    if [ ${#broken[@]} -gt 0 ]; then printf '%s\n' "${broken[@]}" > "$PAR_DIR/$i.broken"; fi
    : > "$PAR_DIR/$i.done"
  ) > "$PAR_DIR/$i.out" 2>&1 &
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
