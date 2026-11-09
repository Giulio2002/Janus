#!/usr/bin/env bash
# Measure the peak memory of a command and everything it starts (sandboxed lean processes
# included): scripts/peak-mem.sh CMD [ARG ...]
#
# The command runs in a transient systemd user scope (its own cgroup). Printed on stderr when it
# ends, as one line starting "peak-mem:":
#   cgroup   the cgroup's memory.peak: the most memory charged to the command at any moment
#            (anonymous memory plus the page cache it brought in, e.g. mapped .olean files);
#   rss-sum  the largest sum of the resident sets of all its processes, sampled every 0.2 s;
#   max-proc the largest resident set of a single process, and which program it was.
# The exit status is the command's. Without systemd-run --user it runs the command plainly and
# reports only the sampled values (from the process tree).
set -u
[ $# -gt 0 ] || { echo "usage: $0 CMD [ARG ...]" >&2; exit 2; }
report="$(mktemp "${TMPDIR:-/tmp}/peak-mem.XXXXXX")"
trap 'rm -f "$report"' EXIT

# sampler PIDFILE CGROUP: until the process in PIDFILE exits, record the peak RSS sum and the
# largest process of the cgroup (or of the process tree when CGROUP is empty).
sampler() {
  local main=$1 cg=$2 peak=0 maxp=0 maxn="" pids p rss name sum
  while kill -0 "$main" 2>/dev/null; do
    if [ -n "$cg" ] && [ -r "$cg/cgroup.procs" ]; then
      pids=$(cat "$cg/cgroup.procs" 2>/dev/null)
    else
      pids="$main $(pgrep -P "$main" 2>/dev/null) $(ps -o pid= --ppid "$(pgrep -d, -P "$main" 2>/dev/null || echo 0)" 2>/dev/null)"
    fi
    sum=0
    for p in $pids; do
      rss=$(awk '/^VmRSS:/ { print $2 }' "/proc/$p/status" 2>/dev/null) || continue
      [ -n "$rss" ] || continue
      sum=$((sum + rss))
      if [ "$rss" -gt "$maxp" ]; then maxp=$rss; maxn=$(cat "/proc/$p/comm" 2>/dev/null); fi
    done
    [ "$sum" -gt "$peak" ] && peak=$sum
    echo "$peak $maxp $maxn" > "$report"
    sleep 0.2
  done
}

gb() { awk -v k="$1" 'BEGIN { printf "%.2f GB", k / 1048576 }'; }

if command -v systemd-run >/dev/null && systemd-run --user --scope -q true 2>/dev/null; then
  # Inside the scope: start the command, sample its cgroup, then print memory.peak.
  systemd-run --user --scope -q bash -c '
    cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
    "$@" & main=$!
    '"$(declare -f sampler)"'
    report='"$report"' sampler $main "$cg" &
    wait $main; st=$?
    wait
    echo "$(cat "$cg/memory.peak")" >> '"$report"'
    exit $st' peak-mem "$@"
  st=$?
  { read -r peak maxp maxn; read -r cgpeak; } < "$report"
  echo "peak-mem: cgroup $(gb $(( ${cgpeak:-0} / 1024 ))), rss-sum $(gb "${peak:-0}"), max-proc $(gb "${maxp:-0}") (${maxn:-?})" >&2
  exit $st
fi
"$@" & main=$!
sampler $main "" &
wait $main; st=$?
wait
read -r peak maxp maxn < "$report"
echo "peak-mem: rss-sum $(gb "${peak:-0}"), max-proc $(gb "${maxp:-0}") (${maxn:-?}) (no cgroup)" >&2
exit $st
