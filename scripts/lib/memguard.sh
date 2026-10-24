# shellcheck shell=bash
# Hard memory guard for scripts that run Lean, lake or go test (sourced; also executable as
# `bash scripts/lib/memguard.sh run …`). The shell side of cmd/janus/memguard.go: a command
# runs inside a cgroup v2 memory limit (memory.max, no swap), so a runaway Lean process is
# killed on its own by the kernel's cgroup OOM killer instead of taking the host down.
#
#   memguard_run [-l LIMIT] [-n LABEL] -- CMD ARGS...
#       run CMD under LIMIT (default $JANUS_MEM_MAX, else min(24G, 40% of MemTotal); "off"
#       disables). Prints one line on stderr: "memguard[LABEL]: peak X / limit Y (MECH)", plus
#       "OOM-KILLED" when the kernel killed something inside; returns CMD's status, or 137 on an
#       OOM kill.
#   memguard_lake ARGS...      lake ARGS under the guard, LEAN_NUM_THREADS (= lake's job count)
#                              from the budget: memguard_jobs 3G (JANUS_LAKE_JOB_MEM).
#   memguard_self "$@"         re-run the calling script, once, inside a script-wide guard of
#                              max(limit, MemAvailable - 40 GiB) (JANUS_SCRIPT_MEM_MAX), so
#                              everything it starts is bounded and keeps 40 GiB for the host.
#   memguard_mechanism         cgroup | systemd-user | systemd-system | prlimit | none | off
#   memguard_limit             the default per-job limit in bytes (empty when off)
#   memguard_bytes SIZE        "16G", "1500M", "1.5GiB", bytes -> bytes
#   memguard_jobs PER_JOB [CAP]
#       floor(min(limit, MemAvailable - 40 GiB) / PER_JOB), clamped to [1, CAP or nproc].
#
# Nesting: the outer guard is a systemd scope with Delegate=yes (or a child of an already
# delegated cgroup); its command runs in a leaf "leader" cgroup and JANUS_MEMGUARD_CGROUP points
# at the guard's cgroup. A nested memguard_run, and janus itself (every lean, leanchecker, lake
# it starts), create their own limited child cgroups there instead of new systemd scopes, which
# would escape the outer limit. The effective limit of a job is the smallest on its path.
#
# Mechanisms, strongest first (JANUS_MEMGUARD=<mech> forces one): a child of the delegated
# $JANUS_MEMGUARD_CGROUP ("cgroup"); systemd-run --user --scope ("systemd-user"); systemd-run
# --scope as root ("systemd-system"); prlimit --as=LIMIT+16G per process ("prlimit": weak, Lean
# reserves ~10 GiB of address space up front); nothing ("none", with a warning).

# shellcheck disable=SC2034
_MG_SELF="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/memguard.sh"
_MG_GIB=$((1 << 30))
_MG_PRLIMIT_SLACK=$((16 << 30))
_MG_HEADROOM=$((40 << 30))

memguard_bytes() {
  local s="${1^^}" mult=1 num
  s="${s%B}"; s="${s%I}"
  case "$s" in
    *K) mult=$((1 << 10)); s="${s%K}" ;;
    *M) mult=$((1 << 20)); s="${s%M}" ;;
    *G) mult=$((1 << 30)); s="${s%G}" ;;
    *T) mult=$((1 << 40)); s="${s%T}" ;;
  esac
  case "$s" in ''|*[!0-9.]*|*.*.*) echo "memguard: '$1' is not a size like 16G or 1500M" >&2; return 1 ;; esac
  num=$(awk -v n="$s" -v m="$mult" 'BEGIN { printf "%.0f", n * m }')
  echo "$num"
}

_mg_meminfo() { awk -v k="$1:" '$1 == k { print $2 * 1024 }' /proc/meminfo 2>/dev/null; }

_mg_fmt() {
  awk -v n="${1:-0}" 'BEGIN { if (n >= 1073741824) printf "%.1f GiB", n / 1073741824; else printf "%.0f MiB", n / 1048576 }'
}

memguard_limit() {
  local v="${JANUS_MEM_MAX:-}" t
  if [ -n "$v" ]; then
    case "${v,,}" in off) return 0 ;; esac
    memguard_bytes "$v"
    return
  fi
  t=$(_mg_meminfo MemTotal)
  if [ -n "$t" ] && [ $((t * 2 / 5)) -lt $((24 * _MG_GIB)) ]; then echo $((t * 2 / 5)); else echo $((24 * _MG_GIB)); fi
}

_mg_own_cgroup() { local p; p=$(sed -n 's/^0:://p' /proc/self/cgroup 2>/dev/null); [ -n "$p" ] && echo "/sys/fs/cgroup$p"; }

# _mg_cgroup_ok PARENT: a child of PARENT can get a memory.max.
_mg_cgroup_ok() {
  local d="$1/mg-probe-$$-$RANDOM" ok=1
  [ -e "$1/cgroup.subtree_control" ] || return 1
  mkdir "$d" 2>/dev/null || return 1
  if [ -w "$d/memory.max" ] && [ -w "$d/cgroup.procs" ]; then ok=0; fi
  rmdir "$d" 2>/dev/null
  return $ok
}

_mg_systemd_ok() {
  local out
  command -v systemd-run >/dev/null 2>&1 || return 1
  [ "$1" = --user ] || [ "$(id -u)" = 0 ] || return 1
  if [ "$1" = --user ] && [ -z "${XDG_RUNTIME_DIR:-}" ] && [ -S "/run/user/$(id -u)/bus" ]; then
    XDG_RUNTIME_DIR="/run/user/$(id -u)"
    export XDG_RUNTIME_DIR
  fi
  # shellcheck disable=SC2086,SC2016
  out=$(timeout 20 systemd-run $1 --scope --quiet --collect -p MemoryMax=$((1 << 30)) -p MemorySwapMax=0 -- \
          sh -c 'cat "/sys/fs/cgroup$(sed -n "s/^0:://p" /proc/self/cgroup)/memory.max"' 2>/dev/null) || return 1
  [ "$out" = $((1 << 30)) ]
}

memguard_mechanism() { _mg_detect; echo "$_MG_MECH"; }

# _mg_detect sets _MG_MECH (and _MG_PARENT for "cgroup") once; call it outside $(…).
_mg_detect() {
  [ -n "${_MG_MECH:-}" ] && return 0
  local force="${JANUS_MEMGUARD:-}" own
  _MG_MECH=none
  _MG_PARENT=""
  case "${JANUS_MEM_MAX:-}" in [Oo][Ff][Ff]) _MG_MECH=off; return 0 ;; esac
  own=$(_mg_own_cgroup)
  if { [ -z "$force" ] || [ "$force" = cgroup ]; } && [ -n "${JANUS_MEMGUARD_CGROUP:-}" ] && _mg_cgroup_ok "$JANUS_MEMGUARD_CGROUP"; then
    _MG_MECH=cgroup; _MG_PARENT="$JANUS_MEMGUARD_CGROUP"
  elif { [ -z "$force" ] || [ "$force" = cgroup ]; } && [ -n "$own" ] && _mg_cgroup_ok "$own"; then
    _MG_MECH=cgroup; _MG_PARENT="$own"
  elif { [ -z "$force" ] || [ "$force" = systemd-user ]; } && _mg_systemd_ok --user; then
    _MG_MECH=systemd-user
  elif { [ -z "$force" ] || [ "$force" = systemd-system ]; } && _mg_systemd_ok ""; then
    _MG_MECH=systemd-system
  elif { [ -z "$force" ] || [ "$force" = prlimit ]; } && command -v prlimit >/dev/null 2>&1; then
    _MG_MECH=prlimit
  fi
  return 0
}

memguard_jobs() {
  local per cap lim avail n
  per=$(memguard_bytes "${1:?memguard_jobs PER_JOB [CAP]}") || return 1
  cap="${2:-$(nproc 2>/dev/null || echo 4)}"
  lim=$(memguard_limit)
  avail=$(( $(_mg_meminfo MemAvailable) - _MG_HEADROOM ))
  if [ -z "$lim" ] || [ "$avail" -lt "$lim" ]; then lim=$avail; fi
  n=$(( lim / per ))
  [ "$n" -gt "$cap" ] && n=$cap
  [ "$n" -lt 1 ] && n=1
  echo "$n"
}

_mg_log_once() {
  [ -n "${_MG_LOGGED:-}" ] && return
  _MG_LOGGED=1
  _mg_detect
  local m="$_MG_MECH"
  case "$m" in
    off) echo "memguard: off (JANUS_MEM_MAX=off): no memory limit" >&2 ;;
    none) echo "memguard: WARNING: no mechanism available (no delegated cgroup, systemd-run or prlimit); commands run without a memory limit" >&2 ;;
    prlimit) echo "memguard: prlimit (weaker: per-process virtual-memory limit = limit + 16 GiB)" >&2 ;;
    *) echo "memguard: $m${_MG_PARENT:+ under $_MG_PARENT}, default limit $(_mg_fmt "$(memguard_limit)") per job, no swap" >&2 ;;
  esac
}

# _mg_report LABEL PEAK LIMIT KILLED MECH
_mg_report() {
  local msg
  msg="memguard[$1]: peak $(_mg_fmt "$2") / limit $(_mg_fmt "$3") ($5)"
  [ "$4" = 1 ] && msg="$msg OOM-KILLED: the command exceeded its memory limit"
  [ "$4" = 2 ] && msg="$msg (a nested guard killed one of its jobs)"
  echo "$msg" >&2
}

# _mg_killed CG: CG's own limit was hit and something under it was OOM-killed. A kill caused by
# a nested guard's smaller limit (janus's per-job cgroups) is that guard's to report.
_mg_killed() {
  _mg_nested_kill "$1" || return 1
  [ -e "$1/memory.events.local" ] || return 0
  awk '$1 == "oom" && $2 > 0 { k = 1 } END { exit !k }' "$1/memory.events.local" 2>/dev/null
}
# _mg_nested_kill CG: something under CG (at any depth) was OOM-killed.
_mg_nested_kill() { awk '($1 == "oom_kill" || $1 == "oom_group_kill") && $2 > 0 { k = 1 } END { exit !k }' "$1/memory.events" 2>/dev/null; }

_mg_eff_limit() {
  local p="$1" lim="" v
  while [ "${p#/sys/fs/cgroup/}" != "$p" ]; do
    v=$(cat "$p/memory.max" 2>/dev/null)
    case "$v" in ''|max) ;; *) if [ -z "$lim" ] || [ "$v" -lt "$lim" ]; then lim=$v; fi ;; esac
    p=$(dirname "$p")
  done
  echo "${lim:-0}"
}

# _mg_cgroup_run MECH PARENT LIMIT LABEL CMD...: CMD in PARENT/mg-…/leader with memory.max=LIMIT
# on PARENT/mg-… (delegated to CMD through JANUS_MEMGUARD_CGROUP). No memory.oom.group: on an
# OOM the kernel kills the largest process (a lean), so a nested janus survives to report it.
_mg_cgroup_run() {
  local mech="$1" parent="$2" limit="$3" label="$4" d rc peak killed=0 lim
  shift 4
  d="$parent/mg-$$-$RANDOM$RANDOM"
  if ! { mkdir "$d" && echo "$limit" > "$d/memory.max" && { [ ! -e "$d/memory.swap.max" ] || echo 0 > "$d/memory.swap.max"; } &&
         echo +memory > "$d/cgroup.subtree_control" && mkdir "$d/leader"; } 2>/dev/null; then
    rmdir "$d/leader" "$d" 2>/dev/null
    echo "memguard[$label]: cannot set up a child cgroup of $parent" >&2
    return 125
  fi
  ( echo 0 > "$d/leader/cgroup.procs" || exit 125
    # shellcheck disable=SC2030
    export JANUS_MEMGUARD_CGROUP="$d"
    unset _MG_MECH _MG_PARENT
    exec "$@" )
  rc=$?
  peak=$(cat "$d/memory.peak" 2>/dev/null || echo 0)
  if _mg_killed "$d"; then killed=1; elif _mg_nested_kill "$d"; then killed=2; fi
  lim=$(_mg_eff_limit "$d")
  echo 1 > "$d/cgroup.kill" 2>/dev/null || true
  find "$d" -depth -type d -exec rmdir {} + 2>/dev/null
  rmdir "$d" 2>/dev/null
  _mg_report "$label" "$peak" "$lim" "$killed" "$mech"
  [ "$killed" = 1 ] && return 137
  return "$rc"
}

# Inside a systemd scope with Delegate=yes: move into scope/leader, then run under the scope.
_mg_scope_inner() {
  local limit="$1" label="$2" mech="$3" cg rc peak killed=0
  shift 3
  cg=$(_mg_own_cgroup)
  if mkdir "$cg/leader" 2>/dev/null && echo 0 > "$cg/leader/cgroup.procs" 2>/dev/null &&
     echo +memory > "$cg/cgroup.subtree_control" 2>/dev/null; then
    _mg_cgroup_run "$mech" "$cg" "$limit" "$label" "$@"
    return $?
  fi
  # No delegation: the command shares the scope with this shell; read the scope's counters.
  ( unset _MG_MECH _MG_PARENT; exec "$@" )
  rc=$?
  peak=$(cat "$cg/memory.peak" 2>/dev/null || echo 0)
  _mg_killed "$cg" && killed=1
  _mg_report "$label" "$peak" "$limit" "$killed" "$mech"
  [ "$killed" = 1 ] && return 137
  return "$rc"
}

memguard_run() {
  local limit="" label="" mech user=""
  while [ $# -gt 0 ]; do
    case "$1" in
      -l) limit="$2"; shift 2 ;;
      -n) label="$2"; shift 2 ;;
      --) shift; break ;;
      *) break ;;
    esac
  done
  [ $# -gt 0 ] || { echo "memguard_run: no command" >&2; return 2; }
  [ -n "$label" ] || label="$(basename "$1")"
  if [ -z "$limit" ]; then
    limit=$(memguard_limit) || return 2
  else
    case "${limit,,}" in off) limit="" ;; *) limit=$(memguard_bytes "$limit") || return 2 ;; esac
  fi
  _mg_log_once
  mech="$_MG_MECH"
  [ -n "$limit" ] || mech=off
  case "$mech" in
    cgroup) _mg_cgroup_run cgroup "$_MG_PARENT" "$limit" "$label" "$@" ;;
    systemd-user|systemd-system)
      [ "$mech" = systemd-user ] && user=--user
      # shellcheck disable=SC2086
      systemd-run $user --scope --quiet --collect -p Delegate=yes -p MemoryMax="$limit" -p MemorySwapMax=0 \
        -p OOMPolicy=continue -- bash "$_MG_SELF" __scope "$limit" "$label" "$mech" "$@" ;;
    prlimit) prlimit --as=$((limit + _MG_PRLIMIT_SLACK)) -- "$@" ;;
    *) "$@" ;;
  esac
}

memguard_lake() {
  if [ -n "${LEAN_NUM_THREADS:-}" ]; then
    memguard_run -n "lake $1" -- lake "$@"
  else
    memguard_run -n "lake $1" -- env LEAN_NUM_THREADS="$(memguard_jobs "${JANUS_LAKE_JOB_MEM:-3G}")" lake "$@"
  fi
}

# memguard_self "$@": re-run the calling script once inside a script-wide guard.
memguard_self() {
  # shellcheck disable=SC2031
  [ -n "${JANUS_MEMGUARD_CGROUP:-}${_MG_SELF_DONE:-}" ] && return 0
  local mech lim avail
  _mg_detect
  mech="$_MG_MECH"
  case "$mech" in cgroup|systemd-user|systemd-system) ;; *) _mg_log_once; return 0 ;; esac
  if [ -n "${JANUS_SCRIPT_MEM_MAX:-}" ]; then
    lim=$(memguard_bytes "$JANUS_SCRIPT_MEM_MAX") || exit 2
  else
    lim=$(memguard_limit)
    avail=$(( $(_mg_meminfo MemAvailable) - _MG_HEADROOM ))
    [ "$avail" -gt "$lim" ] && lim=$avail
  fi
  export _MG_SELF_DONE=1
  exec bash "$_MG_SELF" run -l "$lim" -n "$(basename "$0")" -- bash "$0" "$@"
}

# Executable entry points.
if [ "${BASH_SOURCE[0]}" = "$0" ]; then
  case "${1:-}" in
    __scope) shift; _mg_scope_inner "$@"; exit $? ;;
    run) shift; memguard_run "$@"; exit $? ;;
    mechanism) memguard_mechanism; exit 0 ;;
    *) echo "usage: memguard.sh run [-l LIMIT] [-n LABEL] -- CMD... | mechanism" >&2; exit 2 ;;
  esac
fi
