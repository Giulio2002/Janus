# Sourced by the verify-* scripts: `jv ARGS...` is `bin/janus verify ARGS...` under a wall-clock
# limit, JANUS_ITEM_TIMEOUT seconds (default 2700 = 45 min) per invocation. A run that exceeds it is
# killed (SIGTERM, then SIGKILL 30 s later; the sandboxed Lean children die with their parent) and
# fails with exit status 124; "TIMEOUT: ..." is printed on its output, which the callers keep in the
# item's log and show on failure. One hung proof therefore costs at most the limit instead of the
# whole gate. JANUS_ITEM_TIMEOUT=0 disables the limit.
jv() {
  local t=${JANUS_ITEM_TIMEOUT:-2700} rc=0
  if [ "$t" = 0 ]; then bin/janus verify "$@"; return $?; fi
  timeout -k 30 "$t" bin/janus verify "$@" || rc=$?
  if [ "$rc" = 124 ] || [ "$rc" = 137 ]; then
    echo "TIMEOUT: janus verify exceeded ${t}s (JANUS_ITEM_TIMEOUT) and was killed: $*"
    rc=124
  fi
  return $rc
}
