# shellcheck shell=bash
# gotest_row NAME CMD...: run a Go-test row of an audit round with its output kept in a log (never /dev/null), so a failure can be
# diagnosed: test/redteam/work-logs/NAME.log (JANUS_AUDIT_LOGDIR overrides the directory). Returns the command's status; on failure the tail
# of the log is printed, with its path. (Rows used to send the output to /dev/null: the gate of 10104e01 had two BROKEN rows, R1 of
# round 15a and R2 of round 15c, whose cause could not be read afterwards.)
gotest_row() {
  local name=$1 rc=0 dir log
  shift
  dir="${JANUS_AUDIT_LOGDIR:-${root:-.}/test/redteam/work-logs}"
  mkdir -p "$dir"; log="$dir/$name.log"
  "$@" > "$log" 2>&1 || rc=$?
  if [ "$rc" != 0 ]; then
    echo "  >>> $name failed (exit $rc); log: $log; last lines:"
    tail -n 25 "$log" | sed 's/^/      | /'
  fi
  return "$rc"
}
