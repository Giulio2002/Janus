# Sourced by scripts/verify-examples.sh and scripts/verify-amd64-examples.sh: verify several
# theorems of one proof file against one extraction in ONE `janus verify` run.
#
#   verify_theorems OUTDIR PROOF STATUSDIR THEOREM... [-- JANUS-VERIFY-ARGS...]
#
# The proof file is compiled once (and the extraction check, the trusted compile, the framework
# pins and the framework replay verdict are done once); every theorem then gets its own, complete
# checks inside that run: its own audit (statement, kind, axiom allow-list), its own result-cache
# entry and report (OUTDIR/verified/<Theorem>.json; the first theorem's is also OUTDIR/verified.json),
# and the kernel replay of its import closure (see docs/TESTING.md, "One compile per proof file").
# A failing theorem fails alone: each theorem's status is read from the results file janus itself
# writes (--results), never from the log text. A timeout or a crash of the run (no results file)
# fails every theorem of it.
# STATUSDIR/<i>.log and STATUSDIR/<i>.rc hold the output and exit status of theorem i (0-based);
# STATUSDIR/all.log is the whole run's output, STATUSDIR/results.json janus's per-theorem results.
# The whole set holds an exclusive lock next to OUTDIR (.<name>.theorems.lock): a second run on the
# same extraction in the same tree (two suites in one worktree) fails at once with a message
# instead of racing the first one's reports.
. "$(dirname "${BASH_SOURCE[0]}")/itemtimeout.sh"

verify_theorems() {
  local out=$1 proof=$2 st=$3 i=0 thm
  shift 3
  local -a thms=() args=() targs=()
  while [ $# -gt 0 ] && [ "$1" != -- ]; do thms+=("$1"); shift; done
  [ "${1:-}" = -- ] && { shift; args=("$@"); }
  local lock lkfd
  lock="$(dirname "$out")/.$(basename "$out").theorems.lock"
  exec {lkfd}>>"$lock"
  if ! flock -n "$lkfd"; then
    exec {lkfd}>&-
    for ((i = 0; i < ${#thms[@]}; i++)); do
      echo "verify_theorems: $out is being verified by another run in this tree (lock $lock held); refusing to race it" > "$st/$i.log"
      echo 75 > "$st/$i.rc"
    done
    echo "verify_theorems: $out is in use by another run in this tree ($lock); not verified" >&2
    return 1
  fi
  for thm in "${thms[@]}"; do targs+=(--theorem "$thm"); done
  rm -f "$st/results.json"
  local rc=0
  jv "$out" --proof "$proof" "${targs[@]}" --results "$st/results.json" ${args[@]+"${args[@]}"} > "$st/all.log" 2>&1 || rc=$?
  [ "$rc" != 124 ] || echo "TIMEOUT: $out ${thms[*]}" >&2
  exec {lkfd}>&-
  local trc
  for ((i = 0; i < ${#thms[@]}; i++)); do
    thm=${thms[$i]}
    trc=$rc; [ "$trc" != 0 ] || trc=1   # no verdict for this theorem unless the results file gives one
    if [ -s "$st/results.json" ] && command -v jq >/dev/null &&
       jq -e --arg t "$thm" '.schema == 1 and ([.results[] | select(.theorem == $t and .status == "verified")] | length) == 1' \
         "$st/results.json" >/dev/null 2>&1; then
      trc=0
    fi
    # this theorem's block of the output (introduced by "=== NAME: ..."); a failure also shows the
    # lines before the first block (the run's own messages, a timeout notice)
    {
      [ "$trc" = 0 ] || awk 'index($0, "=== ") == 1 { exit } { print }' "$st/all.log"
      awk -v m="=== $thm: " 'index($0, "=== ") == 1 { on = (index($0, m) == 1) } on' "$st/all.log"
    } > "$st/$i.log"
    [ "$trc" = 0 ] || { [ -s "$st/$i.log" ] || cat "$st/all.log" > "$st/$i.log"; }
    echo "$trc" > "$st/$i.rc"
  done
}
