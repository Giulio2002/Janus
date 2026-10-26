# Sourced by scripts/verify-examples.sh and scripts/verify-amd64-examples.sh: verify several
# theorems of one proof file against one extraction, up to $JANUS_THEOREM_JOBS (default 2) at once.
#
#   verify_theorems OUTDIR PROOF STATUSDIR THEOREM... [-- JANUS-VERIFY-ARGS...]
#
# Each theorem is a complete, independent `janus verify` (its own proof compile, audit and kernel
# replay; nothing is shared between them that a sequential run would not share through the
# caches). The first theorem runs in OUTDIR (its verified.json stays there); every further one
# runs in a sibling copy of OUTDIR (same parent, so identity.json's relative binary path is the
# same) with a unique mktemp name, removed afterwards, because one verified.json per directory is
# written by each run. The whole set holds an exclusive lock next to OUTDIR (.<name>.theorems.lock):
# a second run on the same extraction in the same tree (two suites in one worktree) fails at once
# with a message instead of racing the first one's copies.
# STATUSDIR/<i>.log and STATUSDIR/<i>.rc hold the output and exit status of theorem i (0-based).
# The extra theorems of an example (the non-vacuity witnesses, F64ToU64's `exact`, ...) used to
# run one after the other, each compiling the same proof again: Classify's three took 3 x 170 s.
verify_theorems() {
  local out=$1 proof=$2 st=$3 i=0 thm dir
  shift 3
  local -a thms=() args=()
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
  for thm in "${thms[@]}"; do
    dir=$out
    if [ $i -gt 0 ]; then
      dir="$(mktemp -d "$(dirname "$out")/.thm-$(basename "$out")-$i.XXXXXX")"
      cp -r "$out"/. "$dir"/; rm -f "$dir/verified.json"
    fi
    ( rc=0
      bin/janus verify "$dir" --proof "$proof" --theorem "$thm" ${args[@]+"${args[@]}"} > "$st/$i.log" 2>&1 || rc=$?
      echo "$rc" > "$st/$i.rc"
      [ "$dir" = "$out" ] || rm -rf "$dir" ) &
    i=$((i + 1))
    while [ "$(jobs -rp | wc -l)" -ge "${JANUS_THEOREM_JOBS:-2}" ]; do wait -n || true; done
  done
  wait || true
  exec {lkfd}>&-
}
