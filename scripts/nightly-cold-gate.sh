#!/usr/bin/env bash
# The nightly cold gate (docs/TESTING.md "Build cache policy"): run scripts/gate.sh on one commit with the
# ASL/Sail build caches OFF (JANUS_ASL_CACHE=0, a fresh worktree with no builds), and compare its lane results
# and its ASL/Sail artifact hashes with a cached run of the same commit. Any disagreement is a P0 cache bug
# (a key that misses an input, or a cache that served something its inputs do not determine): exit 1.
#
#   scripts/nightly-cold-gate.sh [--commit REV] [--cached-out DIR] [--work DIR] [--keep] [-- GATE ARGS...]
#
#   --commit REV     the commit to check (default HEAD of this checkout)
#   --cached-out DIR use the gate output DIR of an earlier cached run of the same commit (it must contain
#                    timeline.jsonl and artifact-hashes.json: run `gate-cachecmp.py hashes` after that run);
#                    without it the cached run is made here too, in its own fresh worktree
#   --work DIR       scratch (default: mktemp -d /srv/janus-ops/work.XXXX); worktrees and logs go there
#   --keep           keep the scratch directory (default: remove it when the runs agree)
#   -- ...           the rest goes to scripts/gate.sh (both runs), e.g. -j 2
# THE ONLY WRITER OF THE MODEL PIN (docs/TESTING.md "Cold gate and the model pin"): when the cold gate (which builds the
# ArmASL model and the Sail driver from source: JANUS_ASL_CACHE=0, a fresh worktree) PASSED and agrees with the cached run, the
# cold run's model artifacts are pinned (scripts/model-pin.sh write: atomic, under a lock). `gate.sh --cold` restores them with full
# integrity validation instead of rebuilding ~1 h of ArmASL + ~25 min of Sail. A pin that already exists for the same inputs must
# be reproduced byte for byte in every .olean/.ilean and the driver, else this run exits 1 ("NOT REPRODUCED") and keeps the old pin.
# Both runs get the SAME explicit SAIL_SPLIT (the caller's value, default 1; recorded in artifact-hashes.json): a
# cached/cold pair built with different SAIL_SPLIT settings is reported by gate-cachecmp.py as a CONFIGURATION
# MISMATCH (exit 2), never as a cache verdict. A --cached-out run must have been made with the same SAIL_SPLIT.
# Both runs use `memcap -m 80G` and scripts/gate.sh's own load/memory/disk refusal. Nothing is installed:
# an example crontab line is in docs/TESTING.md.
# Exit: 0 agree (and the pin written or reproduced); 1 P0 disagreement or the pin was not reproduced; 2 could not compare, the cold
# gate failed, or a run could not start.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
commit="" cached="" work="" keep=0
while [ $# -gt 0 ]; do
  case "$1" in
    --commit) commit="$2"; shift 2 ;;
    --cached-out) cached="$2"; shift 2 ;;
    --work) work="$2"; shift 2 ;;
    --keep) keep=1; shift ;;
    --) shift; break ;;
    *) echo "nightly-cold-gate: unknown argument $1" >&2; exit 2 ;;
  esac
done
gate_args=("$@")
sail_split="${SAIL_SPLIT:-1}"
commit=$(git -C "$root" rev-parse --verify "${commit:-HEAD}^{commit}") || { echo "nightly-cold-gate: bad commit" >&2; exit 2; }
[ -n "$work" ] || work=$(mktemp -d /srv/janus-ops/work.XXXX)
mkdir -p "$work"
cmp_py="$root/scripts/gate-cachecmp.py"
trees=()
cleanup() {
  local t
  for t in "${trees[@]}"; do git -C "$root" worktree remove --force "$t" >/dev/null 2>&1 || true; done
  [ "$keep" = 1 ] || [ "${rc_final:-2}" != 0 ] || rm -rf "$work"
}
trap cleanup EXIT

run_gate() { # NAME CACHE_ENV...: a fresh worktree of the commit, gate.sh, then the artifact hashes
  local name=$1; shift
  local t="$work/tree-$name" out="$work/out-$name"
  git -C "$root" worktree add --detach -f "$t" "$commit" >/dev/null || { echo "nightly-cold-gate: cannot create $t" >&2; return 2; }
  trees+=("$t")
  local rc=0
  (cd "$t" && env -u JANUS_MODEL_PIN -u JANUS_MODEL_PIN_STALE -u JANUS_COLD -u JANUS_COLD_DONE -u JANUS_COLD_PIN_CHECKED "$@" SAIL_SPLIT="$sail_split" memcap -m 80G scripts/gate.sh --out "$out" --speed-baseline enforce "${gate_args[@]}") > "$work/$name.log" 2>&1 || rc=$?
  echo "nightly-cold-gate: $name gate rc=$rc (log $work/$name.log)"
  eval "gate_rc_$name=$rc"
  SAIL_SPLIT="$sail_split" python3 -I "$cmp_py" hashes "$t" "$out/artifact-hashes.json" || return 2
  return 0
}

if [ -z "$cached" ]; then
  run_gate cached -u JANUS_ASL_CACHE || exit 2
  cached="$work/out-cached"
fi
run_gate cold JANUS_ASL_CACHE=0 || exit 2
python3 -I "$cmp_py" compare "$cached" "$work/out-cold"
rc_final=$?
if [ "$rc_final" = 0 ] && [ "${gate_rc_cold:-1}" != 0 ]; then
  echo "nightly-cold-gate: the cold gate FAILED (rc ${gate_rc_cold:-?}) and so did the cached one: the runs agree but nothing is proven; the model pin is NOT written"
  rc_final=2
fi
if [ "$rc_final" = 0 ]; then
  # the cold tree still holds the model built from source: pin it (or confirm the existing pin byte for byte)
  (cd "$work/tree-cold" && JANUS_PIN_WRITER=nightly-cold-gate memcap -m 24G scripts/model-pin.sh write --commit "$commit" --evidence "$work/out-cold/artifact-hashes.json")
  rc_final=$?
  [ "$rc_final" = 0 ] || echo "nightly-cold-gate: the model pin was NOT written/confirmed (rc $rc_final)"
fi
[ "$rc_final" = 0 ] || echo "nightly-cold-gate: runs kept in $work"
exit $rc_final
