#!/usr/bin/env bash
# Every soundness audit (test/redteam/run-all.sh and test/redteam/rounds/round{2..8}/run-round*.sh) as parallel lanes,
# after one shared build: janus is built once (test/redteam/bin/janus-rounds, passed to every lane as
# JANUS_AUDIT_BIN), and the framework build of this checkout and the example binaries once, so no
# lane rebuilds them (JANUS_AUDIT_PREBUILT=1; JANUS_GATE_PREBUILT=1: scripts/gate.sh has built all of it already). The rounds are independent: each writes only its own
# test/redteam/<round>/work and temporary caches, and they share only the read-only framework build and
# artifacts/ (built here first). Each lane's output is printed whole, in order; a lane whose script
# fails (any BROKEN row) fails the run.
#
# Usage: test/redteam/run-rounds.sh [-j LANES] [round …]   (rounds: all r2 … rN, one per test/redteam/rounds/round*/; default every one)
#   -j LANES   lanes at once (default min(cores/12, (MemAvailable-40G)/20G, 4), admitted by memory); each lane runs
#              its own rows with -j $JANUS_LANE_JOBS (default 2).
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=../../scripts/lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
# shellcheck source=../../scripts/lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
# A lane holds several rows at once: two jobs' budget each (admission, default -j and cgroup
# limit), and at most 4 lanes by default (each runs -j $JANUS_LANE_JOBS rows).
PAR_JOB_MEM_KB=$((2 * PAR_JOB_MEM_KB)); PAR_MAX_DEFAULT_JOBS=4; PAR_CORES_PER_JOB=$((2 * PAR_CORES_PER_JOB))
par_init "$@"
PAR_JOB_MEM=20G
declare -A script=([all]=test/redteam/run-all.sh [alla]=test/redteam/run-all-a.sh [allb]=test/redteam/run-all-b.sh [allc]=test/redteam/run-all-c.sh [r2]=test/redteam/rounds/round2/run-round2.sh [r3]=test/redteam/rounds/round3/run-round3.sh
  [r4]=test/redteam/rounds/round4/run-round4.sh [r5]=test/redteam/rounds/round5/run-round5.sh [r6]=test/redteam/rounds/round6/run-round6.sh
  [r7]=test/redteam/rounds/round7/run-round7.sh [r7c]=test/redteam/rounds/round7/run-cache.sh [r7c1]=test/redteam/rounds/round7/run-cache-1.sh [r7c2]=test/redteam/rounds/round7/run-cache-2.sh [r7c3]=test/redteam/rounds/round7/run-cache-3.sh [r7j]=test/redteam/rounds/round7/run-j1.sh [r8]=test/redteam/rounds/round8/run-round8.sh
  [r8a]=test/redteam/rounds/round8/run-rows-a.sh [r8b]=test/redteam/rounds/round8/run-rows-b.sh [r8c]=test/redteam/rounds/round8/run-rows-c.sh)
# Every test/redteam/rounds/roundN/run-roundN.sh is a lane, so a new round can never be skipped silently.
for f in test/redteam/rounds/round*/run-round*.sh; do
  n="r${f#test/redteam/rounds/round}"; n="${n%%/*}"
  [ -n "${script[$n]:-}" ] || script[$n]="$f"
done
# Longest first (measured), so the long lanes start at once; rounds without a measurement last.
lanes=(${PAR_ARGS[@]+"${PAR_ARGS[@]}"})
if [ ${#lanes[@]} -eq 0 ]; then
  lanes=(r7 r7c1 r7c2 r7c3 r7j r8a r8b r8c r5 alla allb allc r2 r6 r3 r4)
  for n in $(printf '%s\n' "${!script[@]}" | sort -V); do
    [ "$n" != r7c ] && [ "$n" != r8 ] && [ "$n" != all ] || continue   # r7c, r8, all = their parts (r7c1..3, r8a..c, alla..c) in one lane: only on request
    case " ${lanes[*]} " in *" $n "*) ;; *) lanes+=("$n");; esac
  done
fi
# Round 7's result-cache rows (test/redteam/rounds/round7/run-cache.sh) are three lanes, r7c1..r7c3 (run-cache-{1,2,3}.sh: the longest lane of the rounds, 1703 s in one piece; r7c still selects all rows in one lane), and its consumer row J1a
# (test/redteam/rounds/round7/run-j1.sh) is r7j; selecting r7 selects all three, so no row is dropped (run-round7.sh alone still runs them at its end).
case " ${lanes[*]} " in *" r7 "*) for x in r7c1 r7c2 r7c3 r7j; do case " ${lanes[*]} " in *" $x "*) ;; *) lanes+=($x);; esac; done;; esac
export JANUS_R7_NO_CACHE_ROWS=1
for l in "${lanes[@]}"; do
  [ -n "${script[$l]:-}" ] || { echo "unknown round $l (all r2 r3 r4 r5 r6 r7 r8)"; exit 2; }
done

wall=$(date +%s)
mkdir -p test/redteam/bin
if [ "${JANUS_GATE_PREBUILT:-}" = 1 ]; then
  # scripts/gate.sh built (once) test/redteam/bin/janus-rounds, the framework, the auditor and both ISAs' example binaries
  [ -x test/redteam/bin/janus-rounds ] || { echo "JANUS_GATE_PREBUILT=1 but test/redteam/bin/janus-rounds is missing"; exit 1; }
else
  CGO_ENABLED=0 go build -o test/redteam/bin/janus-rounds ./cmd/janus || exit 1
  # Every target any round needs, built once: rounds run with JANUS_AUDIT_PREBUILT=1 and never build (a concurrent lake build rewrites
  # .lake/build/lib/lean under the other lanes). r10: janus-oracle-amd64 and janus-decode (kept apart from .lake/build, which janus
  # runs may prune of extra module outputs).
  memguard_lake build Janus Janus.Tools.Audit janus-audit janus-oracle-amd64 janus-decode >/dev/null || { echo "lake build failed (fix the Lean library first)"; exit 1; }
  cp -f .lake/build/bin/janus-decode test/redteam/bin/janus-decode-prebuilt.new && mv -f test/redteam/bin/janus-decode-prebuilt.new test/redteam/bin/janus-decode-prebuilt || exit 1
  [ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null || exit 1
  { [ -f artifacts/examples-amd64 ] && [ -d artifacts/amd64/HexDigit ] && [ -d artifacts/amd64/Add ]; } ||
    bash scripts/build-examples-amd64.sh >/dev/null 2>&1 || exit 1
fi
export JANUS_AUDIT_BIN="$root/test/redteam/bin/janus-rounds" JANUS_AUDIT_PREBUILT=1
export JANUS_JOBS="${JANUS_LANE_JOBS:-2}"
# The rows run with --fresh and each in a private cache, so each used to replay the whole framework
# (`leanchecker Janus`, minutes under load). One gate-private verdict store (mode 0700, its own key,
# hidden from the sandbox) lets them share that replay: its entries are named by the toolchain and
# the SHA-256 of every framework module-data file, so a framework build that differs in any module
# (the tampered ones the rows test) is replayed; `--fresh-framework` ignores the store.
if [ -z "${JANUS_VERDICT_CACHE:-}" ]; then
  verdicts="$(mktemp -d "${TMPDIR:-/tmp}/janus-verdicts.XXXXXX")" || exit 1
  trap 'rm -rf "$verdicts"' EXIT
  export JANUS_VERDICT_CACHE="$verdicts/store"
fi
echo "audit lanes: ${lanes[*]} (-j $PAR_JOBS lanes, -j $JANUS_JOBS rows each); built in $(( $(date +%s) - wall ))s"

broken=()
for l in "${lanes[@]}"; do
  par_run 's=$(date +%s); echo "==================== $l: ${script[$l]}"
  "${script[$l]}" || broken+=("$l")
  echo "==================== $l: $(( $(date +%s) - s ))s"'
done
par_wait
echo "audit lanes: $(( $(date +%s) - wall ))s wall"
if [ ${#broken[@]} -gt 0 ]; then echo "BROKEN lanes: ${broken[*]}"; exit 1; fi
echo "All audit lanes as expected (no BROKEN row)."
