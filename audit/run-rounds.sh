#!/usr/bin/env bash
# Every soundness audit (audit/run-all.sh and audit/round{2..8}/run-round*.sh) as parallel lanes,
# after one shared build: janus is built once (audit/bin/janus-rounds, passed to every lane as
# JANUS_AUDIT_BIN), and the framework build of this checkout and the example binaries once, so no
# lane rebuilds them (JANUS_AUDIT_PREBUILT=1). The rounds are independent: each writes only its own
# audit/<round>/work and temporary caches, and they share only the read-only framework build and
# artifacts/ (built here first). Each lane's output is printed whole, in order; a lane whose script
# fails (any BROKEN row) fails the run.
#
# Usage: audit/run-rounds.sh [-j LANES] [round …]   (rounds: all r2 r3 r4 r5 r6 r7 r8; default every one)
#   -j LANES   lanes at once (default: scripts/lib/parallel.sh, admitted by memory); each lane runs
#              its own rows with -j $JANUS_LANE_JOBS (default 2).
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=../scripts/lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
# shellcheck source=../scripts/lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
par_init "$@"
# A lane holds several rows at once: give it two jobs' budget (admission and cgroup limit).
PAR_JOB_MEM_KB=$((2 * PAR_JOB_MEM_KB)); PAR_JOB_MEM=20G
declare -A script=([all]=audit/run-all.sh [r2]=audit/round2/run-round2.sh [r3]=audit/round3/run-round3.sh
  [r4]=audit/round4/run-round4.sh [r5]=audit/round5/run-round5.sh [r6]=audit/round6/run-round6.sh
  [r7]=audit/round7/run-round7.sh [r8]=audit/round8/run-round8.sh)
# Longest first (measured), so the long lanes start at once.
lanes=(${PAR_ARGS[@]+"${PAR_ARGS[@]}"})
[ ${#lanes[@]} -gt 0 ] || lanes=(all r5 r6 r2 r7 r8 r3 r4)
for l in "${lanes[@]}"; do
  [ -n "${script[$l]:-}" ] || { echo "unknown round $l (all r2 r3 r4 r5 r6 r7 r8)"; exit 2; }
done

wall=$(date +%s)
mkdir -p audit/bin
go build -o audit/bin/janus-rounds ./cmd/janus || exit 1
memguard_lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed (fix the Lean library first)"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null || exit 1
{ [ -f artifacts/examples-amd64 ] && [ -d artifacts/amd64/HexDigit ] && [ -d artifacts/amd64/Add ]; } ||
  bash scripts/build-examples-amd64.sh >/dev/null 2>&1 || exit 1
export JANUS_AUDIT_BIN="$root/audit/bin/janus-rounds" JANUS_AUDIT_PREBUILT=1
export JANUS_JOBS="${JANUS_LANE_JOBS:-2}"
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
