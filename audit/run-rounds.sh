#!/usr/bin/env bash
# Every soundness audit (audit/run-all.sh and audit/round{2..8}/run-round*.sh) as parallel lanes,
# after one shared build: janus is built once (audit/bin/janus-rounds, passed to every lane as
# JANUS_AUDIT_BIN), and the framework build of this checkout and the example binaries once, so no
# lane rebuilds them (JANUS_AUDIT_PREBUILT=1; JANUS_GATE_PREBUILT=1: scripts/gate.sh has built all of it already). The rounds are independent: each writes only its own
# audit/<round>/work and temporary caches, and they share only the read-only framework build and
# artifacts/ (built here first). Each lane's output is printed whole, in order; a lane whose script
# fails (any BROKEN row) fails the run.
#
# Usage: audit/run-rounds.sh [-j LANES] [round …]   (rounds: all r2 … rN, one per audit/round*/; default every one)
#   -j LANES   lanes at once (default min(cores/12, (MemAvailable-40G)/20G, 4), admitted by memory); each lane runs
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
# A lane holds several rows at once: two jobs' budget each (admission, default -j and cgroup
# limit), and at most 4 lanes by default (each runs -j $JANUS_LANE_JOBS rows).
PAR_JOB_MEM_KB=$((2 * PAR_JOB_MEM_KB)); PAR_MAX_DEFAULT_JOBS=4; PAR_CORES_PER_JOB=$((2 * PAR_CORES_PER_JOB))
par_init "$@"
PAR_JOB_MEM=20G
declare -A script=([all]=audit/run-all.sh [r2]=audit/round2/run-round2.sh [r3]=audit/round3/run-round3.sh
  [r4]=audit/round4/run-round4.sh [r5]=audit/round5/run-round5.sh [r6]=audit/round6/run-round6.sh
  [r7]=audit/round7/run-round7.sh [r7c]=audit/round7/run-cache.sh [r7j]=audit/round7/run-j1.sh [r8]=audit/round8/run-round8.sh)
# Every audit/roundN/run-roundN.sh is a lane, so a new round can never be skipped silently.
for f in audit/round*/run-round*.sh; do
  n="r${f#audit/round}"; n="${n%%/*}"
  [ -n "${script[$n]:-}" ] || script[$n]="$f"
done
# Longest first (measured), so the long lanes start at once; rounds without a measurement last.
lanes=(${PAR_ARGS[@]+"${PAR_ARGS[@]}"})
if [ ${#lanes[@]} -eq 0 ]; then
  lanes=(r7 r7c r7j r8 r5 all r2 r6 r3 r4)
  for n in $(printf '%s\n' "${!script[@]}" | sort -V); do
    case " ${lanes[*]} " in *" $n "*) ;; *) lanes+=("$n");; esac
  done
fi
# Round 7's result-cache rows (audit/round7/run-cache.sh) are their own lane, r7c, and its consumer row J1a
# (audit/round7/run-j1.sh) is r7j; selecting r7 selects all three, so no row is dropped (run-round7.sh alone still runs them at its end).
case " ${lanes[*]} " in *" r7 "*) for x in r7c r7j; do case " ${lanes[*]} " in *" $x "*) ;; *) lanes+=($x);; esac; done;; esac
export JANUS_R7_NO_CACHE_ROWS=1
for l in "${lanes[@]}"; do
  [ -n "${script[$l]:-}" ] || { echo "unknown round $l (all r2 r3 r4 r5 r6 r7 r8)"; exit 2; }
done

wall=$(date +%s)
mkdir -p audit/bin
if [ "${JANUS_GATE_PREBUILT:-}" = 1 ]; then
  # scripts/gate.sh built (once) audit/bin/janus-rounds, the framework, the auditor and both ISAs' example binaries
  [ -x audit/bin/janus-rounds ] || { echo "JANUS_GATE_PREBUILT=1 but audit/bin/janus-rounds is missing"; exit 1; }
else
  go build -o audit/bin/janus-rounds ./cmd/janus || exit 1
  memguard_lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed (fix the Lean library first)"; exit 1; }
  [ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null || exit 1
  { [ -f artifacts/examples-amd64 ] && [ -d artifacts/amd64/HexDigit ] && [ -d artifacts/amd64/Add ]; } ||
    bash scripts/build-examples-amd64.sh >/dev/null 2>&1 || exit 1
fi
export JANUS_AUDIT_BIN="$root/audit/bin/janus-rounds" JANUS_AUDIT_PREBUILT=1
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
