#!/usr/bin/env bash
# The merge check: the checks an integration branch must pass before it is merged (lake build incl. JanusTests and
# the auditor, the axiom guard and address lint, go vet/build, `go test ./cmd/...`, every audit round, and the
# example sweep with cgo), run as ONE scripts/gate.sh with its dependency graph instead of one phase after the
# other. Nothing is dropped or weakened: these are the lanes `verify`, `gotest`, `rounds`, `axiom`, `govet` of the
# gate, with their own checks, timeouts and verdict. It is a PARTIAL gate (the ISA-model lanes x86, asl-*, rtasl-*,
# sail and the decoder lane are left out, as the sequential merge-check scripts left them out): it does not replace
# the full gate before a push to main.
#
#   scripts/check-merge.sh [-j N] [--lanes N] [any other scripts/gate.sh option]
#
#   -j N       items at once in the example pool and the gate's own pool (default $JANUS_JOBS, else 4); the
#              go test shards and the audit lanes scale with it (docs/TESTING.md "The gate driver")
#   --lanes N  lanes at once (default N + 3: the pool and N+2 others)
#
# Why not the sequential version (lake build; go test; audit rounds; examples, one after the other): the four
# big phases are independent once the framework is built, and the gate starts each as soon as ITS inputs exist
# (docs/TESTING.md "Dependency-driven prebuild"); the go tests are sharded by measured duration (6 shards instead of
# one process with -parallel 2) and the example sweep is one longest-first queue. Run under `memcap` and, on the
# shared box, `heavy-run` (RULES.md); the gate refuses to start on a loaded host unless JANUS_GATE_FORCE=1.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
jobs_n="${JANUS_JOBS:-4}"
lanes_n=""
args=()
while [ $# -gt 0 ]; do
  case "$1" in
    -j|--jobs) jobs_n="${2:?}"; shift 2 ;;
    --lanes) lanes_n="${2:?}"; shift 2 ;;
    *) args+=("$1"); shift ;;
  esac
done
[ -n "$lanes_n" ] || lanes_n=$((jobs_n + 3))
exec scripts/gate.sh -j "$jobs_n" --lanes "$lanes_n" --only verify,gotest,rounds,axiom,govet "${args[@]}"
