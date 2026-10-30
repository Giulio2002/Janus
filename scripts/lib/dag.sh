# shellcheck shell=bash
# The gate's dependency graph (scripts/gate.sh): prebuild stages and lanes are items of ONE pool (scripts/lib/pool.sh,
# `needs`), and each starts as soon as ITS inputs are ready, not after the whole prebuild. A stage that fails blocks only
# its dependents (reported BLOCKED, a gate failure); independent stages keep running.
#
#   DAG_DEPS[NAME]   the stages NAME waits for
#   dag_closure NAMES...   NAMES and everything they (transitively) need, one per line (a run with --only builds only that)
#   dag_check              fails if a dependency is unknown or the graph has a cycle
#
# Stages (pre-*: the prebuild; tree-*: private copies of the finished framework build for the lake lanes; the rest: lanes):
#   pre-gobin      go build bin/janus                         pre-lake    lake build (the shared framework build: the ONLY writer)
#   pre-ex-*       the example binaries (ex-amd64 also rebuilds bin/janus: after pre-gobin)
#   pre-rounds-bin audit/bin/janus-rounds (after pre-gobin)   pre-warm    one verification of Add (framework build + replay verdict)
#   pre-fixture    the go tests' framework fixture (seeded by pre-warm's cache)
#   pre-pin        hash the finished framework build and switch the lakeguard on: every READER of the shared build needs it,
#                  so none starts before the build it reads has finished and been hashed
# Readers: verify, gotest, rounds, decoder (and the tree copies, which copy the build). Lanes that need nothing built:
# axiom, govet, cachekeys.
declare -gA DAG_DEPS
_EX="pre-ex-arm64 pre-ex-amd64 pre-ex-asm pre-ex-sys pre-ex-rtmisc pre-ex-print pre-ex-cgo"
DAG_DEPS=(
  [pre-gobin]="" [pre-lake]=""
  [pre-ex-arm64]="" [pre-ex-asm]="" [pre-ex-sys]="" [pre-ex-rtmisc]="" [pre-ex-print]="" [pre-ex-cgo]=""
  [pre-ex-amd64]="pre-gobin" [pre-rounds-bin]="pre-gobin"
  [pre-pin]="pre-lake"
  [pre-warm]="pre-gobin pre-lake pre-ex-arm64"
  [pre-fixture]="pre-lake pre-warm"
  [tree-x86]="pre-pin pre-gobin $_EX" [tree-asl]="pre-pin pre-gobin $_EX" [tree-aslv]="pre-pin pre-gobin $_EX" [tree-go]="pre-pin pre-gobin $_EX"
  [verify]="pre-pin pre-gobin pre-warm $_EX"
  [gotest]="pre-pin pre-gobin pre-fixture"
  [rounds]="pre-pin pre-rounds-bin pre-warm $_EX"
  [decoder]="pre-pin pre-gobin"
  [axiom]="" [govet]="" [cachekeys]=""
  [x86]="tree-x86" [oracle]="tree-asl" [asl-build]="tree-asl" [sail-build]="tree-asl" [testlane]="tree-asl"
  [asl-verify]="tree-aslv"
  [rtasl-prove]="tree-asl" [rtasl-rel]="tree-asl" [rtasl-strict]="tree-asl" [rtasl-replay]="tree-asl"
  [rtasl-btf]="tree-asl" [rtasl-probes]="tree-asl" [rtasl-fsqrt]="tree-asl"
  [rtasl-go]="tree-go pre-fixture"
)

dag_closure() {
  local -A seen=(); local -a todo=("$@"); local n d
  while [ ${#todo[@]} -gt 0 ]; do
    n=${todo[${#todo[@]}-1]}; unset 'todo[${#todo[@]}-1]'
    [ -z "${seen[$n]:-}" ] || continue
    seen[$n]=1; echo "$n"
    for d in ${DAG_DEPS[$n]:-}; do todo+=("$d"); done
  done
}

dag_check() {
  local n d bad=0
  for n in "${!DAG_DEPS[@]}"; do
    for d in ${DAG_DEPS[$n]}; do [ "${DAG_DEPS[$d]+x}" ] || { echo "dag: $n needs unknown stage $d" >&2; bad=1; }; done
  done
  # cycle: repeatedly remove stages whose deps are all removed
  local -A done_=(); local progress=1 left=${#DAG_DEPS[@]}
  while [ "$progress" = 1 ] && [ "$left" -gt 0 ]; do
    progress=0
    for n in "${!DAG_DEPS[@]}"; do
      [ -z "${done_[$n]:-}" ] || continue
      local ok=1; for d in ${DAG_DEPS[$n]}; do [ -n "${done_[$d]:-}" ] || ok=""; done
      [ -z "$ok" ] || { done_[$n]=1; left=$((left - 1)); progress=1; }
    done
  done
  [ "$left" -eq 0 ] || { echo "dag: a dependency cycle among $left stages" >&2; bad=1; }
  return $bad
}
