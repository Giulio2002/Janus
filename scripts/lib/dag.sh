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
#   pre-stamp      one verification of Add with --janus-root <checkout>: janus stamps the checkout's own framework build
#                  (and may delete and rebuild modules whose files no longer match an OLD stamp), so every write janus can make to the
#                  shared build happens BEFORE the pin; afterwards the stamp is fresh and a --janus-root verification only reads
#   (pre-warm and pre-stamp both verify artifacts/Add, whose theorems lock admits one run at a time: pre-warm waits for pre-stamp)
#   pre-fixture-emb the go tests' framework fixture, embedded part (JANUS_TEST_FIXTURE_PART=embedded): the embedded framework's
#                  build and replay verdict, built cold INSIDE the fixture directory. It reads neither this checkout's build nor the
#                  user's cache (no seed: pre-stamp and pre-warm write that cache), so it needs nothing and starts at t=0
#   pre-fixture    the fixture's checkout part (JANUS_TEST_FIXTURE_PART=checkout): the checkout's replay verdict, carried from the
#                  user's cache (where pre-stamp's --janus-root verification recorded it) or replayed; that verification only ever
#                  reads a fresh stamp after the hash, so it needs pre-stamp and pre-pin. It never reads the user cache's framework
#                  build, so it does not wait for pre-warm
#   pre-pin        hash the finished framework build and switch the lakeguard on: every READER of the shared build needs it,
#                  so none starts before the build it reads has finished and been hashed
# Readers: verify, gotest, rounds, decoder (and the tree copies, which copy the build). Lanes that need nothing built:
# axiom, govet, cachekeys.
declare -gA DAG_DEPS
_EX="pre-ex-arm64 pre-ex-amd64 pre-ex-asm pre-ex-sys pre-ex-rtmisc pre-ex-print pre-ex-cgo"
DAG_DEPS=(
  [pre-gobin]="" [pre-lake]=""
  [pre-ex-arm64]="" [pre-ex-asm]="" [pre-ex-sys]="" [pre-ex-rtmisc]="" [pre-ex-print]="" [pre-ex-cgo]=""
  [pre-ex-amd64]="pre-gobin" [pre-rounds-bin]="pre-gobin pre-ex-amd64"
  [pre-stamp]="pre-gobin pre-lake pre-ex-arm64 pre-ex-amd64"
  [pre-pin]="pre-lake pre-stamp"
  [pre-warm]="pre-gobin pre-lake pre-ex-arm64 pre-stamp"
  [pre-fixture-emb]=""
  [pre-fixture]="pre-lake pre-stamp pre-pin pre-fixture-emb"
  [tree-x86]="pre-pin pre-gobin $_EX" [tree-asl]="pre-pin pre-gobin $_EX" [tree-aslv]="pre-pin pre-gobin $_EX" [tree-go]="pre-pin pre-gobin $_EX"
  [verify]="pre-pin pre-gobin pre-warm $_EX"
  [gotest]="pre-pin pre-gobin pre-fixture"
  [rounds]="pre-pin pre-rounds-bin pre-warm $_EX"
  [decoder]="pre-pin pre-gobin pre-ex-amd64"
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

# Resources the stages touch, and how (w = writes or replaces it, r = reads/executes it). Two stages that touch the same
# resource, at least one of them as a writer, must be ORDERED (one in the other's closure): that is what the structure
# alone does not show (pre-stamp and pre-warm both verify artifacts/Add and collided on its theorems lock; pre-ex-amd64
# replaces bin/janus while others run it). scripts/lib/test-dag.sh asserts it for every pair.
declare -gA DAG_RES
DAG_RES=(
  [artifact:Add]="w:pre-stamp w:pre-warm w:verify"
  [bin/janus]="w:pre-gobin w:pre-ex-amd64 r:pre-stamp r:pre-warm r:pre-rounds-bin r:verify r:rounds r:decoder r:tree-x86 r:tree-asl r:tree-aslv r:tree-go"
  [framework-build]="w:pre-lake w:pre-stamp r:pre-pin r:pre-warm r:pre-fixture r:verify r:gotest r:rounds r:decoder r:tree-x86 r:tree-asl r:tree-aslv r:tree-go"
  [audit/bin/janus-rounds]="w:pre-rounds-bin r:rounds"
  [go-test-fixture]="w:pre-fixture-emb w:pre-fixture r:gotest r:rtasl-go"
  [examples-arm64]="w:pre-ex-arm64 r:pre-stamp r:pre-warm r:verify r:rounds r:tree-x86 r:tree-asl r:tree-aslv r:tree-go"
  [examples-amd64]="w:pre-ex-amd64 r:verify r:rounds r:tree-x86 r:tree-asl r:tree-aslv r:tree-go"
  [user-cache-framework]="w:pre-stamp w:pre-warm"
  [user-cache-checkout-verdict]="w:pre-stamp r:pre-fixture"
)

# dag_has STAGE DEP: DEP is in STAGE's closure. NOT `dag_closure STAGE | grep -qx DEP`: grep -q leaves at the first match, the
# producer is then killed by SIGPIPE while it still writes (a loaded host makes that likely), and under `set -o pipefail` the
# pipeline reports failure for a stage that DOES depend on DEP: a stage seemed unordered/missing (flaky test-dag.sh, seen
# in two gate runs). The closure is captured first, the match runs on a here-string.
dag_has() { local c; c="$(dag_closure "$1")"; grep -qx -- "$2" <<<"$c"; }

# dag_unordered: print every pair of stages that share a resource (one at least writing) with no dependency path between them
dag_unordered() {
  local res a b ma mb sa sb
  for res in "${!DAG_RES[@]}"; do
    local -a ent=(${DAG_RES[$res]})
    for a in "${ent[@]}"; do for b in "${ent[@]}"; do
      ma=${a%%:*}; sa=${a#*:}; mb=${b%%:*}; sb=${b#*:}
      [ "$sa" \< "$sb" ] || continue
      [ "$ma" = w ] || [ "$mb" = w ] || continue
      dag_has "$sa" "$sb" && continue
      dag_has "$sb" "$sa" && continue
      echo "$res: $sa ($ma) and $sb ($mb) are not ordered"
    done; done
  done
}
