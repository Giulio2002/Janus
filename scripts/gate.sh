#!/usr/bin/env bash
# The gate: one driver for every check. It prebuilds once, then runs every stage as a parallel lane
# that reads the prebuilt outputs.
#
#   scripts/gate.sh [-j N | --jobs N|auto] [--lanes N] [--changed] [--only a,b,..] [--skip a,b,..] [--out DIR]
#
#   -j N        items at once in the verify pool (default $JANUS_JOBS, else 2: RULES.md on the shared box;
#               `auto` = the formula of scripts/lib/parallel.sh). The other stages scale with it: the go
#               test shards (max(2, N), one test slot each) and the audit lanes (N).
#   --lanes N   lanes at once (default $JANUS_LANES, else N + 1: the verify pool and N others). Lanes are
#               queued longest first by their time in the last run (artifacts/gate/lane-times).
#   --changed   development only (scripts/verify-all-examples.sh --changed): not a gate run.
#   --filter ERE   verify lane: only the items whose id matches (scripts/verify-all-examples.sh --filter)
#   --gotest-run ERE   go test lane: only the tests whose name matches
#   --rounds LIST  audit lane: only these rounds (audit/run-rounds.sh, e.g. "r2 r3")
#   --incremental  (or JANUS_GATE_INCREMENTAL=1) skip every item and lane for which the record of a PASS exists
#               whose key is identical: a content hash of every input of the item (cmd/janus/incr.go,
#               scripts/lib/incr.sh, docs/TESTING.md "Incremental gate"). Anything else runs, in full. The DEFAULT is
#               a FULL run, which stays mandatory before every push to main and nightly; an incremental run says
#               INCREMENTAL in its verdict and lists every item and lane as RAN or SKIPPED with the time, host and
#               commit of the PASS a skip replays. The prebuild, the build lanes and the axiom guard always run.
#   --explain ITEM  print the key components of an item (arm64:Add, cgo:amd64/CAdd, ...) or a lane (lane:gotest,
#               lane:rounds, ...) with their hashes, whether a record exists, and exit; nothing is run or recorded.
#   --speed-baseline record|enforce   `enforce` (default): compare with scripts/speed-baseline.tsv (fail on a
#               >1.5x item or total; with no file, "speed check NOT enforced: no baseline" is printed loudly
#               in the summary). `record`: after a passing FULL run write the baseline from the run (only
#               items that PASSED; the host load is in its header); commit it after a green full gate.
#
# Cancel a run: it is its own process group, and writes the group id to <out>/pgid; cancel with
#   kill -- -$(cat <out>/pgid)
# (or stop its memcap scope). Never kill by name or pattern: other gates share this host.
#   --only/--skip  stage lists (names below); a partial run says PARTIAL and writes no lane times.
#   --out DIR   logs and the timeline (default artifacts/gate/<UTC timestamp>, linked as artifacts/gate/latest)
#
# PHASE 1, prebuild (once; every later stage reads these read-only):
#   go build bin/janus (+ audit/bin/janus-rounds, the audit lanes' copy), `lake build` and
#   `lake build Janus Janus.Tools.Audit janus-audit`, the example binaries of every suite
#   (scripts/build-examples{,-amd64,-asm,-sys,-rtmisc,-print,-cgo}.sh), and the framework build and
#   replay verdict (a first verification of the Add example).
# PHASE 2, lanes (each a stage, its full log in <out>/lanes/<name>.log):
#   verify      scripts/verify-all-examples.sh --cgo: ONE queue of every arm64, amd64, asm, rtmisc, sys, print
#               and cgo item, longest first (scripts/lib/pool.sh), results streamed as they finish
#   gotest      scripts/gotest-shards.sh: `go test -timeout 7000s ./cmd/...` in balanced shards, every test once
#   rounds      audit/run-rounds.sh (all audit rounds, themselves parallel lanes)
#   axiom       scripts/ci-axiom-guard.sh
#   x86         scripts/x86formal.sh prove
#   asl-build   scripts/asl.sh build (JanusASL, ArmASL and janus-asl-check, once: lakes that build in one package race)
#   sail-build  scripts/oracle-sail.sh build (the Sail C oracle used by rtasl-fsqrt)
#   rtasl-prove (builds JanusASL first: set $ASL_CACHE; the others wait for it) rtasl-rel rtasl-strict rtasl-replay rtasl-btf rtasl-probes rtasl-fsqrt rtasl-go
#               audit/rt-asl/run.sh GROUP: the red-team round ASL, one lane per group
# The verdict is strict: a failed, timed-out or missing item or lane fails the gate (exit 1). Item timeouts
# (JANUS_ITEM_TIMEOUT), the audit, the kernel replay, the pins and every other check are those of the
# scripts the lanes run; this driver only schedules them.
#
# Output: a result line the moment each item or lane finishes (PASS/FAIL/TIMEOUT + wall seconds), a
# progress line every minute, <out>/timeline.jsonl (one JSON object per prebuild step, item, pool and
# lane: start/end epoch seconds, wall, status) and the report of scripts/gate-report.py at the end.
# Refuses to start with load >= 70, MemAvailable < 40 GiB or < 60 GiB free on the checkout's disk
# (RULES.md) unless JANUS_GATE_FORCE=1. LEAN_NUM_THREADS defaults to 4 and is capped at 4.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH
[ ! -d "$HOME/.elan/bin" ] || export PATH="$HOME/.elan/bin:$PATH"
# shellcheck source=lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
# shellcheck source=lib/pool.sh
. "$root/scripts/lib/pool.sh"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
# shellcheck source=lib/incr.sh
. "$root/scripts/lib/incr.sh"
memguard_self "$@"

# the lane-specific arguments of a lane's skip key (everything else comes from incr_lane)
lane_spec() {
  case "$1" in
    gotest) local sh=${jobs_n:-2}; [ "$sh" -ge 2 ] 2>/dev/null || sh=2
      printf '%s\n' --arg "run:${gtrun:-}" --arg "shards:$sh" ;;
    rounds) printf '%s\n' --arg "rounds:${rounds:-}" ;;
  esac
}
orig_args=("$@")
sbfile="${JANUS_SPEED_BASELINE:-$root/scripts/speed-baseline.tsv}"
jobs_n="${JANUS_JOBS:-}" lanes_n="${JANUS_LANES:-}" changed="" only="" skip="" out="" vfilter="" gtrun="" rounds="" upd="" sbmode=enforce incremental="${JANUS_GATE_INCREMENTAL:-}" explain_item=""
while [ $# -gt 0 ]; do
  case "$1" in
    -j|--jobs) jobs_n="${2:?-j needs a number}"; shift 2 ;;
    -j*) jobs_n="${1#-j}"; shift ;;
    --lanes) lanes_n="${2:?--lanes needs a number}"; shift 2 ;;
    --changed) changed=1; shift ;;
    --only) only="${2:?}"; shift 2 ;;
    --skip) skip="${2:?}"; shift 2 ;;
    --out) out="${2:?}"; shift 2 ;;
    --filter) vfilter="${2:?}"; shift 2 ;;
    --gotest-run) gtrun="${2:?}"; shift 2 ;;
    --rounds) rounds="${2:?}"; shift 2 ;;
    --incremental) incremental=1; shift ;;
    --explain) explain_item="${2:?--explain needs an item (e.g. arm64:Add) or a lane (e.g. lane:gotest)}"; shift 2 ;;
    --update-baseline) sbmode=record; shift ;;
    --speed-baseline) sbmode="${2:?}"; shift 2 ;;
    -h|--help) sed -n '2,/^set -uo/p' "${BASH_SOURCE[0]}" | sed '$d'; exit 0 ;;
    *) echo "usage: scripts/gate.sh [-j N|auto] [--lanes N] [--changed] [--only a,b] [--skip a,b] [--out DIR]" >&2; exit 2 ;;
  esac
done
if [ -z "$explain_item" ]; then
  # --explain mode and the pre-check mode make incr_begin report "skipped" without verifying anything: a variable
  # left in the environment must never reach a verifying gate
  unset JANUS_INCR_EXPLAIN JANUS_INCR_PRECHECK
fi
if [ -n "$explain_item" ]; then
  # --explain: no prebuild, no admission, no run; reads the prebuilt state of an earlier run
  export JANUS_INCR_EXPLAIN=1
  case "$explain_item" in
    lane:*) lname="${explain_item#lane:}"
      incr_lane "$lname" true $(lane_spec "$lname"); exit 0 ;;
    *) exec scripts/verify-all-examples.sh --cgo --explain --filter "^${explain_item//./\\.}\$" ;;
  esac
fi
# -j / --lanes not given (or -j auto): sized from the free cores and MemAvailable (scripts/lib/autojobs.sh),
# using the largest recorded per-item peak of the speed baseline; an explicit -j / JANUS_JOBS is used as given.
. "$root/scripts/lib/autojobs.sh"
autosized=""; auto_why=""; rounds_lanes_n=""; auto_budget=""
if [ -n "${JANUS_GATE_AUTO_WHY:-}" ]; then   # (the setsid re-exec below keeps the first sizing)
  autosized=1; auto_why="$JANUS_GATE_AUTO_WHY"; rounds_lanes_n="${JANUS_GATE_ROUNDS_LANES:-}"; auto_budget="${JANUS_GATE_AUTO_BUDGET:-}"
elif [ -z "$jobs_n" ] || [ "$jobs_n" = auto ]; then
  _pk0="$(autojobs_peak_gib "$sbfile")"
  read -r jobs_n auto_lanes auto_why < <(if [ -n "$_pk0" ]; then AUTOJOBS_PEAK_GIB="$_pk0" autojobs_size; else autojobs_size; fi)
  [ -n "$lanes_n" ] || lanes_n=$auto_lanes
  autosized=1
  # the audit rounds' own lane count (audit/run-rounds.sh reads JANUS_ROUNDS_LANES; an older one ignores it)
  rounds_lanes_n="${JANUS_ROUNDS_LANES:-$(autojobs_rounds_lanes)}"; auto_budget="$(autojobs_budget)"
  # the verify pool memory budget (GiB): per-item admission in scripts/verify-all-examples.sh
  export JANUS_VERIFY_MEM_BUDGET_GIB="${JANUS_VERIFY_MEM_BUDGET_GIB:-$(autojobs_verify_budget_gib)}"
fi
case "$jobs_n" in ''|*[!0-9]*|0) echo "gate: -j needs a positive number (got '$jobs_n')" >&2; exit 2 ;; esac
[ -n "$lanes_n" ] || lanes_n=$((jobs_n + 1))
case "$lanes_n" in ''|*[!0-9]*|0) echo "gate: --lanes needs a positive number (got '$lanes_n')" >&2; exit 2 ;; esac
export JANUS_JOBS=$jobs_n
# Admission control of every pool (scripts/lib/pool.sh): no new item starts when MemAvailable would fall below
# the floor (JANUS_GATE_MEM_FLOOR_GIB, default 30) plus one item's estimate (largest recorded peak x1.5, at least 4 GiB)
_pk="$(autojobs_peak_gib "$sbfile")"
export POOL_MEM_HEADROOM_KB=$(( ${JANUS_GATE_MEM_FLOOR_GIB:-30} * 1048576 ))
export POOL_JOB_MEM_KB=$(awk -v p="${_pk:-6.1}" 'BEGIN { i = p * 1.5; if (i < 4) i = 4; printf "%d", i * 1048576 }')
# incremental skipping is opt-in (the default is a full run); recording the passes is always on, so a full run
# feeds the next incremental one
export JANUS_INCR_RECORD=1
# records are written only for a clean tree that does not change during the run (scripts/lib/incr.sh)
unset JANUS_GATE_TREE0; incr_tree_pin
if [ -n "$incremental" ]; then export JANUS_GATE_INCREMENTAL=1; else unset JANUS_GATE_INCREMENTAL; fi
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"; [ "$LEAN_NUM_THREADS" -le 4 ] || export LEAN_NUM_THREADS=4

stages_all=(verify gotest rounds axiom govet cachekeys decoder x86 oracle asl-verify asl-build sail-build rtasl-prove rtasl-rel rtasl-strict rtasl-replay rtasl-btf rtasl-probes rtasl-fsqrt rtasl-go)
selected() { # NAME: is the stage selected?
  local n=$1
  if [ -n "$only" ]; then case ",$only," in *",$n,"*) ;; *) return 1 ;; esac; fi
  case ",$skip," in *",$n,"*) return 1 ;; esac
  return 0
}
partial=""
{ [ -n "$only" ] || [ -n "$skip" ] || [ -n "$changed" ] || [ -n "$vfilter" ] || [ -n "$gtrun" ] || [ -n "$rounds" ]; } && partial=1

# ---- admission (RULES.md)
load1=$(awk '{ print int($1) }' /proc/loadavg); memk=$(par_mem_available_kb)
free_g=$(df --output=avail -BG "$root" | tail -1 | tr -dc 0-9)
if [ "${JANUS_GATE_FORCE:-}" != 1 ]; then
  if [ "$load1" -ge 70 ] || [ "$memk" -lt $((40 * 1024 * 1024)) ] || [ "${free_g:-0}" -lt 60 ]; then
    echo "gate: host too busy (load $load1, MemAvailable $((memk / 1048576)) GiB, $free_g GiB free): need load < 70, >= 40 GiB, >= 60 GiB free (JANUS_GATE_FORCE=1 overrides)" >&2
    exit 3
  fi
fi

now() { date +%s.%N; }
[ -n "$out" ] || out="$root/artifacts/gate/$(date -u +%Y%m%dT%H%M%SZ)"
mkdir -p "$out/prebuild" "$out/lanes" "$out/verify"
ln -sfn "$out" "$root/artifacts/gate/latest" 2>/dev/null || true
tlf="$out/timeline.jsonl"; : > "$tlf"
# Own process group (setsid, once): every child of this run is in it, and a cancel is `kill -- -PGID`.
if [ "${JANUS_GATE_PG:-}" != "$out" ]; then
  export JANUS_GATE_PG="$out" JANUS_JOBS="$jobs_n" JANUS_LANES="$lanes_n"
  [ -z "$autosized" ] || export JANUS_GATE_AUTO_WHY="$auto_why" JANUS_GATE_ROUNDS_LANES="$rounds_lanes_n" JANUS_GATE_AUTO_BUDGET="$auto_budget"
  exec setsid --wait "$0" "${orig_args[@]}" --out "$out"
fi
echo "$$" > "$out/pgid"
echo "gate: process group $$ (cancel: kill -- -$$)"
# The isolated lake-lane source copies live under artifacts/gate/trees/<source hash>/ (not in the run's out
# dir): removed when the gate PASSES, kept when it fails or is cancelled (their cold builds are hours), and
# reused by a rerun of the same sources (same hash: git tree + uncommitted diff).
srchash="$( { git rev-parse 'HEAD^{tree}' 2>/dev/null; git diff HEAD 2>/dev/null; git ls-files -o --exclude-standard 2>/dev/null | sort | xargs -r sha256sum 2>/dev/null; } | sha256sum | cut -c1-16)"
treebase="$root/artifacts/gate/trees/$srchash"
cleanup() {
  local rc=${1:-$?}
  if [ "$rc" = 0 ]; then rm -rf "$treebase"; else [ ! -d "$treebase" ] || echo "gate: isolated lake-lane trees KEPT for a rerun of the same sources: $treebase"; fi
}
cancel() { trap '' TERM INT; echo "gate: cancelled"; kill -TERM -- -$$ 2>/dev/null; trap - EXIT; cleanup 143; exit 143; }
trap cancel TERM INT
trap 'cleanup $?' EXIT
tl_stage() { # KIND NAME START END RC
  printf '{"kind":"%s","name":"%s","start":%.3f,"end":%.3f,"wall":%.3f,"rc":%s}\n' "$1" "$2" "$3" "$4" "$(echo "$4 - $3" | bc)" "$5" >> "$tlf"
}
gate_t0=$(now)
export JANUS_GATE_T0=$gate_t0
sha="$(git rev-parse --short HEAD 2>/dev/null || echo '?')$(git diff --quiet HEAD 2>/dev/null || echo '+dirty')"
printf '{"kind":"gate","commit":"%s","jobs":%s,"lanes":%s,"load1":%s,"memAvailGiB":%s,"cores":%s,"start":%.3f,"partial":%s,"auto":%s,"why":"%s","roundsLanes":"%s","memBudget":"%s"}\n' \
  "$sha" "$jobs_n" "$lanes_n" "$load1" "$((memk / 1048576))" "$(nproc)" "$gate_t0" "$([ -n "$partial" ] && echo true || echo false)" \
  "$([ -n "$autosized" ] && echo true || echo false)" "$(_pool_json "${auto_why:-given}")" "$rounds_lanes_n" "$(_pool_json "$auto_budget")" >> "$tlf"
[ -z "$autosized" ] || echo "gate: -j $jobs_n, $lanes_n lanes chosen automatically: $auto_why; audit rounds: ${rounds_lanes_n:-default} lanes
gate: $auto_budget"
echo "gate: $sha, pool -j $jobs_n, $lanes_n lanes, load $load1, MemAvailable $((memk / 1048576)) GiB, $(nproc) cores; logs and timeline in $out${partial:+; PARTIAL RUN (--only/--skip/--changed)}"

# ---- the prebuild stages (they are items of the same pool as the lanes: scripts/lib/dag.sh)
step() { # NAME CMD...: a prebuild step, logged and timed; returns its status
  local name=$1 s e rc=0; shift
  s=$(now); "$@" > "$out/prebuild/$name.log" 2>&1 || rc=$?; e=$(now)
  tl_stage prebuild "$name" "$s" "$e" "$rc"
  printf 'prebuild %-12s %-4s %8.1fs\n' "$name" "$([ $rc = 0 ] && echo ok || echo FAIL)" "$(echo "$e - $s" | bc)"
  [ $rc = 0 ] || { echo "  ---- $out/prebuild/$name.log ----"; tail -n 25 "$out/prebuild/$name.log" | sed 's/^/  | /'; }
  return $rc
}
# JanusTests and janus-oracle-amd64 are built by CI (.github/workflows/ci.yml) and are not default Lake targets
pre_lake() { memguard_lake build && memguard_lake build Janus Janus.Tools.Audit janus-audit && memguard_lake build JanusTests janus-oracle janus-oracle-amd64 janus-decode janus-testfloat; }
pre_gobin() { CGO_ENABLED=0 go build -o bin/janus ./cmd/janus; }
pre_rounds_bin() { mkdir -p audit/bin && cp -f bin/janus audit/bin/janus-rounds.new && mv -f audit/bin/janus-rounds.new audit/bin/janus-rounds; }
# The go tests' prebuilt framework fixture (cmd/janus/fixture_test.go, docs/TESTING.md "Go tests"): built here, once, by
# the tests' TestMain (a run that selects no test), so the gotest lane does not pay for it; it runs beside the verify pool.
pre_fixture() { JANUS_JOBS="$jobs_n" go test -count=1 -timeout 7000s ./cmd/janus -run '^$'; }
pre_stamp() { JANUS_ROOT="$root" JANUS_EXAMPLES_PREBUILT=1 scripts/verify-examples.sh -j 1 Add; }
pre_warm() { JANUS_EXAMPLES_PREBUILT=1 scripts/verify-examples.sh -j 1 Add; }
# From the moment the shared framework build (.lake/build) is finished nothing may write it (a lake that rebuilds a
# module while another lane's verification has pinned its .olean fails that verification: "framework build changed after
# the kernel replay"). pre-pin hashes the finished build and switches scripts/lib/lakeguard/lake on (it turns every
# `lake build`/`lake exe` in this checkout's package into --no-build); every READER of the build needs pre-pin, so none starts
# before the build it reads has finished and been hashed. The oleans are hashed again at the end of the run.
fw_hash() { (cd "$root/.lake/build" && find . -type f \( -name '*.olean*' -o -name '*.ir' -o -name '*.ilean' \) -print0 | sort -z | xargs -0 sha256sum | sha256sum | cut -d' ' -f1); }
pre_pin() { fw_hash > "$out/fw_hash0" && : > "$out/.pinned" && echo "gate: framework build pinned ($(cat "$out/fw_hash0")); lake build/exe in the shared checkout is --no-build from here on"; }
# a rerun into the same --out must not find the last run's marker: it would arm the lakeguard before pre-lake ran
rm -f "$out/.pinned" "$out/fw_hash0"
JANUS_REAL_LAKE="$(command -v lake)"; export JANUS_REAL_LAKE JANUS_LAKEGUARD_ROOT="$root" JANUS_LAKEGUARD_PIN="$out/.pinned"
export PATH="$root/scripts/lib/lakeguard:$PATH"
export JANUS_EXAMPLES_PREBUILT=1 JANUS_GATE_PREBUILT=1
. "$root/scripts/lib/dag.sh"
dag_check || { echo "gate: internal error: the stage graph is inconsistent"; exit 1; }

# ---- phase 2: lanes
# The JanusASL / JanusX86 / oracle lanes run lake in packages that depend on the framework by path: such a
# lake REPLAYS (rewrites) Janus/*.olean in the framework build it is pointed at, and a verification that
# reads .lake/build at that moment fails ("changed after the proof compile", a missing .olean). They
# therefore work in a private copy of the sources (and a copy of the finished framework build), so the
# prebuilt build the verify, go test and audit lanes read is never written after the prebuild. Their own
# package builds (JanusASL/.lake, JanusX86/.lake, oracle-sail/target) and artifacts/ are shared by
# symlink: only these lanes use the former, and artifacts/ is read-only to them.
mktree() { # DIR [private]: a private copy of the sources and of the finished framework build (kept when present: same hash)
  # "private": JanusASL/.lake is a real directory of the tree's own (filled from the verified ASL cache by asl.sh), not
  # the symlink to the checkout's build that the other lake trees share; a lane in such a tree can never write the checkout
  if [ -f "$1/.gate-tree-ready" ]; then echo "gate: reusing $1"; return 0; fi
  mkdir -p "$1"
  rsync -a --exclude=/.git --exclude=/artifacts --exclude=/audit/bin --exclude=/JanusASL/.lake --exclude=/JanusX86/.lake \
    --exclude=/oracle-sail/target --exclude=/bin ./ "$1"/ || { echo "gate: cannot copy the sources to $1"; exit 1; }
  ln -sfn "$root/artifacts" "$1/artifacts"; if [ "${2:-}" = private ]; then mkdir -p "$1/JanusASL/.lake"; else ln -sfn "$root/JanusASL/.lake" "$1/JanusASL/.lake"; fi
  ln -sfn "$root/JanusX86/.lake" "$1/JanusX86/.lake"; ln -sfn "$root/oracle-sail/target" "$1/oracle-sail/target"
  mkdir -p "$1/bin"; cp -f bin/janus "$1/bin/janus"; : > "$1/.gate-tree-ready"
}
# x86 has a tree of its own, the JanusASL/oracle/rt-asl lanes another: two lakes in one tree race on its .oleans
tree_x86="$treebase/x86" tree="$treebase/asl" tree_aslv="$treebase/aslv" tree_go="$treebase/go"
mkdir -p "$treebase"
exec {treelock}>"$treebase.lock"
flock -n "$treelock" || { echo "gate: another run uses the same sources/trees ($treebase); wait for it"; exit 1; }
# the JanusASL cache hook (scripts/asl.sh ASL_CACHE; agent/speed-asl's JANUS_ASL_CACHE is accepted as an alias;
# its interface is not final, this only forwards the directory)
[ -n "${ASL_CACHE:-}" ] || { [ -z "${JANUS_ASL_CACHE:-}" ] || export ASL_CACHE="$JANUS_ASL_CACHE"; }
mkdir -p "$root/JanusASL/.lake" "$root/JanusX86/.lake" "$root/oracle-sail/target"
echo "gate: isolated source copies for the lake lanes are made once the framework build is pinned (removed when the gate passes, kept otherwise: $treebase)"
lane_times="$root/artifacts/gate/lane-times"
shards=$jobs_n; [ "$shards" -ge 2 ] || shards=2
pool_init gate "$((lanes_n + 4))" "$out/lanes"   # (+4 slots: the prebuild stages and tree copies share the pool)
POOL_GUARD=0 POOL_PROGRESS_SECS="${POOL_PROGRESS_SECS:-60}"
export POOL_TIMELINE="$tlf"   # the verify pool of the verify lane appends its items too
# an estimate for the first run (seconds, the profile's measurements); later runs use their own
declare -A est=([verify]=99999 [gotest]=1600 [rounds]=1000 [x86]=620 [asl-build]=900 [sail-build]=300 [axiom]=1 [govet]=60 [cachekeys]=30 [decoder]=120 [oracle]=900 [asl-verify]=900
  [rtasl-probes]=1200 [rtasl-replay]=900 [rtasl-prove]=600 [rtasl-fsqrt]=600 [rtasl-go]=400 [rtasl-rel]=120 [rtasl-strict]=120 [rtasl-btf]=5)
for k in "${!est[@]}"; do POOL_SECS[$k]=${est[$k]}; done
pool_times "$lane_times"
POOL_SECS[verify]=99999
# Per-lane memory limit (memguard's per-job default of 24G applies inside the outer cap unless JANUS_MEM_MAX is
# set): measured peaks in docs/TESTING.md "Lane memory limits". JANUS_GATE_MEM_<LANE> (e.g. JANUS_GATE_MEM_ASL_BUILD=64G) overrides.
declare -A lanemem=([asl-build]=48G [sail-build]=48G [x86]=24G [gotest]=24G [rounds]=24G [axiom]=24G [govet]=8G [cachekeys]=8G [decoder]=8G [oracle]=24G [asl-verify]=48G [testlane]=48G)
for g in prove rel strict replay btf probes fsqrt go; do lanemem[rtasl-$g]=48G; done
add() { # NAME CODE [NEEDS]
  selected "$1" || return 0
  local v="JANUS_GATE_MEM_${1//-/_}"; v="${v^^}"
  local m="${!v:-${lanemem[$1]:-}}"
  # (verify: no JANUS_MEM_MAX, its items bound themselves as before)
  [ -z "$m" ] || set -- "$1" "export JANUS_MEM_MAX=$m; $2" "${3:-}"
  WANT+=("$1")
  pool_add "$1" "$2" "$1" "${DAG_DEPS[$1]:-} ${3:-}"
}
# addc: a lane that may be skipped on the record of an identical PASS (incr_lane: scripts/lib/incr.sh)
addc() { # NAME CODE [NEEDS]
  local spec
  spec="$(lane_spec "$1" | while IFS= read -r l; do printf ' %q' "$l"; done)"
  add "$1" "incr_lane $(printf '%q' "$1") $(printf '%q' "$2")$spec" "${3:-}"
}
# Lanes that share an isolated tree run `lake` through scripts/lib/lanelake/lake: every lake call in the tree holds
# a flock on the tree (exclusive for anything that can rewrite the package, shared for `lake env`), so a lane's
# rebuild or dependency re-resolution never overlaps another lane's lake call (scripts/lib/test-lanelake.sh).
laneenv() { # TREE: the environment of a lane working in TREE (JANUS_REAL_LAKE is exported above)
  echo "export JANUS_LANE_TREE='$1' JANUS_LANE_LAKE_LOCK='$1/.gate-lake.lock' PATH='$root/scripts/lib/lanelake':\"\$PATH\";"
}
WANT=()
# a lane needs its prerequisite only when that stage is part of this run
needs() { local r="" n; for n in "$@"; do ! selected "$n" || r="${r:+$r }$n"; done; echo "$r"; }
add verify "scripts/verify-all-examples.sh -j $jobs_n --cgo ${changed:+--changed} ${incremental:+--incremental} ${vfilter:+--filter '$vfilter'}"
JANUS_POOL_DIR="$out/verify"; export JANUS_POOL_DIR
addc gotest "JANUS_JOBS=$jobs_n scripts/gotest-shards.sh -n $shards ${gtrun:+--run '$gtrun'} --outdir '$out/gotest'"
addc rounds "${rounds_lanes_n:+export JANUS_ROUNDS_LANES=$rounds_lanes_n; }audit/run-rounds.sh $rounds"
add axiom "scripts/ci-axiom-guard.sh"
# (self-test hook, scripts/lib/test-gatelanes.sh: one extra lane running JANUS_GATE_TEST_LANE in the lake tree)
[ -z "${JANUS_GATE_TEST_LANE:-}" ] || add testlane "$(laneenv "$tree") cd '$tree' && $JANUS_GATE_TEST_LANE"
addc x86 "$(laneenv "$tree_x86") cd '$tree_x86' && scripts/x86formal.sh prove"
# CI checks that the gate used to lack (docs/TESTING.md "CI vs gate"): go vet, the JanusASL cache-key tests, the
# decoder coverage of the arm64 examples, the quick differential oracles (qemu / native), and `asl.sh verify`
add govet "go vet ./..."
add cachekeys "JanusASL/tools/test_asl_cache.sh && JanusASL/tools/test_asl_mod_cache.sh"
add decoder "BLOCKERS_OUT='$out/decoder' scripts/decoder-coverage.sh"
add oracle "$(laneenv "$tree") cd '$tree' && for s in oracle oracle-amd64; do O='$out/'\$s; mkdir -p \"\$O\"; OUT=\"\$O\" KEEP=1 JOBS=4 scripts/\$s.sh quick || exit 1; ! grep -q '\"verdict\":\"MISMATCH\"' \"\$O/verdicts.jsonl\" || { cat \"\$O/repro.md\"; exit 1; }; done" "$(needs rtasl-prove)"
add asl-verify "$(laneenv "$tree_aslv") cd '$tree_aslv' && scripts/asl.sh verify | tee '$out/asl-verify.txt' && test \"\$(grep -c ': ASL corollary verified' '$out/asl-verify.txt')\" = 4 && test ! -L '$tree_aslv/JanusASL/.lake'" "$(needs asl-build)"
add asl-build "$(laneenv "$tree") cd '$tree' && scripts/asl.sh build"
add sail-build "$(laneenv "$tree") cd '$tree' && scripts/oracle-sail.sh build"
for g in prove rel strict replay btf probes fsqrt go; do
  nd=""
  # rtasl-prove (scripts/asl.sh prove) builds JanusASL; two lakes in one package race, so every other lake-using
  # group runs after it (as in audit/rt-asl/run.sh, where prove is the first group)
  case "$g" in prove) nd="$(needs asl-build)" ;; btf|go) ;; fsqrt) nd="$(needs rtasl-prove sail-build)" ;; *) nd="$(needs rtasl-prove)" ;; esac
  gt="$tree"; [ "$g" != go ] || gt="$tree_go"
  addc "rtasl-$g" "$(laneenv "$gt") export RT_ASL_KEEP_DIR='$out/lanes/rtasl-$g.keep'; cd '$gt' && audit/rt-asl/run.sh $g" "$nd"
done
# The stages the selected lanes need (and only those: a run with --only builds only what it reads), queued with their
# dependencies. Prebuild stages and trees are not subject to --only/--skip.
declare -A STAGE_CODE=(
  [pre-gobin]="step pre-gobin pre_gobin" [pre-lake]="step pre-lake pre_lake" [pre-rounds-bin]="step pre-rounds-bin pre_rounds_bin"
  [pre-ex-arm64]="step pre-ex-arm64 scripts/build-examples.sh" [pre-ex-amd64]="step pre-ex-amd64 bash scripts/build-examples-amd64.sh"
  [pre-ex-asm]="step pre-ex-asm scripts/build-examples-asm.sh" [pre-ex-sys]="step pre-ex-sys scripts/build-examples-sys.sh"
  [pre-ex-rtmisc]="step pre-ex-rtmisc scripts/build-examples-rtmisc.sh" [pre-ex-print]="step pre-ex-print scripts/build-examples-print.sh"
  [pre-ex-cgo]="step pre-ex-cgo scripts/build-examples-cgo.sh"
  [pre-stamp]="step pre-stamp pre_stamp" [pre-warm]="step pre-warm pre_warm" [pre-fixture]="step pre-fixture pre_fixture" [pre-pin]="step pre-pin pre_pin"
  [tree-x86]="mktree '$tree_x86'" [tree-asl]="mktree '$tree'" [tree-aslv]="mktree '$tree_aslv' private" [tree-go]="mktree '$tree_go'"
)
# est: long first (the framework build is the critical path of the cold gate)
declare -A STAGE_EST=([pre-lake]=800 [pre-fixture]=300 [pre-warm]=120 [pre-gobin]=60 [pre-ex-amd64]=15)
declare -A queued=()
for n in $(dag_closure "${WANT[@]}"); do
  [ -n "${STAGE_CODE[$n]:-}" ] || continue
  queued[$n]=1
  : "${POOL_SECS[$n]:=${STAGE_EST[$n]:-30}}"
  pool_add "$n" "${STAGE_CODE[$n]}" "$n" "${DAG_DEPS[$n]:-}"
done
# stream the verify lane's own result lines as they are written
tailpid=""
if selected verify; then
  : > "$out/lanes/verify.log"
  tail -n +1 -F "$out/lanes/verify.log" 2>/dev/null | sed -u 's/^/verify | /' & tailpid=$!
fi
lanes_rc=0
l0=$(now)
pool_run || lanes_rc=$?
l1=$(now)
# the timeline holds this gate's own items and lanes only: no self-test pool (their pools are all named selftest-*,
# a prefix no real pool has) (their scripts run with a private
# out dir and timeline; a leak would corrupt the baseline)
if grep -q '"pool":"selftest-' "$tlf"; then
  echo "gate: FAILED: self-test pools leaked into the gate's timeline ($tlf):"; grep '"pool":"selftest-' "$tlf" | head -3
  lanes_rc=1
fi
tl_stage stage lanes "$l0" "$l1" "$lanes_rc"
[ -z "$tailpid" ] || { sleep 1; kill "$tailpid" 2>/dev/null; wait "$tailpid" 2>/dev/null; } || true

# the lane times of this run for the next one's order (only a full, passing lane)
if [ -z "$partial" ]; then
  mkdir -p "$(dirname "$lane_times")"
  { [ -f "$lane_times" ] && cat "$lane_times"; cat "$out"/lanes/*.time 2>/dev/null; } |
    awk -F'\t' '{ t[$1] = $2 } END { for (k in t) printf "%s\t%s\n", k, t[k] }' | sort > "$lane_times.tmp" && mv "$lane_times.tmp" "$lane_times"
fi
gate_t1=$(now)
tl_stage stage gate "$gate_t0" "$gate_t1" "$lanes_rc"
python3 -I "$root/scripts/gate-report.py" "$tlf" || true
# the speed-regression check (on top of every other check): scripts/gate-speedcheck.py, committed baseline
# scripts/speed-baseline.tsv; a regression fails the gate whatever the host load
speed_rc=0
if [ "$sbmode" = record ]; then
  if [ -z "$partial" ] && [ "$lanes_rc" = 0 ]; then
    python3 -I "$root/scripts/gate-speedcheck.py" update "$tlf" "$sbfile" "$out/verify" "$root/artifacts"
    echo "speed check: baseline RECORDED in $sbfile (commit it after reviewing); no comparison made"
  else
    echo "speed check: baseline NOT recorded (record needs a passing full run)"
  fi
elif [ -f "$sbfile" ]; then
  python3 -I "$root/scripts/gate-speedcheck.py" check "$tlf" "$sbfile" "$out/verify" "$root/artifacts" || speed_rc=$?
else
  echo "!!!! speed check NOT enforced: no baseline file $sbfile (record one with --speed-baseline record after a green full gate) !!!!"
fi
[ "$speed_rc" = 0 ] || lanes_rc=1
if [ -f "$out/fw_hash0" ]; then FW_HASH0="$(cat "$out/fw_hash0")"; FW_HASH1="$(fw_hash)"; fi
if [ -f "$out/fw_hash0" ] && [ "$FW_HASH1" != "$FW_HASH0" ]; then echo "gate: FAIL: the shared framework build changed during the lanes ($FW_HASH0 -> $FW_HASH1)"; lanes_rc=1; fi
echo
if [ "$lanes_rc" = 0 ]; then
  echo "GATE PASS$([ -n "$partial" ] && echo ' (PARTIAL RUN: not a full gate)')$([ -n "$incremental" ] && echo ' (INCREMENTAL: items and lanes with a record of an identical PASS were skipped, see the RAN/SKIPPED report; the full cold gate is still required before a push to main)') in $(_pool_fmt "$(echo "$gate_t1 - $gate_t0" | bc)")"
  exit 0
fi
echo "GATE FAIL in $(_pool_fmt "$(echo "$gate_t1 - $gate_t0" | bc)"): ${POOL_FAILED[*]}"
exit 1
