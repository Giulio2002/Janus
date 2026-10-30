#!/usr/bin/env bash
# Verify every arm64 example proof (with the WrongAdd demonstration), every amd64 example
# theorem and the Go assembly (ABI0) examples of both ISAs in one pool of parallel jobs:
# scripts/verify-examples.sh, scripts/verify-amd64-examples.sh and
# scripts/verify-asm-examples.sh and scripts/verify-rtmisc-examples.sh one item at a time, longest first (by the times measured in the
# last run, artifacts/verify-all-examples.times; a built-in order before the first run), so that
# the long proofs overlap the rest instead of ending the run alone.
# The kernel examples (scripts/verify-sys-examples.sh) and the print examples
# (scripts/verify-print-examples.sh) are items of the same queue; --cgo adds the cgo rows
# (scripts/verify-cgo-examples.sh, the slowest suite). One queue, one pool (scripts/lib/pool.sh):
# every item's result line (PASS / FAIL / TIMEOUT and its wall seconds) is printed the moment it
# finishes, with a progress line every minute; the full log of each item is kept in
# $JANUS_POOL_DIR (default artifacts/verify-all-logs/).
# Usage: scripts/verify-all-examples.sh [-j N] [--incremental|--changed] [--explain] [--cgo]
#   -j N        jobs at once (default and memory admission: scripts/lib/parallel.sh).
#   --cgo       also verify the cgo rows (examples/proofs-cgo) in the same queue.
#   --filter ERE   development only: queue just the items whose id ("arm64:Add", "cgo:amd64/CAdd", ...)
#               matches the regular expression; not a gate run.
#   --incremental  (also --changed, or JANUS_GATE_INCREMENTAL=1) skip every item for which the record of a
#               PASS exists whose key is identical: a content hash of EVERY input of the item (its
#               extraction, proof file, the transitive import closure of its modules with their compiled
#               data, the toolchain, the verifier identity, the auditor and leanchecker, the pins, these
#               scripts, the item's arguments and environment: cmd/janus/incr.go, scripts/lib/incr.sh).
#               Anything else -- no record, a damaged or foreign one, an input that cannot be hashed --
#               runs the item, and every item that runs is still checked in full. The default is a FULL
#               run; the full cold gate is mandatory before every push to main and nightly.
#   --explain   (JANUS_INCR_EXPLAIN=1) print the key components of the selected items (use with --filter)
#               and run nothing.
# Every item prints its time, or why it was skipped, and the run ends with a RAN / SKIPPED line per item
# (a skip names the time, host and commit of the PASS it replays) and totals. Exits non-zero if any item
# fails. Every item that passes is recorded (JANUS_INCR_RECORD=1, set here) for later incremental runs.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
# shellcheck source=lib/pool.sh
. "$root/scripts/lib/pool.sh"
par_init "$@"
changed=""
explain=""
cgo=""
filter=""
args=(${PAR_ARGS[@]+"${PAR_ARGS[@]}"})
for ((i = 0; i < ${#args[@]}; i++)); do
  case "${args[$i]}" in
    --changed|--incremental) changed=1 ;;
    --explain) explain=1 ;;
    --cgo) cgo=1 ;;
    --filter) i=$((i + 1)); filter="${args[$i]:?--filter needs a regular expression}" ;;
    *) echo "usage: scripts/verify-all-examples.sh [-j N] [--incremental|--changed] [--explain] [--cgo] [--filter ERE]" >&2; exit 2 ;;
  esac
done
# the incremental gate (scripts/lib/incr.sh): skipping is opt-in; recording the passes is the default
[ -z "$changed" ] || export JANUS_GATE_INCREMENTAL=1
if [ -n "$explain" ]; then export JANUS_INCR_EXPLAIN=1; else unset JANUS_INCR_EXPLAIN JANUS_INCR_PRECHECK; fi
export JANUS_INCR_RECORD="${JANUS_INCR_RECORD:-1}"
# records are written only for a clean tree that does not change during the run (scripts/lib/incr.sh)
. scripts/lib/incr.sh
incr_tree_pin

# JANUS_EXAMPLES_PREBUILT=1 (scripts/gate.sh): bin/janus, the examples' binaries and the framework
# build exist already (built once by the gate); nothing is rebuilt.
if [ "${JANUS_EXAMPLES_PREBUILT:-}" != 1 ]; then
  CGO_ENABLED=0 go build -o bin/janus ./cmd/janus
  scripts/build-examples.sh >/dev/null
  bash scripts/build-examples-amd64.sh >/dev/null 2>&1
  scripts/build-examples-asm.sh >/dev/null
  scripts/build-examples-sys.sh >/dev/null 2>&1
  scripts/build-examples-rtmisc.sh >/dev/null
  scripts/build-examples-print.sh >/dev/null 2>&1
  [ -z "$cgo" ] || scripts/build-examples-cgo.sh >/dev/null
  [ -n "${JANUS_ROOT:-}" ] && (cd "$JANUS_ROOT" && lake build Janus >/dev/null)
  [ -z "$cgo" ] || lake build Janus >/dev/null
fi
export JANUS_EXAMPLES_PREBUILT=1

# The built-in order (longest first, measured), then the rest in the scripts' order.
arm64=(MallocFast RuneLen SumRunes ClearWords A64IndexByte A64Crc32 A64CountByte CopyBlock AddLimbs A64Equal64 Add Max Add128 Mul64 Add256 Div Get AddThree
       Sum SetOne256 HexDigit CopyWords SumSquares AtomicAdd AtomicMax HashWith HashTwice MapSum DeferAdd
       AddF64 Dot3 F64ToU64 Abs NewPair MakeSlice AppendOne SetNext
       Lookup Insert InsertGet Delete SumValues CountKeys LookupKey16 NewMap ClearMap MapAccess1Small
       LookupS InsertS DeleteS LookupK24 InsertK24 Has32 Set32 InsertPtr LookupPtr MakeHint
       Concat ToBytes FromBytes AppendPoint CopyNodes WriteBarrier
       PanicIf DeferInc IndexAt LoadField DeferTwice RecoverSet DeferOrder DeferMix GoexitDefer RangeDefer NestedPanic NestedRecover
       ReverseArray RowsWith SwapBig DotBoth Find2D Fact Compose Shifts AlignUp TotalMeters TotalFeet
       Slice3 Slice2 Sum3 Triangle GotoSum Log2 SumBelow IterSum DivMod10 BitMerge MinMax ClearArray
       Mod IncTwice Bump GlobalTable Table MakeAdder IsEven CycA MulAlgo Double BigLocal SumRec HoldPtr
       SpanSum MinStr I64ToF64 F64ToI64 U64ToF64 F64ToF32 F32ToF64 LoadThird MinF64 MaxF64
       Box AsHasher Classify Equal ScratchSum StackGrow Eq32 StrEq F64Eq CopyTrees ClearTrees LookupStr HashFKey EqFKey
       WrongAdd)
. scripts/example-contracts.sh
arm64+=($runtime_examples $runtime_examples_arm64_only)
amd64=()
for d in examples/proofs-amd64/*/; do amd64+=("$(basename "$d")"); done
asm=()
for f in examples/asm/proofs/*/*.lean; do asm+=("$(basename "$(dirname "$f")")/$(basename "$f" .lean)"); done
items=()
for n in "${arm64[@]}"; do items+=("arm64:$n"); done
for f in "${amd64[@]}"; do items+=("amd64:$f"); done
for t in "${asm[@]}"; do items+=("asm:$t"); done
rtmisc=()
for f in examples/rtmisc/proofs/*/*.lean; do rtmisc+=("$(basename "$(dirname "$f")")/$(basename "$f" .lean)"); done
# split examples: a Lake package per function, one module per runtime-call segment
for f in examples/rtmisc/proofs/*/*/lakefile.toml; do d="$(dirname "$f")"; rtmisc+=("$(basename "$(dirname "$d")")/$(basename "$d")"); done
for t in "${rtmisc[@]}"; do items+=("rtmisc:$t"); done
# the kernel examples, the print examples and (--cgo) the cgo rows: the rows of their own scripts
sys=(); prt=(); cgorows=()
mapfile -t sys < <(scripts/verify-sys-examples.sh --list)
mapfile -t prt < <(scripts/verify-print-examples.sh --list)
for t in "${sys[@]}"; do items+=("sys:$t"); done
for t in "${prt[@]}"; do items+=("print:$t"); done
if [ -n "$cgo" ]; then
  mapfile -t cgorows < <(scripts/verify-cgo-examples.sh --list)
  for t in "${cgorows[@]}"; do items+=("cgo:$t"); done
fi

if [ -n "$filter" ]; then
  mapfile -t items < <(printf '%s\n' "${items[@]}" | grep -E -e "$filter" || true)
  echo "verify-all-examples: --filter '$filter': ${#items[@]} items (development only, not a gate run)"
fi
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
broken=()
wall=$(date +%s)

times="$root/artifacts/verify-all-examples.times"

tmp_unused=""
. scripts/example-contracts.sh
declare -A asm_sym=(
  [AddAsm]=example.com/asm.AddAsm.abi0 [XorSlice]=example.com/asm.XorSlice.abi0
  [Twice]=example.com/asm.Twice.abi0 [CallXor]=example.com/asm.CallXor
  [XorWrapper]=example.com/asm.XorSlice
)

# run_item ITEM: one item of the pool. Everything it prints is the item's log; its exit status is
# its verdict (0: passed, or skipped by the incremental gate on the record of an identical PASS: the
# per-kind scripts decide that, scripts/lib/incr.sh).
run_item() {
  local it=$1 kind=${1%%:*} n=${1#*:} rc=0
  case "$kind" in
    arm64) JANUS_EXAMPLES_SUMMARY="$tmp/arm64-$n" scripts/verify-examples.sh -j 1 "$n" || rc=$? ;;
    amd64) scripts/verify-amd64-examples.sh -j 1 "$n" || rc=$? ;;
    asm) JANUS_EXAMPLES_SUMMARY="$tmp/asm-${n//\//_}" scripts/verify-asm-examples.sh -j 1 "$n" || rc=$? ;;
    rtmisc) JANUS_EXAMPLES_SUMMARY="$tmp/rtmisc-${n//\//_}" scripts/verify-rtmisc-examples.sh -j 1 "$n" || rc=$? ;;
    sys) JANUS_EXAMPLES_SUMMARY="$tmp/sys-${n//\//_}" scripts/verify-sys-examples.sh -j 1 "$n" || rc=$? ;;
    print) JANUS_EXAMPLES_SUMMARY="$tmp/print-${n//\//_}" scripts/verify-print-examples.sh -j 1 "$n" || rc=$? ;;
    cgo) JANUS_EXAMPLES_SUMMARY="$tmp/cgo-${n//\//_}" scripts/verify-cgo-examples.sh -j 1 "$n" || rc=$? ;;
    *) echo "run_item: unknown kind $kind"; rc=2 ;;
  esac
  return $rc
}

# one snapshot of the print proof package for all print items (see scripts/verify-print-examples.sh)
if [ ${#prt[@]} -gt 0 ]; then
  JANUS_PRINT_SNAPSHOT="$(mktemp -d "$root/examples/.print-proofs.XXXXXX")"
  export JANUS_PRINT_SNAPSHOT
  cp -r examples/proofs-print/. "$JANUS_PRINT_SNAPSHOT"/
  trap 'rm -rf "$tmp" "$JANUS_PRINT_SNAPSHOT"' EXIT
fi
# (no per-item cgroup: every item's script bounds its own janus jobs, as before; a print row runs several
# Lean jobs at once and needs far more than one pool slot's budget)
POOL_GUARD=0
pooldir="${JANUS_POOL_DIR:-$root/artifacts/verify-all-logs}"
rm -rf "$pooldir"
pool_init verify "$PAR_JOBS" "$pooldir"
# per-item memory admission when the gate gave the pool a budget (scripts/lib/pool.sh): each running item reserves its
# own recorded peak x1.3 (the conservative estimate when unknown) of JANUS_VERIFY_MEM_BUDGET_GIB
if [ -n "${JANUS_VERIFY_MEM_BUDGET_GIB:-}" ]; then
  POOL_BUDGET_KB=$(awk -v g="$JANUS_VERIFY_MEM_BUDGET_GIB" 'BEGIN { printf "%d", g * 1048576 }');
  pool_peaks "${JANUS_SPEED_BASELINE:-$root/scripts/speed-baseline.tsv}"
fi
pool_times "$times"
# --incremental: first find out, for every item, whether the record of an identical PASS exists (the item's own
# script decides, JANUS_INCR_PRECHECK=1: it extracts, computes the key and exits 90 if the item must run;
# light work, many at once, no pool slot). Only the items that must run are queued.
queue=("${items[@]}")
if [ -n "$changed" ] && [ -z "$explain" ]; then
  pre="$pooldir/precheck"; mkdir -p "$pre"
  pre_jobs="${JANUS_PRECHECK_JOBS:-8}"
  echo "incremental pre-check of ${#items[@]} items ($pre_jobs at once)"
  for it in "${items[@]}"; do
    f="$(_pool_file "$it")"
    while [ "$(jobs -rp | wc -l)" -ge "$pre_jobs" ]; do wait -n 2>/dev/null || true; done
    ( JANUS_INCR_PRECHECK=1 run_item "$it" > "$pre/$f.log" 2>&1; echo $? > "$pre/$f.rc" ) &
  done
  wait
  queue=()
  skip_n=0
  for it in "${items[@]}"; do
    f="$(_pool_file "$it")"
    if [ "$(cat "$pre/$f.rc" 2>/dev/null)" = 0 ] && grep -q ' skipped (unchanged' "$pre/$f.log"; then
      cp "$pre/$f.log" "$pooldir/$f.log"; echo 0 > "$pooldir/$f.rc"; echo 0 > "$pooldir/$f.secs"
      skip_n=$((skip_n + 1))
      printf 'SKIP    %-34s %s\n' "$it" "$(grep -m1 ' skipped (unchanged' "$pre/$f.log" | sed 's/^.*skipped (unchanged: //')"
      if [ -n "${POOL_TIMELINE:-}" ]; then
        note="$(grep -m1 ' skipped (unchanged' "$pre/$f.log" | sed 's/^.*skipped (unchanged: //; s/)$//' | cut -c1-300)"
        printf '{"kind":"item","pool":"verify","id":"%s","status":"SKIP","rc":0,"start":%.3f,"end":%.3f,"wall":0,"note":"%s"}\n' \
          "$(_pool_json "$it")" "$(_pool_now)" "$(_pool_now)" "$(_pool_json "$note")" >> "$POOL_TIMELINE"
      fi
    else
      queue+=("$it")
    fi
  done
  echo "incremental pre-check: ${skip_n} skipped, ${#queue[@]} to run"
fi
queued() { printf '%s\n' "${queue[@]}" | grep -qxF -- "$1"; }
for it in "${queue[@]}"; do
  needs=""
  # the first print row of an ISA builds the lemma modules every row of that ISA imports (in the shared
  # snapshot's consumer workspace); the other rows start when it is done and reuse them, instead of
  # building the same modules at the same time
  case "$it" in print:*/PrintBool|print:*/PrintNeg|print:*/PrintStr) needs="${it%/*}/PrintX"; queued "$needs" || needs="" ;; esac
  pool_add "$it" "run_item \"$it\"" "$it" "$needs"
done
pool_rc=0
if [ -n "$explain" ]; then
  # --explain: each item's script prints its key components and runs nothing (nothing is verified or recorded)
  for it in "${queue[@]}"; do run_item "$it" || true; done
  exit 0
fi
pool_run || pool_rc=$?
broken=(${POOL_FAILED[@]+"${POOL_FAILED[@]}"})
# the report: every item RAN or was SKIPPED, with totals
. scripts/lib/incr.sh
incr_report "$pooldir" "${items[@]}"
{ [ -f "$times" ] && cat "$times"; cat "$pooldir"/*.time 2>/dev/null; } |
  awk -F'\t' '{ t[$1] = $2 } END { for (k in t) printf "%s\t%s\n", k, t[k] }' | sort > "$times.tmp" || true
mv "$times.tmp" "$times"
echo "total: ${#arm64[@]} arm64 items, ${#amd64[@]} amd64 functions, ${#asm[@]} assembly items, ${#sys[@]} kernel examples, ${#rtmisc[@]} remaining-runtime items, ${#prt[@]} print examples, ${#cgorows[@]} cgo rows, $(( $(date +%s) - wall ))s wall (-j $PAR_JOBS)${changed:+; --incremental: items with a record of an identical PASS skipped}"
if [ ${#broken[@]} -gt 0 ]; then echo "FAILED: ${broken[*]}"; exit 1; fi
echo "all ok"
