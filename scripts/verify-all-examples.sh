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
# Usage: scripts/verify-all-examples.sh [-j N] [--changed] [--cgo]
#   -j N        jobs at once (default and memory admission: scripts/lib/parallel.sh).
#   --cgo       also verify the cgo rows (examples/proofs-cgo) in the same queue.
#   --filter ERE   development only: queue just the items whose id ("arm64:Add", "cgo:amd64/CAdd", ...)
#               matches the regular expression; not a gate run.
#   --changed   development mode, NOT a gate run: skip every item whose inputs are byte-identical
#               to those of its last passing run in this checkout (artifacts/verify-all-examples.manifest):
#               its extraction (Extracted.lean, identity.json), its proof file, its extraction
#               arguments, the framework sources and the Lean toolchain. The janus executable is
#               deliberately not an input, so a change to the verifier itself (cmd/janus) is not
#               re-checked on unchanged items: CI and the merge gate run without --changed.
# Every item prints its time. Exits non-zero if any item fails. A run (with or without
# --changed) records the inputs of every item that passed or was skipped in the manifest.
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
cgo=""
filter=""
args=(${PAR_ARGS[@]+"${PAR_ARGS[@]}"})
for ((i = 0; i < ${#args[@]}; i++)); do
  case "${args[$i]}" in
    --changed) changed=1 ;;
    --cgo) cgo=1 ;;
    --filter) i=$((i + 1)); filter="${args[$i]:?--filter needs a regular expression}" ;;
    *) echo "usage: scripts/verify-all-examples.sh [-j N] [--changed] [--cgo] [--filter ERE]" >&2; exit 2 ;;
  esac
done

# JANUS_EXAMPLES_PREBUILT=1 (scripts/gate.sh): bin/janus, the examples' binaries and the framework
# build exist already (built once by the gate); nothing is rebuilt.
if [ "${JANUS_EXAMPLES_PREBUILT:-}" != 1 ]; then
  go build -o bin/janus ./cmd/janus
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

# The inputs of an item (--changed and the manifest): a SHA-256 over the framework sources, the
# toolchain, the item's proof file, its extraction arguments and its extraction (Extracted.lean and
# identity.json without the "binary" path, which only says where the extraction lives).
manifest="$root/artifacts/verify-all-examples.manifest"
global="$( { find Janus -type f -name '*.lean' -print0 | sort -z | xargs -0 sha256sum
             sha256sum Janus.lean lakefile.toml lake-manifest.json lean-toolchain; } | sha256sum | cut -d' ' -f1)"
item_hash() { # ITEM ART_DIR PROOF_FILE [EXTRACTION ARGS...]
  local item=$1 art=$2 proof=$3; shift 3
  [ -f "$art/Extracted.lean" ] && [ -f "$art/identity.json" ] || return 1
  { echo "$global $item"; sha256sum < "$proof"; printf '%s\n' "$@"; cat "$art/Extracted.lean"
    grep -v '^  "binary": ' "$art/identity.json"; } | sha256sum | cut -d' ' -f1
}
declare -A last=()
if [ -n "$changed" ] && [ -f "$manifest" ]; then
  while IFS=$'\t' read -r k v; do last[$k]=$v; done < "$manifest"
fi
# item_skip ITEM HASH: --changed, and the item passed with exactly these inputs.
item_skip() { [ -n "$changed" ] && [ -n "$2" ] && [ "${last[$1]:-}" = "$2" ]; }
# item_done ITEM HASH: record a passing (or skipped) item for the manifest (the pool records the walls).
item_done() {
  local f="${1//\//_}"
  [ -n "$2" ] && printf '%s\t%s\n' "$1" "$2" > "$tmp/pass-$f"
  return 0
}
. scripts/example-contracts.sh
declare -A asm_sym=(
  [AddAsm]=example.com/asm.AddAsm.abi0 [XorSlice]=example.com/asm.XorSlice.abi0
  [Twice]=example.com/asm.Twice.abi0 [CallXor]=example.com/asm.CallXor
  [XorWrapper]=example.com/asm.XorSlice
)

# run_item ITEM: one item of the pool. Everything it prints is the item's log; its exit status is
# its verdict (0: passed or skipped as unchanged).
run_item() {
  local it=$1 kind=${1%%:*} n=${1#*:} h="" rc=0 isa an
  local -a xa=()
  case "$kind" in
    arm64)
      if [ "$n" != WrongAdd ]; then
        mapfile -t xa < <(scripts/example-targets.sh "$n")
        if [ -n "$changed" ] && bin/janus extract artifacts/examples-arm64 "$(example_symbol "$n")" "$tmp/x-$n" \
             ${xa[@]+"${xa[@]}"} >/dev/null 2>&1; then
          h="$(item_hash "$it" "$tmp/x-$n" "examples/proofs/$n.lean" ${xa[@]+"${xa[@]}"} || true)"
        fi
      fi
      if item_skip "$it" "$h"; then
        printf 'arm64  %-9s skipped (unchanged since its last passing run; --changed)\n' "$n"; item_done "$it" "$h"; return 0
      fi
      JANUS_EXAMPLES_SUMMARY="$tmp/arm64-$n" scripts/verify-examples.sh -j 1 "$n" || rc=$?
      if [ $rc = 0 ]; then
        [ "$n" = WrongAdd ] || h="$(item_hash "$it" "artifacts/$n" "examples/proofs/$n.lean" ${xa[@]+"${xa[@]}"} || true)"
        item_done "$it" "$h"
      fi
      return $rc
      ;;
    amd64)
      h="$(item_hash "$it" "artifacts/amd64/$n" "examples/proofs-amd64/$n/Proof.lean" || true)"
      if item_skip "$it" "$h"; then
        printf 'amd64  %-12s skipped (unchanged since its last passing run; --changed)\n' "$n"; item_done "$it" "$h"; return 0
      fi
      scripts/verify-amd64-examples.sh -j 1 "$n" || rc=$?
      [ $rc != 0 ] || item_done "$it" "$h"
      return $rc
      ;;
    asm)
      isa="${n%%/*}"; an="${n#*/}"
      if [ -n "$changed" ] && [ -n "${asm_sym[$an]:-}" ] &&
         bin/janus extract "artifacts/examples-asm-$isa" "${asm_sym[$an]}" "$tmp/x-asm-$isa-$an" >/dev/null 2>&1; then
        h="$(item_hash "$it" "$tmp/x-asm-$isa-$an" "examples/asm/proofs/$n.lean" || true)"
      fi
      if item_skip "$it" "$h"; then
        printf 'asm    %-17s skipped (unchanged since its last passing run; --changed)\n' "$n"; item_done "$it" "$h"; return 0
      fi
      JANUS_EXAMPLES_SUMMARY="$tmp/asm-${n//\//_}" scripts/verify-asm-examples.sh -j 1 "$n" || rc=$?
      [ $rc != 0 ] || item_done "$it" "$(item_hash "$it" "artifacts/asm/$n" "examples/asm/proofs/$n.lean" || true)"
      return $rc
      ;;
    rtmisc)
      # (always run: no --changed hash for the remaining-runtime examples)
      JANUS_EXAMPLES_SUMMARY="$tmp/rtmisc-${n//\//_}" scripts/verify-rtmisc-examples.sh -j 1 "$n" || rc=$?
      return $rc
      ;;
    sys)
      JANUS_EXAMPLES_SUMMARY="$tmp/sys-${n//\//_}" scripts/verify-sys-examples.sh "$n" || rc=$?
      return $rc
      ;;
    print)
      JANUS_EXAMPLES_SUMMARY="$tmp/print-${n//\//_}" scripts/verify-print-examples.sh "$n" || rc=$?
      return $rc
      ;;
    cgo)
      JANUS_EXAMPLES_SUMMARY="$tmp/cgo-${n//\//_}" scripts/verify-cgo-examples.sh -j 1 "$n" || rc=$?
      return $rc
      ;;
  esac
  echo "run_item: unknown kind $kind"; return 2
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
pool_times "$times"
for it in "${items[@]}"; do
  needs=""
  # the first print row of an ISA builds the lemma modules every row of that ISA imports (in the shared
  # snapshot's consumer workspace); the other rows start when it is done and reuse them, instead of
  # building the same modules at the same time
  case "$it" in print:*/PrintBool|print:*/PrintNeg|print:*/PrintStr) needs="${it%/*}/PrintX"; printf '%s\n' "${items[@]}" | grep -qx "$needs" || needs="" ;; esac
  pool_add "$it" "run_item \"$it\"" "$it" "$needs"
done
pool_rc=0
pool_run || pool_rc=$?
broken=(${POOL_FAILED[@]+"${POOL_FAILED[@]}"})
# The manifest: every item that passed (or was skipped as unchanged) in this run; the times of
# the items that ran (the others keep their last time).
cat "$tmp"/pass-* 2>/dev/null | sort > "$manifest.tmp" || true
mv "$manifest.tmp" "$manifest"
{ [ -f "$times" ] && cat "$times"; cat "$pooldir"/*.time 2>/dev/null; } |
  awk -F'\t' '{ t[$1] = $2 } END { for (k in t) printf "%s\t%s\n", k, t[k] }' | sort > "$times.tmp" || true
mv "$times.tmp" "$times"
echo "total: ${#arm64[@]} arm64 items, ${#amd64[@]} amd64 functions, ${#asm[@]} assembly items, ${#sys[@]} kernel examples, ${#rtmisc[@]} remaining-runtime items, ${#prt[@]} print examples, ${#cgorows[@]} cgo rows, $(( $(date +%s) - wall ))s wall (-j $PAR_JOBS)${changed:+; --changed: unchanged items skipped, not a gate run}"
if [ ${#broken[@]} -gt 0 ]; then echo "FAILED: ${broken[*]}"; exit 1; fi
echo "all ok"
