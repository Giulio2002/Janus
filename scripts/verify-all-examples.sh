#!/usr/bin/env bash
# Verify every arm64 example proof (with the WrongAdd demonstration), every amd64 example
# theorem and the Go assembly (ABI0) examples of both ISAs in one pool of parallel jobs:
# scripts/verify-examples.sh, scripts/verify-amd64-examples.sh and
# scripts/verify-asm-examples.sh one item at a time, longest first (by the times measured in the
# last run, artifacts/verify-all-examples.times; a built-in order before the first run), so that
# the long proofs overlap the rest instead of ending the run alone.
# Usage: scripts/verify-all-examples.sh [-j N] [--changed]
#   -j N        jobs at once (default and memory admission: scripts/lib/parallel.sh).
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
par_init "$@"
changed=""
for a in ${PAR_ARGS[@]+"${PAR_ARGS[@]}"}; do
  case "$a" in
    --changed) changed=1 ;;
    *) echo "usage: scripts/verify-all-examples.sh [-j N] [--changed]" >&2; exit 2 ;;
  esac
done

go build -o bin/janus ./cmd/janus
scripts/build-examples.sh >/dev/null
bash scripts/build-examples-amd64.sh >/dev/null 2>&1
scripts/build-examples-asm.sh >/dev/null
scripts/build-examples-sys.sh >/dev/null 2>&1
[ -n "${JANUS_ROOT:-}" ] && (cd "$JANUS_ROOT" && lake build Janus >/dev/null)
export JANUS_EXAMPLES_PREBUILT=1

# The built-in order (longest first, measured), then the rest in the scripts' order.
arm64=(MallocFast ClearWords A64IndexByte A64Crc32 A64CountByte CopyBlock AddLimbs A64Equal64 Add Max Add128 Mul64 Add256 Div Get AddThree
       Sum SetOne256 HexDigit CopyWords SumSquares AtomicAdd AtomicMax HashWith HashTwice MapSum DeferAdd
       AddF64 Dot3 F64ToU64 Abs NewPair MakeSlice AppendOne SetNext
       Lookup Insert InsertGet Delete SumValues CountKeys LookupKey16 NewMap ClearMap MapAccess1Small
       LookupS InsertS DeleteS LookupK24 InsertK24 Has32 Set32 InsertPtr LookupPtr MakeHint
       ReverseArray RowsWith SwapBig DotBoth Find2D Fact Compose Shifts AlignUp TotalMeters TotalFeet
       Slice3 Slice2 Sum3 Triangle GotoSum Log2 SumBelow IterSum DivMod10 BitMerge MinMax ClearArray
       Mod IncTwice Bump GlobalTable Table MakeAdder
       SpanSum MinStr I64ToF64 F64ToI64 U64ToF64 F64ToF32 F32ToF64 LoadThird MinF64 MaxF64
       Box AsHasher Classify Equal Eq32 StrEq F64Eq CopyTrees ClearTrees LookupStr HashFKey EqFKey
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

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
broken=()
wall=$(date +%s)

# Longest first by the last run's times; an item without a time (new) goes first.
times="$root/artifacts/verify-all-examples.times"
if [ -f "$times" ]; then
  declare -A secs=()
  while IFS=$'\t' read -r k v; do secs[$k]=$v; done < "$times"
  mapfile -t items < <(i=0; for it in "${items[@]}"; do printf '%s\t%s\t%s\n' "${secs[$it]:-99999}" "$i" "$it"; i=$((i + 1)); done |
    sort -t$'\t' -k1,1gr -k2,2n | cut -f3)
fi

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
# item_done ITEM HASH SECONDS: record a passing (or skipped) item for the manifest and the times.
item_done() {
  local f="${1//\//_}"
  [ -n "$2" ] && printf '%s\t%s\n' "$1" "$2" > "$tmp/pass-$f"
  [ -n "${3:-}" ] && printf '%s\t%s\n' "$1" "$3" > "$tmp/time-$f"
  return 0
}
. scripts/example-contracts.sh
declare -A asm_sym=(
  [AddAsm]=example.com/asm.AddAsm.abi0 [XorSlice]=example.com/asm.XorSlice.abi0
  [Twice]=example.com/asm.Twice.abi0 [CallXor]=example.com/asm.CallXor
  [XorWrapper]=example.com/asm.XorSlice
)

# run_item ITEM: one block of the pool.
run_item() {
  local it=$1 kind=${1%%:*} n=${1#*:} h="" s secs out isa an
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
      s=$(date +%s.%N)
      if JANUS_EXAMPLES_SUMMARY="$tmp/arm64-$n" scripts/verify-examples.sh -j 1 "$n" >/dev/null 2>&1; then
        secs=$(echo "$(date +%s.%N) - $s" | bc)
        [ "$n" = WrongAdd ] || h="$(item_hash "$it" "artifacts/$n" "examples/proofs/$n.lean" ${xa[@]+"${xa[@]}"} || true)"
        item_done "$it" "$h" "$secs"
      else
        broken+=("$it")
      fi
      { grep -v "^total" "$tmp/arm64-$n" 2>/dev/null || true; } | sed "s/^/arm64  /"
      [ "$n" != WrongAdd ] || printf 'arm64  WrongAdd  (%.1fs)\n' "${secs:-0}"
      ;;
    amd64)
      h="$(item_hash "$it" "artifacts/amd64/$n" "examples/proofs-amd64/$n/Proof.lean" || true)"
      if item_skip "$it" "$h"; then
        printf 'amd64  %-12s skipped (unchanged since its last passing run; --changed)\n' "$n"; item_done "$it" "$h"; return 0
      fi
      s=$(date +%s.%N)
      if out="$(scripts/verify-amd64-examples.sh -j 1 "$n" 2>&1)"; then
        secs=$(echo "$(date +%s.%N) - $s" | bc)
        item_done "$it" "$h" "$secs"
      else
        broken+=("$it")
      fi
      { grep -E "Proof\.(correctness|panics|exact|outOfRange|faults|Witness|corollary)" <<<"$out" || true; } | sed "s/^/amd64  /"
      [ -z "${secs:-}" ] || printf 'amd64  %-12s (%.1fs)\n' "$n" "$secs"
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
      s=$(date +%s.%N)
      if JANUS_EXAMPLES_SUMMARY="$tmp/asm-${n//\//_}" scripts/verify-asm-examples.sh -j 1 "$n" >/dev/null 2>&1; then
        secs=$(echo "$(date +%s.%N) - $s" | bc)
        item_done "$it" "$(item_hash "$it" "artifacts/asm/$n" "examples/asm/proofs/$n.lean" || true)" "$secs"
      else
        broken+=("$it")
      fi
      sed "s/^/asm    /" "$tmp/asm-${n//\//_}" 2>/dev/null || true
      ;;
  esac
  return 0
}

for it in "${items[@]}"; do
  par_run 'run_item "$it"'
done
# the kernel examples (examples/sys, scripts/verify-sys-examples.sh), both ISAs
sys=()
for isa in arm64 amd64; do for n in WriteOut NowNano Pid MustNonNeg; do sys+=("$isa/$n"); done; done
for t in "${sys[@]}"; do
  par_run 'JANUS_EXAMPLES_SUMMARY="$tmp/sys-${t/\//-}" scripts/verify-sys-examples.sh "$t" >/dev/null 2>&1 || broken+=("sys:$t")
  cat "$tmp/sys-${t/\//-}" 2>/dev/null | sed "s/^/sys    /"'
done
par_wait
# The manifest: every item that passed (or was skipped as unchanged) in this run; the times of
# the items that ran (the others keep their last time).
cat "$tmp"/pass-* 2>/dev/null | sort > "$manifest.tmp" || true
mv "$manifest.tmp" "$manifest"
{ [ -f "$times" ] && cat "$times"; cat "$tmp"/time-* 2>/dev/null; } |
  awk -F'\t' '{ t[$1] = $2 } END { for (k in t) printf "%s\t%s\n", k, t[k] }' | sort > "$times.tmp" || true
mv "$times.tmp" "$times"
echo "total: ${#arm64[@]} arm64 items, ${#amd64[@]} amd64 functions, ${#asm[@]} assembly items, ${#sys[@]} kernel examples, $(( $(date +%s) - wall ))s wall (-j $PAR_JOBS)${changed:+; --changed: unchanged items skipped, not a gate run}"
if [ ${#broken[@]} -gt 0 ]; then echo "FAILED: ${broken[*]}"; exit 1; fi
echo "all ok"
