#!/usr/bin/env bash
# Verify every arm64 example proof (with the WrongAdd demonstration), every amd64 example
# theorem and the Go assembly (ABI0) examples of both ISAs in one pool of parallel jobs:
# scripts/verify-examples.sh, scripts/verify-amd64-examples.sh and
# scripts/verify-asm-examples.sh one item at a time, longest first, so that the long ClearWords
# proof overlaps the rest instead of ending one suite before the other starts.
# Usage: scripts/verify-all-examples.sh [-j N]   (-j and its memory-bounded default:
#        scripts/lib/parallel.sh). Exits non-zero if any item fails.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
par_init "$@"

go build -o bin/janus ./cmd/janus
scripts/build-examples.sh >/dev/null
bash scripts/build-examples-amd64.sh >/dev/null 2>&1
scripts/build-examples-asm.sh >/dev/null
[ -n "${JANUS_ROOT:-}" ] && (cd "$JANUS_ROOT" && lake build Janus >/dev/null)
export JANUS_EXAMPLES_PREBUILT=1

# Longest first (measured), then the rest in the scripts' order.
arm64=(MallocFast ClearWords A64IndexByte CopyBlock AddLimbs A64Equal64 Add Max Add128 Mul64 Add256 Div Get AddThree
       Sum SetOne256 HexDigit CopyWords SumSquares AtomicAdd AtomicMax HashWith HashTwice MapSum DeferAdd
       AddF64 Dot3 F64ToU64 Abs NewPair MakeSlice AppendOne SetNext
       Lookup Insert InsertGet Delete SumValues CountKeys LookupKey16 NewMap ClearMap MapAccess1Small
       Box AsHasher Classify Equal PanicIf DeferInc IndexAt LoadField
       ReverseArray RowsWith SwapBig DotBoth Find2D Fact Compose Shifts AlignUp TotalMeters TotalFeet
       Slice3 Slice2 Sum3 Triangle GotoSum Log2 SumBelow IterSum DivMod10 BitMerge MinMax ClearArray
       Mod IncTwice Bump GlobalTable Table MakeAdder
       WrongAdd)
amd64=()
for d in examples/proofs-amd64/*/; do amd64+=("$(basename "$d")"); done
asm=()
for f in examples/asm/proofs/*/*.lean; do asm+=("$(basename "$(dirname "$f")")/$(basename "$f" .lean)"); done
tmp="$(mktemp -d)"
broken=()
wall=$(date +%s)
for n in "${arm64[@]}"; do
  par_run 'JANUS_EXAMPLES_SUMMARY="$tmp/arm64-$n" scripts/verify-examples.sh -j 1 "$n" >/dev/null 2>&1 || broken+=("arm64:$n")
  cat "$tmp/arm64-$n" 2>/dev/null | grep -v "^total" | sed "s/^/arm64  /"'
done
for f in "${amd64[@]}"; do
  par_run 'out="$(scripts/verify-amd64-examples.sh -j 1 "$f" 2>&1)" || broken+=("amd64:$f")
  grep -E "Proof\.(correctness|panics|Witness)" <<<"$out" | sed "s/^/amd64  /"'
done
for t in "${asm[@]}"; do
  par_run 'JANUS_EXAMPLES_SUMMARY="$tmp/asm-${t//\//_}" scripts/verify-asm-examples.sh -j 1 "$t" >/dev/null 2>&1 || broken+=("asm:$t")
  cat "$tmp/asm-${t//\//_}" 2>/dev/null | sed "s/^/asm    /"'
done
par_wait
rm -rf "$tmp"
echo "total: ${#arm64[@]} arm64 items, ${#amd64[@]} amd64 functions, ${#asm[@]} assembly items, $(( $(date +%s) - wall ))s wall (-j $PAR_JOBS)"
if [ ${#broken[@]} -gt 0 ]; then echo "FAILED: ${broken[*]}"; exit 1; fi
echo "all ok"
