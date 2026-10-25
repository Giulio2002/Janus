#!/usr/bin/env bash
# Verify every arm64 example proof (with the WrongAdd demonstration) and every amd64 example
# theorem in one pool of parallel jobs: scripts/verify-examples.sh and
# scripts/verify-amd64-examples.sh one item at a time, longest first, so that the long ClearWords
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
[ -n "${JANUS_ROOT:-}" ] && (cd "$JANUS_ROOT" && lake build Janus >/dev/null)
export JANUS_EXAMPLES_PREBUILT=1

# Longest first (measured), then the rest in the scripts' order.
arm64=(MallocFast ClearWords A64IndexByte CopyBlock AddLimbs A64Equal64 Add Max Add128 Mul64 Add256 Div Get AddThree
       Sum SetOne256 HexDigit CopyWords SumSquares AtomicAdd AtomicMax HashWith HashTwice MapSum DeferAdd
       AddF64 Dot3 F64ToU64 Abs NewPair MakeSlice AppendOne SetNext
       Lookup Insert InsertGet Delete SumValues CountKeys LookupKey16 NewMap ClearMap MapAccess1Small
       Box AsHasher Classify Equal WrongAdd)
amd64=()
for d in examples/proofs-amd64/*/; do amd64+=("$(basename "$d")"); done
tmp="$(mktemp -d)"
broken=()
wall=$(date +%s)
for n in "${arm64[@]}"; do
  par_run 'JANUS_EXAMPLES_SUMMARY="$tmp/arm64-$n" scripts/verify-examples.sh -j 1 "$n" >/dev/null 2>&1 || broken+=("arm64:$n")
  cat "$tmp/arm64-$n" 2>/dev/null | grep -v "^total" | sed "s/^/arm64  /"'
done
for f in "${amd64[@]}"; do
  par_run 'out="$(scripts/verify-amd64-examples.sh -j 1 "$f" 2>&1)" || broken+=("amd64:$f")
  grep -E "Proof\.(correctness|panics)" <<<"$out" | sed "s/^/amd64  /"'
done
par_wait
rm -rf "$tmp"
echo "total: ${#arm64[@]} arm64 items, ${#amd64[@]} amd64 functions, $(( $(date +%s) - wall ))s wall (-j $PAR_JOBS)"
if [ ${#broken[@]} -gt 0 ]; then echo "FAILED: ${broken[*]}"; exit 1; fi
echo "all ok"
