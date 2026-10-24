#!/usr/bin/env bash
# Row SPEC-TF (docs/AUDIT-FP.md): Janus.Float.add/mul/fma/truncInt against SoftFloat 3e vectors.
# Usage: audit/rt-fp/spec-testfloat.sh [MAX_VECTORS_PER_RUN]   (needs /srv/janus-fp-deps, scripts/testfloat.sh)
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TG="${DEPS:-/srv/janus-fp-deps}/tf-8086-SSE/testfloat_gen"
MAX="${1:-60000}"
[ -x "$TG" ] || { echo "skip: no $TG (run scripts/testfloat.sh once)"; exit 0; }
cd "$root" || exit 1
fail=0; tot=0
run() { # FN ROUNDING
  local out
  out="$("$TG" -r"$2" "$1" 2>/dev/null | head -n "$MAX" | lake env lean --run audit/rt-fp/SpecTestFloat.lean "$1" "$2")" || fail=1
  echo "$out" | tail -1
  tot=$((tot + $(echo "$out" | tail -1 | awk '{print $4}')))
  echo "$out" | grep MISMATCH | head -3
}
for f in f32 f64; do
  for op in add mul mulAdd; do
    for rm in near_even minMag min max near_maxMag; do run "${f}_$op" "$rm"; done
  done
  for i in i32 i64 ui32 ui64; do run "${f}_to_$i" minMag; done
done
echo "spec-testfloat: $tot vectors, $([ $fail = 0 ] && echo 0 mismatches || echo MISMATCHES)"
exit $fail
