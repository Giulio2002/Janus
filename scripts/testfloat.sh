#!/usr/bin/env bash
# Cross-check the floating-point model (Janus/Float, Janus/Arm64/Float.lean, Janus/Amd64/Float.lean)
# against Berkeley TestFloat 3e / SoftFloat 3e: testfloat_gen writes test vectors whose
# results SoftFloat computes, and janus-testfloat (Oracle/TestFloat.lean) runs every vector
# through the model. See docs/ORACLE.md ("TestFloat").
#
#   scripts/testfloat.sh            level 1 (every function, every rounding mode)
#   LEVEL=2 N=2000000 scripts/testfloat.sh   level 2, N vectors per run
#
# SoftFloat is built three times, with the specializations that match the architectures:
# ARM-VFPv2 (Arm, FPCR.DN = 0, tininess before rounding), ARM-VFPv2-defaultNaN (FPCR.DN = 1)
# and 8086-SSE (x86 SSE, tininess after rounding). Sources go to DEPS (default
# /srv/janus-fp-deps), pinned to the 3e releases.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEPS="${DEPS:-/srv/janus-fp-deps}"
LEVEL="${LEVEL:-1}"
N="${N:-}"
SF_COMMIT=f74b1e4   # berkeley-softfloat-3 "Release 3e"
TF_COMMIT=06b2007   # berkeley-testfloat-3 "Release 3e"
out="$(realpath -m "${OUT:-$root/artifacts/testfloat}")"
mkdir -p "$DEPS"
cd "$DEPS"
[ -d berkeley-softfloat-3 ] || git clone -q https://github.com/ucb-bar/berkeley-softfloat-3.git
[ -d berkeley-testfloat-3 ] || git clone -q https://github.com/ucb-bar/berkeley-testfloat-3.git
git -C berkeley-softfloat-3 checkout -q "$SF_COMMIT"
git -C berkeley-testfloat-3 checkout -q "$TF_COMMIT"
for spec in 8086-SSE ARM-VFPv2 ARM-VFPv2-defaultNaN; do
  if [ ! -x "tf-$spec/testfloat_gen" ]; then
    rm -rf "sf-$spec" "tf-$spec"
    mkdir -p "sf-$spec" "tf-$spec"
    cp -r berkeley-softfloat-3/build/Linux-x86_64-GCC/. "sf-$spec/"
    sed -i "s|^SOURCE_DIR ?= .*|SOURCE_DIR ?= $DEPS/berkeley-softfloat-3/source|; s|^SPECIALIZE_TYPE ?= .*|SPECIALIZE_TYPE ?= $spec|" "sf-$spec/Makefile"
    make -s -C "sf-$spec" -j8 >/dev/null
    cp -r berkeley-testfloat-3/build/Linux-x86_64-GCC/. "tf-$spec/"
    sed -i "s|^SOURCE_DIR ?= .*|SOURCE_DIR ?= $DEPS/berkeley-testfloat-3/source|; s|^SOFTFLOAT_DIR ?= .*|SOFTFLOAT_DIR ?= $DEPS/berkeley-softfloat-3|; s|^SOFTFLOAT_LIB = .*|SOFTFLOAT_LIB = $DEPS/sf-$spec/softfloat\$(LIB)|" "tf-$spec/Makefile"
    make -s -C "tf-$spec" -j8 testfloat_gen >/dev/null
  fi
done
(cd "$root" && lake build janus-testfloat >/dev/null)
T="$root/.lake/build/bin/janus-testfloat"
mkdir -p "$out"
log="$out/results.txt"
rm -f "$out"/part.*
fail=0
gen_opts=(-level "$LEVEL")
[ -n "$N" ] && gen_opts+=(-n "$N")

# run ISA SPEC TININESS FUNCTION ROUNDING [exact]
# (runs JOBS checks in parallel; each writes its own part file)
JOBS="${JOBS:-16}"
k=0
run() {
  local isa=$1 spec=$2 tin=$3 fn=$4 rm=$5 ex=${6:-}
  local gex=-notexact
  [ "$ex" = exact ] && gex=-exact
  k=$((k + 1))
  while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do wait -n || true; done
  ("tf-$spec/testfloat_gen" "${gen_opts[@]}" "-tininess$tin" "$gex" "-r$rm" $fn |
      "$T" "$isa" "$fn" "$rm" $ex > "$out/part.$k" || touch "$out/part.$k.fail") &
}

modes4=(near_even minMag min max)
modes5=(near_even minMag min max near_maxMag)
for f in f32 f64; do
  for rm in "${modes4[@]}"; do
    for op in add sub mul div sqrt mulAdd; do
      run arm ARM-VFPv2 before "${f}_$op" "$rm"
      run arm-ah ARM-VFPv2 after "${f}_$op" "$rm"
    done
    for op in add mul div sqrt mulAdd; do run arm-dn ARM-VFPv2-defaultNaN before "${f}_$op" "$rm"; done
    for op in add sub mul div sqrt; do run x86 8086-SSE after "${f}_$op" "$rm"; done
    for i in i32 ui32 i64 ui64; do run arm ARM-VFPv2 before "${i}_to_$f" "$rm"; done
    for i in i32 i64; do run x86 8086-SSE after "${i}_to_$f" "$rm"; done
    for i in i32 i64; do run x86 8086-SSE after "${f}_to_$i" "$rm" exact; done
    run x86 8086-SSE after "${f}_roundToInt" "$rm"
    run x86 8086-SSE after "${f}_roundToInt" "$rm" exact
  done
  for rm in "${modes5[@]}"; do
    for i in i32 ui32 i64 ui64; do run arm ARM-VFPv2 before "${f}_to_$i" "$rm" exact; done
    run arm ARM-VFPv2 before "${f}_roundToInt" "$rm"
    run arm ARM-VFPv2 before "${f}_roundToInt" "$rm" exact
  done
  for c in eq lt le eq_signaling le_quiet lt_quiet; do
    run arm ARM-VFPv2 before "${f}_$c" near_even
    run x86 8086-SSE after "${f}_$c" near_even
  done
done
for rm in "${modes4[@]}"; do
  run arm ARM-VFPv2 before f32_to_f64 "$rm"
  run arm ARM-VFPv2 before f64_to_f32 "$rm"
  run arm-dn ARM-VFPv2-defaultNaN before f64_to_f32 "$rm"
  run x86 8086-SSE after f32_to_f64 "$rm"
  run x86 8086-SSE after f64_to_f32 "$rm"
done
wait
rm -f "$out"/part.*.fail.keep
ls "$out"/part.*.fail >/dev/null 2>&1 && fail=1
cat "$out"/part.* | grep -v '^$' > "$log" || true
rm -f "$out"/part.*
awk '/ vectors, / {v+=$(NF-10); m+=$(NF-8); k+=$(NF-3)} END {printf "TOTAL: %d vectors, %d mismatches, %d known NaN-rule differences\n", v, m, k}' "$log" | tee -a "$log"
grep MISMATCH "$log" | head -20 || true
exit $fail
