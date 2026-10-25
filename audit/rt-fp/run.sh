#!/usr/bin/env bash
# Red-team round FP (docs/AUDIT-FP.md): the floating-point models, decoders, specifications and
# example theorems. Writes only to a mktemp directory (and the Go/Lake build caches).
#
#   audit/rt-fp/run.sh                 every row
#   RT_FP_SKIP_SAIL=1 ...              skip A64-SAIL (needs oracle-sail/target/release/janus-oracle-sail,
#                                      built by `scripts/oracle-sail.sh build`, about 30 min once)
#   RT_FP_SKIP_SPEC=1 ...              skip SPEC-TF (about 4 min, needs /srv/janus-fp-deps)
#   JOBS=N                             oracle parallelism (default: by MemAvailable, at most 16)
#
# Every row prints its result; a row whose result contradicts its expectation is marked BROKEN
# and the script exits 1.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=../../scripts/lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
here="$root/audit/rt-fp"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
W="$(mktemp -d "${TMPDIR:-/tmp}/rt-fp.XXXXXX")"
trap 'rm -rf "$W"' EXIT
# Oracle jobs: about 1 GiB each; keep 40 GiB for the host.
JOBS="${JOBS:-$(memguard_jobs 1G 16)}"

broken=()
row() { # row NAME EXPECT RESULT  (RESULT must start with EXPECT)
  local mark=""
  case "$3" in "$2"*) ;; *) mark="   <-- BROKEN"; broken+=("$1") ;; esac
  printf '%-30s %-8s %s%s\n' "$1" "$2" "$3" "$mark"
}
mismatches() { local n; n=$(grep -c '"verdict":"MISMATCH"' "$1/verdicts.jsonl" 2>/dev/null); echo "${n:-0}"; }
summary() { sed -n 's/^\*\*\([0-9]*\) MISMATCH\*\*.*; \([0-9]*\) agree; \([0-9]*\) model-gap.*/\1 MISMATCH, \2 agree, \3 gap/p' "$1/summary.md"; }

echo "== build (Lean model executables, oracle harnesses, generators)"
memguard_lake build janus-oracle janus-oracle-amd64 janus-decode >"$W/lake.log" 2>&1 ||
  { tail -20 "$W/lake.log"; exit 1; }
(cd oracle && CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -o "$W/a64/runner" ./cmd/runner &&
  go build -o "$W/a64/oracle" ./cmd/oracle) || exit 1
(cd oracle-amd64 && CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -buildmode=pie -o "$W/x64/runner" ./cmd/runner &&
  CGO_ENABLED=0 go build -o "$W/x64/oracle" ./cmd/oracle) || exit 1
(cd "$here/gen-a64" && go build -o "$W/gena64" .) || exit 1
(cd "$here/gen-x64" && go build -o "$W/genx64" .) || exit 1
go build -o "$W/janus" ./cmd/janus || exit 1

echo "== A64-*: targeted arm64 corpus (FMA family, FPCR grids, FCVT/FCVTZ*/SCVTF/FRINT boundaries) vs qemu"
"$W/gena64" -o "$W/a64.jsonl" 2>"$W/gena64.log"
"$W/a64/oracle" run -qemu /usr/bin/qemu-aarch64 -runner "$W/a64/runner" -model .lake/build/bin/janus-oracle \
  -j "$JOBS" -cases "$W/a64.jsonl" -out "$W/out-a64" >/dev/null 2>&1
n=$(mismatches "$W/out-a64")
if [ "$n" = 0 ] && [ -s "$W/out-a64/summary.md" ]; then
  row "A64-QEMU (469k cases)" ok "ok ($(summary "$W/out-a64"))"
else
  row "A64-QEMU (469k cases)" ok "FAILED: $n mismatches ($W/out-a64/summary.md)"
  sed -n '/## Mismatches/,$p' "$W/out-a64/summary.md" | head -20
fi

sail="$root/oracle-sail/target/release/janus-oracle-sail"
if [ -n "${RT_FP_SKIP_SAIL:-}" ] || [ ! -x "$sail" ]; then
  row "A64-SAIL" skip "skip (no $sail or RT_FP_SKIP_SAIL)"
else
  echo "== A64-SAIL: the same corpus on the Sail ASL model, three-way"
  # KEEP=1: the rows below read the raw verdicts (W is removed on exit anyway).
  KEEP=1 QEMU_OUT="$W/out-a64" OUT="$W/out-sail" JOBS="$JOBS" scripts/oracle-sail.sh run >"$W/sail.log" 2>&1
  js=$(mismatches "$W/out-sail/janus-vs-sail"); qs=$(mismatches "$W/out-sail/qemu-vs-sail")
  if [ -s "$W/out-sail/janus-vs-sail/summary.md" ] && [ "$js" = 0 ] && [ "$qs" = 0 ]; then
    row "A64-SAIL (Janus/qemu vs Sail)" ok "ok (Janus vs Sail: $(summary "$W/out-sail/janus-vs-sail"); qemu vs Sail: $qs MISMATCH)"
  else
    row "A64-SAIL (Janus/qemu vs Sail)" ok "FAILED: Janus-vs-Sail $js, qemu-vs-Sail $qs mismatches ($(tail -3 "$W/sail.log" | tr '\n' ' '))"
  fi
fi

echo "== X64-*: targeted SSE corpus (grids x all 64 mask subsets, CMPSD, COMIS, conversions, ROUNDSD, prefixes) vs host"
"$W/genx64" -o "$W/x64.jsonl" 2>"$W/genx64.log"
"$W/x64/oracle" selftest -runner "$W/x64/runner" >"$W/x64-selftest.log" 2>&1 || { tail -5 "$W/x64-selftest.log"; exit 1; }
"$W/x64/oracle" run -runner "$W/x64/runner" -model .lake/build/bin/janus-oracle-amd64 -j "$JOBS" \
  -cases "$W/x64.jsonl" -out "$W/out-x64" >/dev/null 2>&1
n=$(mismatches "$W/out-x64")
if [ "$n" = 0 ] && [ -s "$W/out-x64/summary.md" ]; then
  row "X64-HOST (446k cases)" ok "ok ($(summary "$W/out-x64"))"
  # DEC-X64: the prefix sweep is the rtfp.x.prefix class of the same run
  p=$(grep -c '"class":"rtfp.x.prefix"' "$W/x64.jsonl")
  row "DEC-X64 (prefix/REX sweep)" ok "ok ($p cases in X64-HOST, 0 MISMATCH)"
else
  row "X64-HOST (446k cases)" ok "FAILED: $n mismatches ($W/out-x64/summary.md)"
fi

echo "== DEC-A64: the decoder on 2.9M words of the FP and Advanced SIMD space vs GNU objdump"
python3 -I "$here/decode/words.py" "$W/w.bin" "$W/w.hex"
.lake/build/bin/janus-decode < "$W/w.hex" > "$W/w.lean"
aarch64-linux-gnu-objdump -D -b binary -m aarch64 "$W/w.bin" | tail -n +8 > "$W/w.objd"
if out=$(python3 -I "$here/decode/compare.py" "$W/w.lean" "$W/w.objd"); then
  row "DEC-A64 (2,949,120 words)" ok "ok ($(grep -o 'disagreements: [0-9]*' <<<"$out"); $(grep -c ' ok ' "$W/w.lean") accepted)"
else
  row "DEC-A64 (2,949,120 words)" ok "FAILED: $(grep -m3 BAD <<<"$out" | tr '\n' ' ')"
fi

if [ -n "${RT_FP_SKIP_SPEC:-}" ]; then
  row "SPEC-TF" skip "skip (RT_FP_SKIP_SPEC)"
else
  echo "== SPEC-TF: Janus.Float.add/mul/fma/truncInt against SoftFloat 3e"
  if out=$("$here/spec-testfloat.sh" 2>&1); then
    row "SPEC-TF (spec vs SoftFloat)" ok "ok ($(tail -1 <<<"$out" | sed 's/^spec-testfloat: //'))"
  else
    row "SPEC-TF (spec vs SoftFloat)" ok "FAILED: $(grep -m3 MISMATCH <<<"$out" | tr '\n' ' ')"
  fi
fi

echo "== X64-MXCSR-STICKY: what MXCSR a Go program's calls actually see"
(cd "$here/probe/mxcsr" && CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v1 go build -o "$W/mxcsr" . &&
  CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -o "$W/mxcsr-arm64" .) || exit 1
hw=$("$W/mxcsr" 0.1 0.2)
v=$(sed -n 's/^main-entry=\(0x[0-9a-f]*\) .*/\1/p' <<<"$hw")
cat > "$W/GoMx.lean" <<EOF
import Janus
open Janus.Amd64
example : GoABI.GoMXCSR { (default : State) with mxcsr := $v } := by unfold GoABI.GoMXCSR; decide
example : ¬ ({ (default : State) with mxcsr := $v }.mxcsr = 0x1F80) := by decide
EOF
if [ "$v" = 0x1f80 ]; then
  row "X64-MXCSR-STICKY hw" ok "UNEXPECTED: main sees $v (flags clear)"
elif lake env lean "$W/GoMx.lean" >"$W/gomx.log" 2>&1; then
  row "X64-MXCSR-STICKY hw" ok "ok (main sees MXCSR=$v: flags set, so s.mxcsr = 0x1F80 excludes it; GoMXCSR accepts it)"
else
  row "X64-MXCSR-STICKY hw" ok "FAILED: GoMXCSR rejects $v: $(head -3 "$W/gomx.log" | tr '\n' ' ')"
fi
lit=$(grep -l 's\.mxcsr = 0x1F80' examples/proofs-amd64/*/Proof.lean 2>/dev/null | tr '\n' ' ')
if [ -n "$lit" ]; then
  row "X64-MXCSR-STICKY proofs" ok "BROKEN: precondition s.mxcsr = 0x1F80 in $lit"
else
  st=""
  for f in AddF64 Dot3 F64ToU64; do
    rm -rf "$W/ex-$f"; cp -r "artifacts/amd64/$f" "$W/ex-$f" 2>/dev/null ||
      { st="$st $f:not-extracted(run scripts/build-examples-amd64.sh)"; continue; }
    if out=$("$W/janus" verify "$W/ex-$f" --proof "examples/proofs-amd64/$f/Proof.lean" --theorem Proof.correctness --binary artifacts/examples-amd64 2>&1) &&
        grep -q 'GoABI.GoMXCSR s' <<<"$out"; then st="$st $f:ok"; else st="$st $f:FAILED"; fi
  done
  case "$st" in *FAILED*|*not-extracted*) row "X64-MXCSR-STICKY proofs" ok "FAILED:$st" ;;
    *) row "X64-MXCSR-STICKY proofs" ok "ok (verified with GoMXCSR in the statement:$st)" ;; esac
fi
hw=$(qemu-aarch64 "$W/mxcsr-arm64" 0.1 0.2)
case "$hw" in
  "main-entry=0x0 "*) row "A64-FPCR-REAL" ok "ok (main sees FPCR=0, FPSR flags set: s.fpcr = 0 is realistic, FPSR is left free) [$hw]" ;;
  *) row "A64-FPCR-REAL" ok "UNEXPECTED: $hw" ;;
esac

echo "== X64-V3-FMA: GOAMD64=v3 fuses Dot3 differently; the v1 theorem must not carry over"
(cd examples/basic && CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v3 go build -trimpath -buildvcs=false -o "$W/ex-v3" ./cmd) || exit 1
if go tool objdump -s 'basic\.Dot3$' "$W/ex-v3" | grep -q 'c4e2e1b9'; then
  "$W/janus" extract "$W/ex-v3" example.com/basic.Dot3 "$W/dot3-v3" >/dev/null 2>&1
  if out=$("$W/janus" verify "$W/dot3-v3" --proof examples/proofs-amd64/Dot3/Proof.lean --theorem Proof.correctness 2>&1); then
    row "X64-V3-FMA" blocked "VERIFIED against the fused v3 binary"
  elif grep -q 'janus64_run: stuck at .*vfmadd231sd' <<<"$out"; then
    # since WP-B the decoder models scalar FMA; the v1 proof (unfused MULSD/ADDSD) gets stuck at
    # the first VFMADD231SD, whose fused result it does not account for
    row "X64-V3-FMA" blocked "blocked (v3 Dot3 = MULSD + 2x VFMADD231SD; the v1 proof fails on it: it gets stuck at the fused VFMADD231SD)"
  else
    row "X64-V3-FMA" blocked "FAILED oddly: $(tail -3 <<<"$out" | tr '\n' ' ')"
  fi
else
  row "X64-V3-FMA" blocked "UNEXPECTED: no VFMADD231SD in the v3 Dot3"
fi

echo "== DOC: statements of the FP rows"
if grep -q 'exact `FPToFixed` for every `FPCR` without trap enables' README.md &&
    ! grep -q 'and Go never changes them' docs/SOUNDNESS.md &&
    grep -q 'calls the `MXCSR` status bits callee-save' docs/SOUNDNESS.md; then
  row "DOC-FP (README/SOUNDNESS)" ok "ok (trap-enable condition stated; MXCSR flags documented as sticky, not in ABIReturn)"
else
  row "DOC-FP (README/SOUNDNESS)" ok "BROKEN: README/SOUNDNESS still overstate the FP theorems"
fi

echo
if [ ${#broken[@]} -eq 0 ]; then echo "rt-fp: every row as expected"; exit 0; fi
echo "rt-fp: BROKEN rows: ${broken[*]}"; exit 1
