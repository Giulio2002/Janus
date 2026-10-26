#!/usr/bin/env bash
# Differential test of the Lean x86-64 model (Janus.Amd64.step) against native execution on
# the x86-64 host (single-stepped, see oracle-amd64/cmd/runner). See docs/ORACLE-AMD64.md.
#
#   scripts/oracle-amd64.sh selftest   build, then check the native harness on known answers
#   scripts/oracle-amd64.sh quick      generated cases only (~100k)
#   scripts/oracle-amd64.sh full       generated + harvested from real Go amd64 binaries (default)
#   scripts/oracle-amd64.sh fp         SSE floating point only: the FP specs and edge families
#                                      plus every FP instruction harvested from the math,
#                                      strconv and sort test binaries (K states each, FPK MXCSR
#                                      settings per state; FP_K states per harvested FP
#                                      instruction, default 20)
#   scripts/oracle-amd64.sh v3         the GOAMD64=v3 extensions only (BMI1/BMI2, MOVBE, scalar
#                                      FMA, PSHUFB/PSIGNB): their specs and the FMA edge family,
#                                      plus every such instruction harvested from GOAMD64=v3 test
#                                      binaries (V3_K states each, default 12)
#   scripts/oracle-amd64.sh x87        the x87 FPU and the C-specific encodings (WP-J): every
#                                      escape-opcode form (N per memory form, N/4 per register
#                                      form) with random x87 states, NOTRACK branches and the
#                                      padded TLS call, plus every x87 instruction harvested from
#                                      gcc/clang -O0/-O2/-O3 long double code (X87_K states each,
#                                      default 40)
#   scripts/oracle-amd64.sh sse        the SSE packed instructions of WP-D only (SSE2 integer and
#                                      FP, SSE3, SSSE3, SSE4.1, SSE4.2): their specs and edge
#                                      families, plus every such instruction harvested from the std
#                                      test binaries with SSE assembly and from the C corpus compiled
#                                      by gcc and clang at -O2/-O3 (SSE_K states each, default 12)
#   scripts/oracle-amd64.sh crypto     the x86 crypto extensions of WP-E only (AES-NI, PCLMULQDQ,
#                                      SHA-NI, ADX): their specs and edge families, plus every such
#                                      instruction harvested from the std test binaries with crypto
#                                      assembly (CRYPTO_K states each, default 12)
#   scripts/oracle-amd64.sh avx512     the AVX-512 instructions of WP-G only (EVEX with ZMM0-31 and
#                                      K0-K7, the VEX opmask instructions, VPCLMULQDQ, GFNI): the
#                                      targeted specs, an EVEX opcode sweep and every distinct
#                                      EVEX/opmask encoding of the scan/crc32/runtime test binaries
#                                      (EVEX_K states each, default 24; SWEEP, default 4)
#   scripts/oracle-amd64.sh avx        the AVX/AVX2/FMA3 instructions of WP-F only (VEX-128/256 on
#                                      YMM): their specs and edge families, plus every such
#                                      instruction harvested from GOAMD64=v3 std test binaries with
#                                      AVX2 assembly and from the C corpus compiled by gcc and clang
#                                      at -O2/-O3 -march=x86-64-v3 (AVX_K states each, default 12)
#
# Environment: OUT (default artifacts/oracle-amd64), JOBS (default 16, at most 24), N
# (encodings per targeted spec, default 600 full / 250 quick), GROUP (random byte strings,
# default 40000 full / 15000 quick), K (states per harvested instruction, default 3),
# PER_CLASS (harvested distinct instructions per modeled class, default 4000), SEED (default 1),
# FPK (MXCSR settings per FP state, default 3 gen / 2 harvest),
# MODEL (default .lake/build/bin/janus-oracle-amd64; e.g. MODEL=oracle-amd64/bin/fakemodel
# to exercise the pipeline without the Lean model).
# KEEP: what the run leaves in OUT (scripts/lib/artifacts.sh). Default: summary.md, repro.*,
# mismatches.jsonl (MISMATCH verdicts, if any) and cases/hw/model/verdicts.jsonl zstd-compressed
# (.zst); gen.jsonl and harvest.jsonl (whose union is cases.jsonl) are removed. KEEP=zst
# compresses every dump, KEEP=1 keeps them all raw.
set -euo pipefail
# Example binaries (and so every address a proof depends on) are built with exactly this Go
# release, whatever Go is installed; the go command downloads it on first use.
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
# shellcheck source=lib/artifacts.sh
. "$root/scripts/lib/artifacts.sh"
memguard_self "$@"
mode="${1:-full}"
export PATH="$PATH:/usr/local/go/bin"
OUT="${OUT:-$root/artifacts/oracle-amd64}"
JOBS="${JOBS:-16}"
[ "$JOBS" -gt 24 ] && JOBS=24
SEED="${SEED:-1}"
K="${K:-3}"
PER_CLASS="${PER_CLASS:-4000}"
MODEL="${MODEL:-$root/.lake/build/bin/janus-oracle-amd64}"
bin="$root/oracle-amd64/bin"

echo "== build"
(cd "$root/oracle-amd64" &&
  CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -buildmode=pie -o "$bin/runner" ./cmd/runner &&
  CGO_ENABLED=0 go build -o "$bin/oracle" ./cmd/oracle &&
  go build -o "$bin/fakemodel" ./cmd/fakemodel)
if [ "$MODEL" = "$root/.lake/build/bin/janus-oracle-amd64" ]; then
  (cd "$root" && memguard_lake build janus-oracle-amd64)
fi

echo "== harness self-test"
"$bin/oracle" selftest -runner "$bin/runner" > "$bin/selftest.log" || { cat "$bin/selftest.log"; exit 1; }
tail -1 "$bin/selftest.log"
[ "$mode" = selftest ] && exit 0

mkdir -p "$OUT"
# However the run ends: keep the summaries, compressed verdicts and corpus, drop the other dumps
# (KEEP=1 keeps everything raw; scripts/lib/artifacts.sh).
trap 'art_prune "$OUT"' EXIT
cases=()
case "$mode" in
  quick) N="${N:-250}"; GROUP="${GROUP:-15000}" ;;
  full)  N="${N:-600}"; GROUP="${GROUP:-40000}" ;;
  fp)    N="${N:-600}"; GROUP=0 ;;
  v3)    N="${N:-600}"; GROUP=0 ;;
  x87)   N="${N:-600}"; GROUP=0 ;;
  sse)   N="${N:-600}"; GROUP=0 ;;
  crypto) N="${N:-600}"; GROUP=0 ;;
  avx)   N="${N:-600}"; GROUP=0 ;;
  avx512) N="${N:-300}"; GROUP=0 ;;
  *) echo "usage: $0 selftest|quick|full|fp|v3|x87|sse|crypto|avx|avx512" >&2; exit 2 ;;
esac
fpk=()
[ -n "${FPK:-}" ] && fpk=(-fpk "$FPK")
v3re='^(andn|blsr|blsmsk|blsi|bextr|bzhi|shlx|shrx|sarx|rorx|mulx|pdep|pext|movbe|pshufb|psignb|vfn?m(add|sub)(132|213|231)s[sd])$'
v3pkgs="math math/big strconv internal/strconv internal/runtime/maps encoding/binary math/bits reflect internal/abi math/rand runtime"
cryptopkgs="runtime crypto/aes crypto/cipher crypto/sha256 crypto/sha1 math/big crypto/internal/fips140/bigmod crypto/internal/fips140/aes/gcm crypto/rsa"
avx512pkgs="internal/runtime/gc/scan hash/crc32 runtime"
avxpkgs="crypto/sha256 crypto/sha1 crypto/sha512 crypto/tls bytes strings math internal/bytealg"
ssepkgs="internal/chacha8rand hash/crc32 bytes strings crypto/internal/fips140/nistec crypto/aes crypto/sha256 crypto/sha1 crypto/cipher math"
if [ "$mode" = fp ]; then
  echo "== generate (SSE floating point: $N encodings per spec, $((N / 2)) edge rounds)"
  "$bin/oracle" gen -fp-only -n "$N" -seed "$SEED" "${fpk[@]}" -o "$OUT/gen.jsonl"
elif [ "$mode" = x87 ]; then
  echo "== generate (x87 and CET/TLS encodings: $N per memory form, $((N / 4)) per register form)"
  "$bin/oracle" gen -x87-only -n "$N" -seed "$SEED" -o "$OUT/gen.jsonl"
elif [ "$mode" = v3 ]; then
  echo "== generate (GOAMD64=v3 extensions: $N encodings per spec, $((N / 4)) FMA edge rounds)"
  "$bin/oracle" gen -v3-only -n "$N" -seed "$SEED" "${fpk[@]}" -o "$OUT/gen.jsonl"
elif [ "$mode" = sse ]; then
  echo "== generate (SSE packed, WP-D: $N encodings per spec, $((N / 4)) edge rounds)"
  "$bin/oracle" gen -sse-only -n "$N" -seed "$SEED" "${fpk[@]}" -o "$OUT/gen.jsonl"
elif [ "$mode" = crypto ]; then
  echo "== generate (x86 crypto extensions, WP-E: $N encodings per spec, $((N / 2)) edge rounds)"
  "$bin/oracle" gen -crypto-only -n "$N" -seed "$SEED" "${fpk[@]}" -o "$OUT/gen.jsonl"
elif [ "$mode" = avx512 ]; then
  echo "== harvest the WP-G (AVX-512, opmask, VPCLMULQDQ, GFNI) instructions of the std test binaries"
  corpus="$bin/corpus-avx512"
  mkdir -p "$corpus"
  (cd "$root/oracle-amd64" &&
    for p in $avx512pkgs; do
      CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v1 go test -c -o "$corpus/${p//\//_}.test" "$p"
    done)
  # x86asm does not know EVEX: GNU objdump lists the instructions (one per line, all bytes)
  for f in "$corpus"/*.test; do
    objdump -d --insn-width=15 --no-addresses "$f"
  done | awk -F'\t' 'NF >= 3 { b = $2; gsub(/ /, "", b); split($3, m, " ");
      if (b ~ /^62/ || m[1] ~ /^k(mov|and|or|xor|xnor|not|shift|test|ortest|add|unpck)/ || m[1] ~ /^vpclmul|^vgf2p8/)
        print b "\t" m[1] }' | sort -u > "$OUT/evex-harvest.txt"
  echo "$(wc -l < "$OUT/evex-harvest.txt") distinct encodings"
  echo "== generate (AVX-512, WP-G: $N encodings per spec, EVEX opcode sweep ${SWEEP:-4} each, ${EVEX_K:-24} states per harvested encoding)"
  "$bin/oracle" gen -avx512-only -n "$N" -sweep "${SWEEP:-4}" -evex-harvest "$OUT/evex-harvest.txt" \
    -evex-k "${EVEX_K:-24}" -seed "$SEED" -o "$OUT/gen.jsonl"
elif [ "$mode" = avx ]; then
  echo "== generate (AVX/AVX2/FMA3, WP-F: $N encodings per spec, $((N / 4)) edge rounds)"
  "$bin/oracle" gen -avx-only -n "$N" -seed "$SEED" "${fpk[@]}" -o "$OUT/gen.jsonl"
else
  echo "== generate ($N encodings per targeted spec, $GROUP random)"
  "$bin/oracle" gen -n "$N" -group "$GROUP" -seed "$SEED" "${fpk[@]}" -o "$OUT/gen.jsonl"
fi
cases+=("$OUT/gen.jsonl")

if [ "$mode" = fp ]; then
  echo "== harvest the FP instructions of the math, strconv and sort test binaries"
  corpus="$bin/corpus-fp"
  mkdir -p "$corpus"
  (cd "$root/oracle-amd64" &&
    for p in math strconv sort; do
      CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v1 go test -c -o "$corpus/${p//\//_}.test" "$p"
    done)
  fpre='^(addsd|subsd|mulsd|divsd|sqrtsd|minsd|maxsd|addss|subss|mulss|divss|sqrtss|minss|maxss|u?comis[sd]|cvt.*|roundsd|roundss|cmpsd_xmm|cmpss|andn?p[sd]|orp[sd]|xorp[sd])$'
  "$bin/oracle" harvest -k "${FP_K:-20}" -per-class 0 -only "$fpre" -seed "$((SEED + 1))" "${fpk[@]}" -o "$OUT/harvest.jsonl" "$corpus"/*
  cases+=("$OUT/harvest.jsonl")
fi

if [ "$mode" = v3 ]; then
  echo "== harvest the v3-extension instructions of GOAMD64=v3 test binaries"
  corpus="$bin/corpus-v3"
  mkdir -p "$corpus"
  (cd "$root/oracle-amd64" &&
    for p in $v3pkgs; do
      CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v3 go test -c -o "$corpus/${p//\//_}.test" "$p"
    done)
  "$bin/oracle" harvest -k "${V3_K:-12}" -per-class 0 -only "$v3re" -seed "$((SEED + 1))" "${fpk[@]}" -o "$OUT/harvest.jsonl" "$corpus"/*
  cases+=("$OUT/harvest.jsonl")
fi

if [ "$mode" = x87 ]; then
  echo "== harvest the x87 instructions of gcc/clang long double code"
  corpus="$bin/corpus-x87"
  mkdir -p "$corpus"
  for cc in gcc clang; do
    command -v "$cc" >/dev/null || continue
    for opt in -O0 -O2 -O3 "-O2 -march=x86-64-v3"; do
      tag="$cc${opt// /}"
      for src in "$root/oracle-amd64/harvest/x87/ld.c" "$root/scripts/coverage/ccorpus/abi.c"; do
        # shellcheck disable=SC2086
        $cc $opt -fPIC -pthread -c -o "$corpus/$(basename "$src" .c)-$tag.o" "$src"
      done
    done
  done
  "$bin/oracle" harvest -k "${X87_K:-40}" -per-class 0 -only '^(f[a-z0-9]*|jmp|call)$' -seed "$((SEED + 1))" \
    -o "$OUT/harvest.jsonl" "$corpus"/*.o
  cases+=("$OUT/harvest.jsonl")
fi

if [ "$mode" = sse ]; then
  echo "== harvest the WP-D instructions of std test binaries and of gcc/clang-compiled C"
  corpus="$bin/corpus-sse"
  mkdir -p "$corpus"
  (cd "$root/oracle-amd64" &&
    for p in $ssepkgs; do
      CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v1 go test -c -o "$corpus/${p//\//_}.test" "$p"
    done)
  for cc in gcc clang; do
    command -v "$cc" >/dev/null || continue
    for o in -O2 -O3; do
      for f in "$root"/scripts/coverage/ccorpus/*.c "$root"/examples/cgo/ccover.c; do
        "$cc" $o -c -fPIC -g -I"$root/examples/cgo" -o "$corpus/c-$cc$o-$(basename "$f" .c).o" "$f"
      done
    done
  done
  ssere="$("$bin/oracle" classes -sse)"
  "$bin/oracle" harvest -k "${SSE_K:-12}" -per-class 0 -only "$ssere" -seed "$((SEED + 1))" "${fpk[@]}" -o "$OUT/harvest.jsonl" "$corpus"/*
  cases+=("$OUT/harvest.jsonl")
fi

if [ "$mode" = crypto ]; then
  echo "== harvest the WP-E instructions of std test binaries"
  corpus="$bin/corpus-crypto"
  mkdir -p "$corpus"
  (cd "$root/oracle-amd64" &&
    for p in $cryptopkgs; do
      CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v1 go test -c -o "$corpus/${p//\//_}.test" "$p"
    done)
  cryptore="$("$bin/oracle" classes -crypto)"
  "$bin/oracle" harvest -k "${CRYPTO_K:-12}" -per-class 0 -only "$cryptore" -seed "$((SEED + 1))" "${fpk[@]}" -o "$OUT/harvest.jsonl" "$corpus"/*
  cases+=("$OUT/harvest.jsonl")
fi

if [ "$mode" = avx ]; then
  echo "== harvest the WP-F instructions of GOAMD64=v3 std test binaries and of gcc/clang -march=x86-64-v3 C"
  corpus="$bin/corpus-avx"
  mkdir -p "$corpus"
  (cd "$root/oracle-amd64" &&
    for p in $avxpkgs; do
      CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v3 go test -c -o "$corpus/${p//\//_}.test" "$p"
    done)
  for cc in gcc clang; do
    command -v "$cc" >/dev/null || continue
    for o in -O2 -O3; do
      for f in "$root"/scripts/coverage/ccorpus/*.c "$root"/examples/cgo/ccover.c "$root"/examples/cgo/vec/*.c; do
        "$cc" $o -march=x86-64-v3 -c -fPIC -g -I"$root/examples/cgo" -I"$root/examples/cgo/vec" \
          -o "$corpus/c-$cc$o-$(basename "$f" .c).o" "$f"
      done
    done
  done
  avxre="$("$bin/oracle" classes -avx)"
  "$bin/oracle" harvest -k "${AVX_K:-12}" -per-class 0 -only "$avxre" -seed "$((SEED + 1))" "${fpk[@]}" -o "$OUT/harvest.jsonl" "$corpus"/*
  cases+=("$OUT/harvest.jsonl")
fi

if [ "$mode" = full ]; then
  echo "== harvest corpus (real Go amd64 code)"
  corpus="$bin/corpus"
  mkdir -p "$corpus"
  (cd "$root/oracle-amd64" &&
    CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v1 go build -o "$corpus/bigprog" ./harvest/bigprog &&
    for p in math math/big strconv sort crypto/sha256 bytes strings math/bits encoding/binary sync/atomic; do
      CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v1 go test -c -o "$corpus/${p//\//_}.test" "$p"
    done
    # GOAMD64=v3 code (BMI1/BMI2, MOVBE, FMA, PSHUFB/PSIGNB)
    for p in math strconv internal/runtime/maps encoding/binary; do
      CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v3 go test -c -o "$corpus/v3_${p//\//_}.test" "$p"
    done)
  # gcc-compiled C (the cgo examples and the model-coverage corpus examples/cgo/ccover.c)
  if command -v gcc >/dev/null; then
    printf 'int main(void){return 0;}\n' > "$corpus/cmain.c"
    gcc -g -O2 -o "$corpus/ccover-c" "$root/examples/cgo/ccover.c" "$root/examples/cgo/cfuncs.c" \
      "$corpus/cmain.c" -I"$root/examples/cgo"
    rm -f "$corpus/cmain.c"
  fi
  if [ ! -f "$root/artifacts/examples-amd64" ]; then
    (cd "$root/examples/basic" && CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -trimpath -o "$root/artifacts/examples-amd64" ./cmd)
  fi
  "$bin/oracle" harvest -k "$K" -per-class "$PER_CLASS" -seed "$((SEED + 1))" "${fpk[@]}" -o "$OUT/harvest.jsonl" \
    "$corpus"/* "$root/artifacts/examples-amd64"
  cases+=("$OUT/harvest.jsonl")
fi

echo "== run (native vs $(basename "$MODEL"))"
IFS=, eval 'list="${cases[*]}"'
"$bin/oracle" run -runner "$bin/runner" -model "$MODEL" -j "$JOBS" -cases "$list" -out "$OUT" > /dev/null
mismatch=0
if grep -q '"verdict":"MISMATCH"' "$OUT/verdicts.jsonl"; then
  mismatch=1
  echo "== minimize mismatches"
  "$bin/oracle" minimize -runner "$bin/runner" -model "$MODEL" -out "$OUT" -max 200 > /dev/null
  echo "minimal reproductions: $OUT/repro.md"
fi
sed -n '1,6p' "$OUT/summary.md"
echo "report: $OUT/summary.md  (per-case verdicts: $OUT/verdicts.jsonl, zstd-compressed unless KEEP=1)"
if [ "$mismatch" = 1 ]; then
  echo "FAIL: model disagrees with hardware (see $OUT/repro.md)" >&2
  exit 1
fi
