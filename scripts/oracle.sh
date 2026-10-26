#!/usr/bin/env bash
# Differential test of the Lean AArch64 model (Janus.Arm64.step) against native execution
# under qemu-aarch64. See docs/ORACLE.md.
#
#   scripts/oracle.sh selftest        build, then check the native harness on known answers
#   scripts/oracle.sh quick           ~60k generated cases
#   scripts/oracle.sh full            generated + harvested from real Go arm64 binaries (default)
#   scripts/oracle.sh fp              scalar floating point only: generated fp.* classes (FP_K
#                                     states per word) + harvested fp.* words (FP_HARVEST_K states)
#   scripts/oracle.sh neon            Advanced SIMD: the targeted neon.*/vls.struct/vls.np classes,
#                                     the SIMD&FP words of the C harvest corpus (oracle/harvest/neon,
#                                     gcc/clang -O0/-O2/-O3, NEON_K states each) and of the Go
#                                     harvest, random simd/vls group words, and SEQ straight-line
#                                     blocks (sequence mode, oracle/cmd/neonseq)
#   scripts/oracle.sh crypto          crypto extension / CRC32 / permutes only: generated classes
#                                     (CRYPTO_CLASSES), harvested words of the crypto test binaries
#                                     (CRYPTO_HARVEST_K states each) and sequence-mode blocks
#                                     (oracle seqgen: SEQ_N per family, SEQ_WINDOWS real windows)
#
# Environment: OUT (default artifacts/oracle), JOBS (default nproc), N (words per generated
# class, default 4000 for full / 1500 for quick), K (states per harvested word, default 3),
# PER_CLASS (harvested distinct words per class, default 8000), SEED (default 1), FP_K (states
# per generated fp.* word, default 4), FP_HARVEST_K (states per harvested fp.* word in fp mode, 40),
# QEMU (default /usr/bin/qemu-aarch64; set QEMU= to run natively on an arm64 Linux host),
# EXCL_SEQ (generated exclusive-monitor blocks, default 5·N), EXCL_LOOPS_K (states per harvested
# LL/SC retry loop, default 8).
# KEEP: what the run leaves in OUT (scripts/lib/artifacts.sh). Default: summary.md, repro.*,
# mismatches.jsonl (MISMATCH verdicts, if any) and cases/hw/model/verdicts.jsonl zstd-compressed
# (.zst); gen.jsonl and harvest.jsonl (whose union is cases.jsonl) are removed. KEEP=zst
# compresses every dump, KEEP=1 keeps them all raw.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
# shellcheck source=lib/artifacts.sh
. "$root/scripts/lib/artifacts.sh"
memguard_self "$@"
mode="${1:-full}"
export PATH="$PATH:/usr/local/go/bin"
OUT="${OUT:-$root/artifacts/oracle}"
JOBS="${JOBS:-$(nproc)}"
SEED="${SEED:-1}"
K="${K:-3}"
PER_CLASS="${PER_CLASS:-8000}"
QEMU="${QEMU-/usr/bin/qemu-aarch64}"
bin="$root/oracle/bin"

echo "== build"
(cd "$root/oracle" &&
  CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -o "$bin/runner" ./cmd/runner &&
  go build -o "$bin/oracle" ./cmd/oracle)
(cd "$root" && memguard_lake build janus-oracle janus-decode)
common=(-qemu "$QEMU" -runner "$bin/runner")
# DCZID_EL0 is IMPLEMENTATION DEFINED: every case carries the reference CPU's own value (the
# Lean side uses it as State.dczid; the runner refuses a case with a different one).
DCZID="$(GODEBUG=asyncpreemptoff=1 ${QEMU:+"$QEMU"} "$bin/runner" -dczid)"
echo "== reference DCZID_EL0 = $DCZID"

echo "== harness self-test"
"$bin/oracle" selftest "${common[@]}" -dczid "$DCZID" > "$bin/selftest.log" || { cat "$bin/selftest.log"; exit 1; }
tail -1 "$bin/selftest.log"
[ "$mode" = selftest ] && exit 0

mkdir -p "$OUT"
# However the run ends: keep the summaries, compressed verdicts and corpus, drop the other dumps
# (KEEP=1 keeps everything raw; scripts/lib/artifacts.sh).
trap 'art_prune "$OUT"' EXIT
cases=()
case "$mode" in
  quick) N="${N:-1500}" ;;
  full)  N="${N:-4000}" ;;
  fp)    N="${N:-20000}" ;;
  neon)  N="${N:-20000}" ;;
  crypto) N="${N:-20000}" ;;
  *) echo "usage: $0 selftest|quick|full|fp|neon|crypto" >&2; exit 2 ;;
esac
FP_K="${FP_K:-4}"
echo "== generate ($N words per class)"
# The crypto-extension / CRC32 / permute classes and their AdvSIMD neighbours (gen/crypto.go).
CRYPTO_CLASSES="${CRYPTO_CLASSES:-^(crypto\.|simd\.(pmull|permute|dupscalar|aes|ext|tbl)$|dpr\.crc32$)}"
if [ "$mode" = fp ]; then
  "$bin/oracle" gen -dczid "$DCZID" -n "$N" -only '^fp\.' -fp-k "$FP_K" -seed "$SEED" -o "$OUT/gen.jsonl"
elif [ "$mode" = neon ]; then
  "$bin/oracle" gen -dczid "$DCZID" -n "$N" -only '^(neon|vls\.(struct|np))' -group "$N" -seed "$SEED" -o "$OUT/gen.jsonl"
  echo "== harvest the C corpus (oracle/harvest/neon)"
  ccdir="$(mktemp -d -p /var/tmp janus-neon-cc.XXXXXX)"
  bash "$root/oracle/harvest/neon/build.sh" "$ccdir" > /dev/null
  "$bin/oracle" harvest -dczid "$DCZID" -k "${NEON_K:-20}" -per-class 0 -only '^(simd|vls|fp)' -seed "$((SEED + 2))" \
    -first-id 20000000 -o "$OUT/harvest-c.jsonl" "$ccdir"/*/*.o
  rm -rf "$ccdir"
  cases+=("$OUT/harvest-c.jsonl")
  echo "== sequence mode (${SEQ:-50000} blocks)"
  (cd "$root/oracle" && go build -o "$bin/neonseq" ./cmd/neonseq)
  "$bin/neonseq" -n "${SEQ:-50000}" -seed "$SEED" -dczid "$DCZID" -decode "$root/.lake/build/bin/janus-decode" -o "$OUT/seq.jsonl"
  cases+=("$OUT/seq.jsonl")
elif [ "$mode" = crypto ]; then
  "$bin/oracle" gen -dczid "$DCZID" -n "$N" -only "$CRYPTO_CLASSES" -seed "$SEED" -o "$OUT/gen.jsonl"
else
  # gen/seq.excl: exclusive-monitor blocks in sequence mode (EXCL_SEQ, default 5 per class word)
  "$bin/oracle" gen -dczid "$DCZID" -n "$N" -group "$((N * 2))" -excl-seq "${EXCL_SEQ:-$((N * 5))}" -seed "$SEED" -o "$OUT/gen.jsonl"
fi
cases+=("$OUT/gen.jsonl")

if [ "$mode" = full ] || [ "$mode" = fp ] || [ "$mode" = neon ] || [ "$mode" = crypto ]; then
  echo "== harvest corpus (real Go arm64 code)"
  corpus="$bin/corpus"
  mkdir -p "$corpus"
  # The crypto packages bring the SHA-1/SHA-256/SHA-512/SHA-3, AES-GCM (PMULL), CRC32 and
  # chacha20 (ZIP, via crypto/tls) assembly kernels.
  (cd "$root/oracle" &&
    CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -o "$corpus/bigprog" ./harvest/bigprog &&
    for p in math math/big strconv sort crypto/sha256 bytes strings sync/atomic sync runtime \
        crypto/sha1 crypto/sha512 crypto/sha3 crypto/cipher hash/crc32 crypto/tls; do
      CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go test -c -o "$corpus/${p//\//_}.test" "$p"
    done)
  # gcc-compiled C (the cgo examples and the model-coverage corpus examples/cgo/ccover.c)
  if command -v aarch64-linux-gnu-gcc >/dev/null; then
    printf 'int main(void){return 0;}\n' > "$corpus/cmain.c"
    aarch64-linux-gnu-gcc -g -O2 -o "$corpus/ccover-c" "$root/examples/cgo/ccover.c" \
      "$root/examples/cgo/cfuncs.c" "$corpus/cmain.c" -I"$root/examples/cgo"
    rm -f "$corpus/cmain.c"
  fi
  extra=()
  for f in "$root"/artifacts/*-arm64; do [ -f "$f" ] && extra+=("$f"); done
  hargs=()
  [ "$mode" = fp ] && hargs=(-only '^fp\.' -per-class 0 -fp-k "${FP_HARVEST_K:-40}")
  [ "$mode" = neon ] && hargs=(-only '^(simd|vls)\.' -per-class 0)
  [ "$mode" = crypto ] && hargs=(-only "$CRYPTO_CLASSES" -per-class 0)
  # harvest/seq.excl: the binaries' LL/SC retry loops (full mode)
  [ "$mode" = full ] && hargs=(-excl-loops "${EXCL_LOOPS_K:-8}")
  hk="$K"
  [ "$mode" = crypto ] && hk="${CRYPTO_HARVEST_K:-40}"
  "$bin/oracle" harvest -dczid "$DCZID" -k "$hk" -per-class "$PER_CLASS" "${hargs[@]}" -seed "$((SEED + 1))" -o "$OUT/harvest.jsonl" "$corpus"/* "${extra[@]}"
  cases+=("$OUT/harvest.jsonl")
fi
if [ "$mode" = full ] || [ "$mode" = crypto ]; then
  # Sequence mode: straight-line blocks (synthetic chains per family + windows of the real
  # crypto kernels), executed in one go natively and word by word by janus-oracle.
  echo "== sequences"
  sn="${SEQ_N:-500}"; swin="${SEQ_WINDOWS:-2000}"
  [ "$mode" = crypto ] && { sn="${SEQ_N:-10000}"; swin="${SEQ_WINDOWS:-20000}"; }
  "$bin/oracle" seqgen -dczid "$DCZID" -n "$sn" -windows "$swin" -seed "$((SEED + 2))" -o "$OUT/seq.jsonl" "$corpus"/*
  cases+=("$OUT/seq.jsonl")
fi

echo "== run (native under ${QEMU:-native} vs janus-oracle)"
IFS=, eval 'list="${cases[*]}"'
"$bin/oracle" run "${common[@]}" -model "$root/.lake/build/bin/janus-oracle" -j "$JOBS" -cases "$list" -out "$OUT" > /dev/null
mismatch=0
if grep -q '"verdict":"MISMATCH"' "$OUT/verdicts.jsonl"; then
  mismatch=1
  echo "== minimize mismatches"
  "$bin/oracle" minimize "${common[@]}" -model "$root/.lake/build/bin/janus-oracle" -out "$OUT" -max 200 > /dev/null
  echo "minimal reproductions: $OUT/repro.md"
fi
sed -n '1,6p' "$OUT/summary.md"
echo "report: $OUT/summary.md  (per-case verdicts: $OUT/verdicts.jsonl, zstd-compressed unless KEEP=1)"
if [ "$mismatch" = 1 ]; then
  echo "FAIL: model disagrees with hardware (see $OUT/repro.md)" >&2
  exit 1
fi
