#!/usr/bin/env bash
# Decoder strictness sweep over the classes added on arm64cov2 (SIMD&FP data processing,
# SIMD&FP loads/stores) plus exclusive/ordered/CAS, LSE atomics and system words: every word
# the Janus decoder accepts must be a valid instruction per GNU objdump (binutils 2.46).
# Usage (from the root of a COPY of the arm64cov2 tree, after `lake build Janus janus-decode`):
#   audit/round2/model/sweep_vs_objdump.sh [N] [SEED]
# Result on accb078, N=1500000 SEED=11: model-ok 365909, model-ok-but-objdump-invalid 0.
set -euo pipefail
d="$(cd "$(dirname "$0")" && pwd)"; root="$d/../../.."
N=${1:-1500000}; SEED=${2:-11}
tmp=$(mktemp -d)
python3 -I "$d/sweep_gen.py" "$N" "$SEED" > "$tmp/words.txt"
"$root/.lake/build/bin/janus-decode" < "$tmp/words.txt" > "$tmp/decoded.txt"
python3 -I "$d/sweep_objcmp.py" "$tmp/decoded.txt"
