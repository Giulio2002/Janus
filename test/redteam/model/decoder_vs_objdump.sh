#!/usr/bin/env bash
# Every word the Janus decoder accepts must be a valid instruction per GNU objdump.
# Usage: audit/model/decoder_vs_objdump.sh [N] [SEED]   (from /srv/janus, after lake build)
set -euo pipefail
cd "$(dirname "$0")"
N=${1:-400000}; SEED=${2:-7}
python3 -I gen_words.py "$N" "$SEED" > words.txt
../../.lake/build/bin/janus-decode < words.txt > decoded.txt
python3 -I objcmp.py decoded.txt
