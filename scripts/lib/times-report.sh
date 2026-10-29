#!/usr/bin/env bash
# times-report.sh FILE: summarize a JANUS_TIMES_FILE (scripts/lib/parallel.sh): blocks by wall time,
# and the gaps between section marks. Usage: JANUS_TIMES_FILE=/path audit/run-rounds.sh r7; scripts/lib/times-report.sh /path
sort -n "$1" | awk -F'\t' '
  $4 ~ /^block:/ { printf "%8.0fs block  %s %s\n", $2-$1, $3, substr($4,8) > "/dev/stderr"; next }
  { if (prev != "") printf "%8.0fs section %s -> %s\n", $1-pt, prev, substr($4,7); prev=substr($4,7); pt=$1 }' 2>&1 | sort -rn | head -${2:-40}
