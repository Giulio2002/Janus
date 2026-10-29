#!/usr/bin/env bash
# Self-test of scripts/lib/rounds-lanes.sh (lane-count selection and the longest-first order).
set -u
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
. "$here/rounds-lanes.sh"
fail=0
t() { # t EXPECT CORES LOAD MEM_GIB
  local got; got="$(rounds_lane_count "$2" "$3" $(( $4 * 1024 * 1024 )))"
  if [ "$got" != "$1" ]; then echo "FAIL: lanes($2 cores, load $3, $4 GiB) = $got, want $1"; fail=1; else echo "ok: lanes($2 cores, load $3, $4 GiB) = $got"; fi
}
t 5 48 5 200      # (48-5)/8 = 5 lanes by cores; (200-40)/15 = 10 by memory
t 6 48 0 400      # capped at 6
t 2 48 45 400     # load >= 40: fall back to 2
t 2 48 5 120      # MemAvailable <= 120 GiB: 2
t 2 48 5 100
t 3 48 24 200     # (48-24)/8 = 3
t 2 8 0 200       # few cores: at least 2
t 2 48 5 50       # little memory
# order: the long lanes first, every lane once
o="$(rounds_longest_first)"
set -- $o
[ "$1 $2" = "r7c r7j" ] && echo "ok: r7c r7j first" || { echo "FAIL: order starts '$1 $2'"; fail=1; }
[ "$(printf '%s\n' $o | sort | uniq -d | wc -l)" = 0 ] && echo "ok: no lane twice" || { echo "FAIL: a lane twice"; fail=1; }
for l in r2 r3 r4 r5 r6 r7 r7c r7j r8 r9 r10 r11 r12 rfw all; do
  case " $o " in *" $l "*) ;; *) echo "FAIL: lane $l missing from the order"; fail=1 ;; esac
done
[ "$fail" = 0 ] && echo "rounds-lanes self-test: all ok" || exit 1
