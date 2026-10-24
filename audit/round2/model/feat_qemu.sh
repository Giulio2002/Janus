#!/usr/bin/env bash
# Run feat.S under several qemu CPU models: shows that LDADDAL/LDAPR are UNDEFINED (SIGILL,
# exit 132) on Armv8.0 cores, that unaligned LDAR faults (SIGBUS, 135) without FEAT_LSE2, and
# that DCZID_EL0 differs between CPU models (exit code of 'z').
set -euo pipefail
d="$(cd "$(dirname "$0")" && pwd)"; tmp=$(mktemp -d)
aarch64-linux-gnu-as "$d/feat.S" -o "$tmp/feat.o" && aarch64-linux-gnu-ld "$tmp/feat.o" -o "$tmp/feat"
for cpu in cortex-a53 cortex-a72 neoverse-n1 max; do
  line="$cpu:"
  for t in a r e z u; do
    set +e; qemu-aarch64 -cpu $cpu "$tmp/feat" $t 2>/dev/null; rc=$?; set -e
    line="$line $t=$rc"
  done
  echo "$line"
done
# Observed (qemu 10.2.1): cortex-a53: a=132 r=132 e=0 z=4 u=135 | cortex-a72: same |
# neoverse-n1: a=0 r=0 e=0 z=4 u=135 | max: a=0 r=0 e=0 z=7 u=0
