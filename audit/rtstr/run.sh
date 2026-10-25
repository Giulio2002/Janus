#!/usr/bin/env bash
# audit/rtstr: the string, slice and write-barrier contracts (R1, R5) against the real Go 1.26
# runtime. Builds audit/rtstr/probe for amd64 (native) and arm64 (qemu-aarch64), then
#  * checks every string example against Go's own builtins on random inputs (both ISAs);
#  * prints the capacities the runtime chooses (growslice for 24-byte elements, []byte(s)) and has
#    Lean check them against the specs' formulas (growCap, roundupsize) by `decide` (both ISAs);
#  * under gdb (amd64), evaluates the write-barrier readiness HRoom at real gcWriteBarrier2 calls.
# Exits non-zero on any failure. Needs go1.26.0 (GOTOOLCHAIN), qemu-aarch64, gdb.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
export PATH="$PATH:/usr/local/go/bin"
T="$(mktemp -d)"; trap 'rm -rf "$T"' EXIT
fail=0
check() { if [ "$2" = 0 ]; then echo "  ok    $1: $3"; else echo "  FAIL  $1: $3"; fail=1; fi; }
( cd audit/rtstr/probe && export GOTOOLCHAIN=go1.26.0 CGO_ENABLED=0 &&
  GOARCH=amd64 GOAMD64=v1 go build -trimpath -o "$T/p-amd64" . &&
  GOARCH=arm64 go build -trimpath -o "$T/p-arm64" . ) || { echo "probe build failed"; exit 1; }
for isa in amd64 arm64; do
  run="$T/p-$isa"; [ $isa = arm64 ] && run="qemu-aarch64 $T/p-arm64"
  o="$($run strings 20000)"; grep -q 'mismatches=0$' <<<"$o"; check "strings-$isa" $? "$o"
  { echo "import Janus"; echo "open Janus.Contracts"; echo "set_option maxRecDepth 100000"
    $run vectors; } > "$T/vec-$isa.lean"
  lake env lean "$T/vec-$isa.lean" > "$T/vec-$isa.log" 2>&1
  check "capacities-$isa" $? "growCap 24 true (l+1) l for l ≤ 1200, roundupsize k true for k ≤ 3000 ($(grep -c error "$T/vec-$isa.log") errors)"
done
o="$(gdb -batch -x audit/rtstr/wb_amd64.py --args "$T/p-amd64" wb 200000 2>&1 | grep '^PROBE')"
r="$(sed -E 's/.*calls=([0-9]+) room=([0-9]+) hroom=([0-9]+).*/\1 \2 \3/' <<<"$o")"
set -- $r
[ "${1:-0}" -gt 0 ] && [ "${3:-0}" -gt 0 ] && [ "${2:-0}" = "${3:-x}" ]
check "wb-hroom-amd64" $? "$o (HRoom holds at every call with room; the rest are buffer flushes)"
exit $fail
