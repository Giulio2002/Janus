#!/usr/bin/env bash
# The differential test of the C ABI classification (Janus/CABI/AAPCS64.lean, Janus/CABI/SysV.lean)
# against the real compilers: gcc and clang, -O0 and -O2, arm64 (aarch64-linux-gnu-gcc,
# clang --target=aarch64-linux-gnu, run under qemu-aarch64) and amd64. See
# scripts/cabiprobe/main.go for what is checked (argument and result locations, AL, layout,
# va_list states and va_arg) and docs/FFI.md §1 for the results.
#
# Usage: scripts/cabi-probe.sh [cabiprobe flags]   e.g. -random 400 -seed 7 -configs amd64/gcc/O2
# Writes artifacts/cabi-probe/summary.txt and mismatches.txt; exit status 1 on any mismatch.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH

for tool in gcc clang aarch64-linux-gnu-gcc qemu-aarch64; do
  command -v "$tool" >/dev/null || { echo "cabi-probe: $tool not found" >&2; exit 2; }
done

lake build Janus >/dev/null
(cd scripts/cabiprobe && go build -o "$root/bin/cabiprobe" .)
bin/cabiprobe -root "$root" -out "$root/artifacts/cabi-probe" "$@"
