#!/usr/bin/env bash
# tamper.sh BINARY OUT SYMBOL: copy BINARY to OUT with one byte of SYMBOL's code changed, outside
# every PC-relative field (so the normalized code hash of cmd/janus/stubpin.go changes): on arm64
# bit 0 of the first word (the destination register of the prologue's `MOVD 16(R28), R16`, or of
# gcWriteBarrierN's `ORR $16, ZR, R25`), on amd64 the first 0x10 byte of the first four (the
# stack-guard displacement `CMPQ SP, 0x10(R14)`, or gcWriteBarrierN's `MOVL $0x10, R11`) XOR 8.
set -euo pipefail
bin=$1 out=$2 sym=$3
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
J="${JANUS_AUDIT_BIN:-$root/bin/janus}"
addr=$("$J" list "$bin" --filter "$sym" | awk -v s="$sym" '$3 == s {print $1}')
[ -n "$addr" ] || { echo "tamper: no function $sym in $bin" >&2; exit 1; }
cp "$bin" "$out"
python3 -I - "$out" "$addr" <<'PY'
import struct, sys
path, addr = sys.argv[1], int(sys.argv[2], 16)
b = bytearray(open(path, 'rb').read())
machine = struct.unpack_from('<H', b, 18)[0]
shoff, = struct.unpack_from('<Q', b, 0x28)
shentsize, shnum = struct.unpack_from('<HH', b, 0x3a)
off = None
for i in range(shnum):
    sh = shoff + i * shentsize
    stype, flags, saddr, soff, ssize = struct.unpack_from('<IQQQQ', b, sh + 4)
    if flags & 4 and saddr <= addr < saddr + ssize:   # SHF_EXECINSTR
        off = soff + addr - saddr
if off is None:
    sys.exit('tamper: address not in an executable section')
if machine == 183:          # EM_AARCH64
    b[off] ^= 1
else:                       # EM_X86_64
    k = next(k for k in range(4) if b[off + k] == 0x10)
    b[off + k] ^= 8
open(path, 'wb').write(bytes(b))
PY
