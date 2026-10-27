#!/usr/bin/env python3
"""Round-12 ELF crafting (ELF64 little-endian, arm64 or x86-64). Usage:
  craft_elf.py MODE SRC DST PATCH_VADDR ORIG_HEX NEW_HEX [ALIGN]

Every mode starts from SRC, a Go example binary, and edits only headers or appends bytes.
  overlap     append a page with ORIG_HEX->NEW_HEX patched at PATCH_VADDR and an extra PT_LOAD
              (page-sized, p_align ALIGN, default 0x1000) mapping it over the original code.
              The loader maps it LAST, so the patched bytes execute (confirmed under qemu);
              the section headers still describe the original bytes. (round-11b O1)
  overlap-sub append the same but map only 16 bytes at PATCH_VADDR (byte-level overlap that
              does not start on a page boundary)
  secoff      advance the .text section header's sh_offset by 4 (program headers untouched)
  filesz      make the text PT_LOAD's p_filesz > p_memsz
  wx          make the text PT_LOAD writable+executable
  misalign    move the text PT_LOAD's p_vaddr by 0x10 so offset and vaddr are not congruent
"""
import os, struct, sys

def main():
    mode, src, dst, vs, orig_hex, new_hex = sys.argv[1:7]
    align = int(sys.argv[7], 0) if len(sys.argv) > 7 else 0x1000
    vaddr = int(vs, 0); orig = bytes.fromhex(orig_hex); new = bytes.fromhex(new_hex)
    d = bytearray(open(src, "rb").read())
    phoff = struct.unpack_from("<Q", d, 32)[0]; phn = struct.unpack_from("<H", d, 56)[0]
    ph = [list(struct.unpack_from("<IIQQQQQQ", d, phoff + 56 * i)) for i in range(phn)]
    # fields: type flags off vaddr paddr filesz memsz align
    cov = [i for i, p in enumerate(ph) if p[0] == 1 and p[3] <= vaddr < p[3] + p[5]]
    assert len(cov) == 1, cov
    ci = cov[0]; c = ph[ci]
    def put(i):
        struct.pack_into("<IIQQQQQQ", d, phoff + 56 * i, *ph[i])
    if mode in ("overlap", "overlap-sub"):
        pg = vaddr & ~0xFFF
        fo = c[2] + (pg - c[3])
        page = bytearray(d[fo:fo + 0x1000]); assert len(page) == 0x1000
        r = vaddr - pg
        assert bytes(page[r:r + len(orig)]) == orig, (page[r:r + len(orig)].hex(), orig.hex())
        page[r:r + len(new)] = new
        base = vaddr if mode == "overlap-sub" else pg
        size = 16 if mode == "overlap-sub" else 0x1000
        body = page[base - pg:base - pg + size]
        # place the new bytes at a file offset congruent to the vaddr modulo the alignment
        a = max(align, 0x1000)
        off = (len(d) + a - 1) // a * a + (base % a)
        d += b"\0" * (off - len(d)); d += body
        new_phoff = (len(d) + 7) // 8 * 8
        d += b"\0" * (new_phoff - len(d))
        for i in range(phn):
            d += struct.pack("<IIQQQQQQ", *ph[i])
        d += struct.pack("<IIQQQQQQ", 1, 5, off, base, base, size, size, align)
        struct.pack_into("<Q", d, 32, new_phoff); struct.pack_into("<H", d, 56, phn + 1)
    elif mode == "filesz":
        c[6] = c[5] - 16; put(ci)
    elif mode == "wx":
        c[1] |= 2; put(ci)
    elif mode == "misalign":
        c[3] += 0x10; put(ci)
    elif mode == "secoff":
        shoff = struct.unpack_from("<Q", d, 40)[0]; shn = struct.unpack_from("<H", d, 60)[0]
        shs = struct.unpack_from("<H", d, 62)[0]
        stro = struct.unpack_from("<Q", d, shoff + 64 * shs + 24)[0]
        for i in range(shn):
            o = shoff + 64 * i
            n = struct.unpack_from("<I", d, o)[0]
            if bytes(d[stro + n:stro + n + 6]) == b".text\0":
                struct.pack_into("<Q", d, o + 24, struct.unpack_from("<Q", d, o + 24)[0] + 4)
                break
        else:
            raise SystemExit("no .text")
    else:
        raise SystemExit("bad mode")
    open(dst, "wb").write(d); os.chmod(dst, 0o755)
    print(f"wrote {dst}: mode {mode}")

main()
