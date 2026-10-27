package main

// The loader's view of an ELF executable (docs/SOUNDNESS.md, "ELF loader semantics").
//
// Janus extracts code and data by section header, but the kernel (Linux binfmt_elf) maps the
// image by PT_LOAD program header, in table order, later mappings replacing earlier ones, and
// never looks at section headers. loaderView is the address -> file-offset map built from the
// PT_LOAD entries exactly that way; every byte the extractor copies is read through it, and
// every section used is cross-checked against it. Binaries whose PT_LOADs overlap, are
// malformed, or are writable+executable are rejected outright (neither Go's linker nor gcc/ld
// produce them), so the "later wins" resolution below never has to decide anything for an
// accepted binary: the map is a function and the two descriptions cannot diverge.

import (
	"bytes"
	"debug/elf"
	"encoding/binary"
	"fmt"
	"os"
)

// loadPageSize is the largest page size Linux can map PT_LOADs with for the ISA: 64 KiB on
// arm64 (4/16/64 KiB kernels exist), 4 KiB on x86-64 (huge pages do not apply to binfmt_elf
// PT_LOAD mappings). Overlap and offset/vaddr congruence are checked at this granularity, so two
// segments that share a page on any supported kernel are rejected.
func loadPageSize(m elf.Machine) uint64 {
	if m == elf.EM_AARCH64 {
		return 1 << 16
	}
	return 1 << 12
}

type loadSeg struct {
	Off, Vaddr, Filesz, Memsz, Flags, Align uint64
}

type loaderView struct {
	gran uint64 // loadPageSize of the ISA
	data []byte
	segs []loadSeg // PT_LOAD entries in table order
}

func elfDiag(msg, next string) *diag {
	if next == "" {
		next = "Use an unmodified executable produced by go build (or gcc/ld for cgo); the program and section headers must agree."
	}
	return &diag{Msg: msg, Stage: "binary validation", Next: next}
}

func (lv *loaderView) pageDown(x uint64) uint64 { return x &^ (lv.gran - 1) }
func (lv *loaderView) pageUp(x uint64) uint64   { return (x + lv.gran - 1) &^ (lv.gran - 1) }

// newLoaderView builds the loader map and rejects malformed PT_LOAD tables:
//
//	L1  p_filesz <= p_memsz
//	L2  the file bytes [p_offset, p_offset+p_filesz) lie inside the file; no address overflow
//	L3  p_offset ≡ p_vaddr (mod the ISA's largest page size, loadPageSize), and if p_align > 1 it is a power of two with
//	    p_offset ≡ p_vaddr (mod p_align) (the kernel maps whole pages at a file offset)
//	L4  no two PT_LOADs overlap, at loadPageSize granularity (64 KiB arm64, 4 KiB amd64) over [p_vaddr, p_vaddr+p_memsz)
//	    (the kernel maps whole pages, so a shared page is an overlap)
//	L5  no PT_LOAD is both writable and executable
//	L6  at least one PT_LOAD
func newLoaderView(f *elf.File, data []byte, path string) (*loaderView, error) {
	lv := &loaderView{data: data, gran: loadPageSize(f.Machine)}
	for i, p := range f.Progs {
		if p.Type != elf.PT_LOAD {
			continue
		}
		s := loadSeg{p.Off, p.Vaddr, p.Filesz, p.Memsz, uint64(p.Flags), p.Align}
		bad := func(why string) error {
			return elfDiag(fmt.Sprintf("%s: PT_LOAD #%d (offset 0x%x, vaddr 0x%x, filesz 0x%x, memsz 0x%x, align 0x%x) %s",
				path, i, s.Off, s.Vaddr, s.Filesz, s.Memsz, s.Align, why), "")
		}
		if s.Filesz > s.Memsz {
			return nil, bad("has p_filesz > p_memsz")
		}
		if s.Off+s.Filesz < s.Off || s.Off+s.Filesz > uint64(len(data)) {
			return nil, bad("maps file bytes beyond the end of the file")
		}
		if s.Vaddr+s.Memsz < s.Vaddr || lv.pageUp(s.Vaddr+s.Memsz) < s.Vaddr {
			return nil, bad("wraps the address space")
		}
		if s.Off%lv.gran != s.Vaddr%lv.gran {
			return nil, bad("has p_offset and p_vaddr that are not congruent modulo the page size")
		}
		if s.Align > 1 && (s.Align&(s.Align-1) != 0 || s.Off%s.Align != s.Vaddr%s.Align) {
			return nil, bad("has a p_align that is not a power of two, or p_offset % p_align != p_vaddr % p_align")
		}
		if s.Flags&uint64(elf.PF_W) != 0 && s.Flags&uint64(elf.PF_X) != 0 {
			return nil, bad("is writable and executable")
		}
		lo, hi := lv.pageDown(s.Vaddr), lv.pageUp(s.Vaddr+s.Memsz)
		for j, o := range lv.segs {
			olo, ohi := lv.pageDown(o.Vaddr), lv.pageUp(o.Vaddr+o.Memsz)
			if lo < ohi && olo < hi && s.Memsz > 0 && o.Memsz > 0 {
				return nil, bad(fmt.Sprintf("overlaps an earlier PT_LOAD (#%d, vaddr 0x%x, memsz 0x%x) at page granularity; the kernel would map the later one over the earlier, so the extracted bytes could differ from the executed ones", j, o.Vaddr, o.Memsz))
			}
		}
		lv.segs = append(lv.segs, s)
	}
	if len(lv.segs) == 0 {
		return nil, elfDiag(path+" has no PT_LOAD segment", "")
	}
	return lv, nil
}

// seg returns the PT_LOAD the loader maps addr from: the LAST one in table order whose
// [vaddr, vaddr+memsz) contains addr (binfmt_elf: later mappings replace earlier ones).
func (lv *loaderView) seg(addr uint64) (loadSeg, bool) {
	for i := len(lv.segs) - 1; i >= 0; i-- {
		s := lv.segs[i]
		if addr >= s.Vaddr && addr-s.Vaddr < s.Memsz {
			return s, true
		}
	}
	return loadSeg{}, false
}

// read returns the file-backed bytes the loader maps at [addr, addr+size): one segment must
// map all of them from its file image (p_filesz).
func (lv *loaderView) read(addr, size uint64) ([]byte, error) {
	s, ok := lv.seg(addr)
	if !ok || addr+size < addr || addr+size > s.Vaddr+s.Filesz {
		return nil, fmt.Errorf("[0x%x, 0x%x) is not file-backed by the PT_LOAD that the loader maps there", addr, addr+size)
	}
	off := s.Off + (addr - s.Vaddr)
	return append([]byte(nil), lv.data[off:off+size]...), nil
}

// sectionBytes reads the bytes of file-backed section s through the loader map and requires
// them to equal the bytes its section header points at (sh_offset).
func (lv *loaderView) sectionBytes(s *elf.Section, path string) ([]byte, error) {
	mismatch := func(why string) error {
		return elfDiag(fmt.Sprintf("section %s of %s (vaddr 0x%x, file offset 0x%x, size 0x%x) %s; the bytes the kernel maps at that address would differ from the section's bytes, so Janus would reason about code or data that does not execute",
			s.Name, path, s.Addr, s.Offset, s.Size, why), "")
	}
	if s.Flags&elf.SHF_COMPRESSED != 0 {
		return nil, mismatch("is compressed")
	}
	if s.Offset+s.Size < s.Offset || s.Offset+s.Size > uint64(len(lv.data)) {
		return nil, mismatch("lies beyond the end of the file")
	}
	got, err := lv.read(s.Addr, s.Size)
	if err != nil {
		return nil, mismatch("is not covered by a PT_LOAD segment with a matching file-to-address mapping (" + err.Error() + ")")
	}
	if !bytes.Equal(got, lv.data[s.Offset:s.Offset+s.Size]) {
		return nil, mismatch("differs from the bytes the loader maps at its address")
	}
	return got, nil
}

// validateSegments is the entry point: it builds the loader view and cross-checks every
// section and every content-bearing non-LOAD program header against it.
//
//	S1  every allocated, file-backed section's bytes at sh_offset equal the loader's bytes at sh_addr
//	S2  an executable section lies in a PF_X, non-PF_W segment, and no writable segment shares a page with it
//	S3  an allocated NOBITS section (not TLS) lies in the zero-fill tail (p_filesz..p_memsz) of a segment
//	S4  PT_TLS, PT_DYNAMIC and PT_INTERP images equal the loader's bytes
//	S5  PT_GNU_RELRO lies inside one PT_LOAD and does not touch an executable section
func validateSegments(f *elf.File, data []byte, path string) (*loaderView, error) {
	lv, err := newLoaderView(f, data, path)
	if err != nil {
		return nil, err
	}
	for _, s := range f.Sections {
		if s.Flags&elf.SHF_ALLOC == 0 || s.Size == 0 {
			continue
		}
		if s.Type == elf.SHT_NOBITS {
			if s.Flags&elf.SHF_TLS != 0 {
				continue
			}
			seg, ok := lv.seg(s.Addr)
			if !ok || s.Addr < seg.Vaddr+seg.Filesz || s.Addr+s.Size > seg.Vaddr+seg.Memsz {
				return nil, elfDiag(fmt.Sprintf("NOBITS section %s of %s (vaddr 0x%x, size 0x%x) is not inside the zero-fill part of a PT_LOAD", s.Name, path, s.Addr, s.Size), "")
			}
			continue
		}
		if _, err := lv.sectionBytes(s, path); err != nil {
			return nil, err
		}
		seg, _ := lv.seg(s.Addr)
		if s.Flags&elf.SHF_EXECINSTR != 0 {
			if seg.Flags&uint64(elf.PF_X) == 0 || seg.Flags&uint64(elf.PF_W) != 0 {
				return nil, elfDiag(fmt.Sprintf("executable section %s of %s is mapped by a PT_LOAD that is not (executable and non-writable); it is not the executed code, or it can be rewritten at run time", s.Name, path), "")
			}
		}
	}
	// S2, explicit: no writable segment shares a page with an executable section.
	for _, s := range f.Sections {
		if s.Flags&elf.SHF_ALLOC == 0 || s.Flags&elf.SHF_EXECINSTR == 0 || s.Size == 0 {
			continue
		}
		for _, g := range lv.segs {
			if g.Flags&uint64(elf.PF_W) != 0 && lv.pageDown(s.Addr) < lv.pageUp(g.Vaddr+g.Memsz) && lv.pageDown(g.Vaddr) < lv.pageUp(s.Addr+s.Size) {
				return nil, elfDiag(fmt.Sprintf("a writable PT_LOAD (vaddr 0x%x, memsz 0x%x) overlaps the executable section %s of %s; code must be in a non-writable segment", g.Vaddr, g.Memsz, s.Name, path), "")
			}
		}
	}
	for _, p := range f.Progs {
		switch p.Type {
		case elf.PT_TLS, elf.PT_DYNAMIC, elf.PT_INTERP:
			if p.Filesz == 0 {
				continue
			}
			img, err := lv.read(p.Vaddr, p.Filesz)
			if err != nil || p.Off+p.Filesz > uint64(len(data)) || !bytes.Equal(img, data[p.Off:p.Off+p.Filesz]) {
				return nil, elfDiag(fmt.Sprintf("%s program header (vaddr 0x%x, offset 0x%x) of %s does not match the bytes the loader maps at its address", p.Type, p.Vaddr, p.Off, path), "")
			}
		case ptGnuRelro:
			seg, ok := lv.seg(p.Vaddr)
			if !ok || p.Vaddr+p.Memsz > seg.Vaddr+seg.Memsz {
				return nil, elfDiag(fmt.Sprintf("PT_GNU_RELRO (vaddr 0x%x, memsz 0x%x) of %s is not inside a single PT_LOAD", p.Vaddr, p.Memsz, path), "")
			}
			for _, s := range f.Sections {
				if s.Flags&elf.SHF_EXECINSTR != 0 && s.Flags&elf.SHF_ALLOC != 0 && s.Size > 0 && s.Addr < p.Vaddr+p.Memsz && p.Vaddr < s.Addr+s.Size {
					return nil, elfDiag(fmt.Sprintf("PT_GNU_RELRO of %s covers the executable section %s", path, s.Name), "")
				}
			}
		}
	}
	return lv, nil
}

// Dynamic tags and relocation types used by checkDynamic.
const (
	dtPltRelSz, dtRela, dtRelaSz, dtRel, dtRelSz, dtPltRel, dtTextRel, dtJmpRel = 2, 7, 8, 17, 18, 20, 22, 23
	dtInitArray, dtInitArraySz, dtFlags, dtPreinitArray, dtPreinitArraySz       = 25, 27, 30, 32, 33
	dfTextRel                                                                   = 4
)

// checkDynamic rejects dynamic relocation and load-time patching that could rewrite code or
// read-only data after load:
//
//	D1  DT_TEXTREL, DF_TEXTREL, and any REL (non-RELA) relocation table are rejected
//	D2  every dynamic relocation (RELA, JMPREL, including IRELATIVE/ifunc) must write only
//	    inside a writable PT_LOAD, never an executable section and never a non-writable
//	    allocated section (code and read-only data are final after load)
//	W1  warning: a non-empty .preinit_array, or an .init_array entry that is not in executable
//	    code of the binary, runs code Janus did not extract before main
//
// Relocations are taken from both the PT_DYNAMIC table (what ld.so applies) and the
// allocated SHT_RELA sections, all read through the loader view.
func checkDynamic(f *elf.File, lv *loaderView, path string) (warnings []string, err error) {
	target := func(what string, off uint64) error {
		for _, s := range f.Sections {
			if s.Flags&elf.SHF_ALLOC == 0 || s.Size == 0 || s.Flags&elf.SHF_TLS != 0 {
				continue
			}
			if off < s.Addr+s.Size && s.Addr < off+8 && (s.Flags&elf.SHF_EXECINSTR != 0 || s.Flags&elf.SHF_WRITE == 0) {
				return elfDiag(fmt.Sprintf("%s of %s writes 0x%x, inside the %s section %s; code and read-only data must not be patched at load time", what, path, off, map[bool]string{true: "executable", false: "read-only"}[s.Flags&elf.SHF_EXECINSTR != 0], s.Name), "")
			}
		}
		if g, ok := lv.seg(off); !ok || g.Flags&uint64(elf.PF_W) == 0 {
			return elfDiag(fmt.Sprintf("%s of %s writes 0x%x, which is not in a writable PT_LOAD", what, path, off), "")
		}
		return nil
	}
	relas := func(what string, buf []byte) error {
		for o := 0; o+24 <= len(buf); o += 24 {
			if err := target(what, binary.LittleEndian.Uint64(buf[o:])); err != nil {
				return err
			}
		}
		return nil
	}
	for _, s := range f.Sections {
		if s.Flags&elf.SHF_ALLOC == 0 || s.Size == 0 {
			continue
		}
		switch s.Type {
		case elf.SHT_REL:
			return nil, elfDiag(fmt.Sprintf("%s has a REL relocation section (%s); only RELA tables are supported", path, s.Name), "")
		case elf.SHT_RELA:
			b, err := lv.sectionBytes(s, path)
			if err != nil {
				return nil, err
			}
			if err := relas("a relocation in "+s.Name, b); err != nil {
				return nil, err
			}
		}
	}
	var dyn []byte
	for _, p := range f.Progs {
		if p.Type == elf.PT_DYNAMIC {
			if dyn, err = lv.read(p.Vaddr, p.Filesz); err != nil {
				return nil, elfDiag(path+": PT_DYNAMIC is not file-backed: "+err.Error(), "")
			}
		}
	}
	tags := map[uint64]uint64{}
	for o := 0; o+16 <= len(dyn); o += 16 {
		tag, val := binary.LittleEndian.Uint64(dyn[o:]), binary.LittleEndian.Uint64(dyn[o+8:])
		if tag == 0 {
			break
		}
		tags[tag] = val
	}
	if _, ok := tags[dtTextRel]; ok {
		return nil, elfDiag(path+" has DT_TEXTREL: the loader may patch code pages", "")
	}
	if tags[dtFlags]&dfTextRel != 0 {
		return nil, elfDiag(path+" has DF_TEXTREL: the loader may patch code pages", "")
	}
	if _, ok := tags[dtRel]; ok {
		return nil, elfDiag(path+" has a DT_REL relocation table; only RELA tables are supported", "")
	}
	if tags[dtPltRel] == dtRel {
		return nil, elfDiag(path+" has REL PLT relocations; only RELA is supported", "")
	}
	for _, t := range [][2]uint64{{dtRela, dtRelaSz}, {dtJmpRel, dtPltRelSz}} {
		if sz := tags[t[1]]; tags[t[0]] != 0 && sz > 0 {
			b, err := lv.read(tags[t[0]], sz)
			if err != nil {
				return nil, elfDiag(path+": dynamic relocation table is not file-backed: "+err.Error(), "")
			}
			if err := relas("a dynamic relocation", b); err != nil {
				return nil, err
			}
		}
	}
	inCode := func(a uint64) bool {
		for _, s := range f.Sections {
			if s.Flags&elf.SHF_EXECINSTR != 0 && s.Flags&elf.SHF_ALLOC != 0 && a >= s.Addr && a < s.Addr+s.Size {
				return true
			}
		}
		return false
	}
	for _, name := range []string{".preinit_array", ".init_array"} {
		s := f.Section(name)
		if s == nil || s.Size == 0 || s.Type == elf.SHT_NOBITS {
			continue
		}
		b, err := lv.sectionBytes(s, path)
		if err != nil {
			return nil, err
		}
		for o := 0; o+8 <= len(b); o += 8 {
			a := binary.LittleEndian.Uint64(b[o:])
			if name == ".preinit_array" || !inCode(a) {
				warnings = append(warnings, fmt.Sprintf("%s entry 0x%x of %s runs before main and is not code of this binary's executable sections; code that rewrites verified code at run time (mprotect/mmap of text) is outside the threat model", name, a, path))
			}
		}
	}
	return warnings, nil
}

func warnAll(ws []string) {
	for _, w := range ws {
		fmt.Fprintln(os.Stderr, "warning: "+w)
	}
}
