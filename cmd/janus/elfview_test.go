package main

import (
	"debug/elf"
	"encoding/binary"
	"strings"
	"testing"
)

// Synthetic ELF64 executables for the loader-view and load-time-patching defences
// (cmd/janus/elfview.go, docs/SOUNDNESS.md "ELF loader semantics"). Layout:
//
//	file 0x0000  headers                              (program headers at 0x40)
//	file 0x1000  .text   0x401000 size 0x100  PT_LOAD A  R+X  filesz 0x1000
//	file 0x2000  .rodata 0x402000 size 0x100  PT_LOAD B  R    filesz 0x1000
//	file 0x3000  PT_LOAD C  RW  vaddr 0x403000 filesz 0x1000 memsz 0x2000:
//	             .data 0x403000, .rela.dyn 0x403100, .dynamic 0x403200, .init_array 0x403400,
//	             .preinit_array 0x403500, .bss (NOBITS) 0x404000
//	file 0x4000  .shstrtab, .symtab, .strtab, section headers
type synth struct {
	loads        []loadSeg // overrides the three default PT_LOADs when non-nil
	extraLoad    []loadSeg // appended after the defaults
	relas        [][2]uint64
	relaAsRaw    bool // the relocation table has no SHT_RELA section header: only PT_DYNAMIC finds it
	dyn          [][2]uint64
	relro        *[2]uint64
	initArr      []uint64
	preinit      []uint64
	syms         []synthSym
	textOffDelta uint64
	machine      elf.Machine // default EM_X86_64
	textFlags    uint64      // when nonzero, replaces .text sh_flags
}

type synthSym struct {
	name        string
	value, size uint64
	info        byte
	shndx       uint16
}

const (
	secText = 1 + iota
	secRodata
	secData
	secRela
	secDynamic
	secInit
	secPreinit
	secBss
	secShstr
	secSymtab
	secStrtab
)

func (o synth) build() []byte {
	d := make([]byte, 0x6000)
	le := binary.LittleEndian
	for i := 0; i < 0x100; i++ {
		d[0x1000+i] = 0x90
		d[0x2000+i] = 0x11
	}
	loads := o.loads
	if loads == nil {
		loads = []loadSeg{
			{0x1000, 0x401000, 0x1000, 0x1000, uint64(elf.PF_R | elf.PF_X), 0x1000},
			{0x2000, 0x402000, 0x1000, 0x1000, uint64(elf.PF_R), 0x1000},
			{0x3000, 0x403000, 0x1000, 0x2000, uint64(elf.PF_R | elf.PF_W), 0x1000},
		}
	}
	loads = append(append([]loadSeg(nil), loads...), o.extraLoad...)
	type ph struct {
		typ uint32
		s   loadSeg
	}
	var phs []ph
	for _, l := range loads {
		phs = append(phs, ph{uint32(elf.PT_LOAD), l})
	}
	if len(o.dyn) > 0 {
		phs = append(phs, ph{uint32(elf.PT_DYNAMIC), loadSeg{0x3200, 0x403200, uint64(16 * (len(o.dyn) + 1)), uint64(16 * (len(o.dyn) + 1)), 6, 8}})
	}
	if o.relro != nil {
		phs = append(phs, ph{ptGnuRelro, loadSeg{0, o.relro[0], 0, o.relro[1], 4, 1}})
	}
	// content of the data segment
	for i, r := range o.relas {
		le.PutUint64(d[0x3100+24*i:], r[0])
		le.PutUint64(d[0x3100+24*i+8:], r[1])
	}
	dyn := append([][2]uint64(nil), o.dyn...)
	for i, e := range dyn {
		le.PutUint64(d[0x3200+16*i:], e[0])
		le.PutUint64(d[0x3200+16*i+8:], e[1])
	}
	for i, a := range o.initArr {
		le.PutUint64(d[0x3400+8*i:], a)
	}
	for i, a := range o.preinit {
		le.PutUint64(d[0x3500+8*i:], a)
	}
	// strings and symbols
	shstr := []byte("\x00")
	nm := map[string]uint32{}
	add := func(s string) uint32 {
		if v, ok := nm[s]; ok {
			return v
		}
		nm[s] = uint32(len(shstr))
		shstr = append(shstr, s...)
		shstr = append(shstr, 0)
		return nm[s]
	}
	names := []string{".text", ".rodata", ".data", ".rela.dyn", ".dynamic", ".init_array", ".preinit_array", ".bss", ".shstrtab", ".symtab", ".strtab"}
	for _, n := range names {
		add(n)
	}
	strtab := []byte("\x00")
	symtab := make([]byte, 24)
	for _, s := range o.syms {
		off := len(strtab)
		strtab = append(strtab, s.name...)
		strtab = append(strtab, 0)
		e := make([]byte, 24)
		le.PutUint32(e, uint32(off))
		e[4] = s.info
		le.PutUint16(e[6:], s.shndx)
		le.PutUint64(e[8:], s.value)
		le.PutUint64(e[16:], s.size)
		symtab = append(symtab, e...)
	}
	copy(d[0x4000:], shstr)
	symOff := 0x4400
	copy(d[symOff:], symtab)
	strOff := 0x5000
	copy(d[strOff:], strtab)
	// section headers at 0x5800
	type sh struct {
		name            string
		typ, flags      uint64
		addr, off, size uint64
		link, info      uint32
		align, entsz    uint64
	}
	A, W, X := uint64(elf.SHF_ALLOC), uint64(elf.SHF_WRITE), uint64(elf.SHF_EXECINSTR)
	relaTyp := uint64(elf.SHT_RELA)
	if o.relaAsRaw {
		relaTyp = uint64(elf.SHT_PROGBITS)
	}
	textFlags := A | X
	if o.textFlags != 0 {
		textFlags = o.textFlags
	}
	secs := []sh{
		{},
		{".text", 1, textFlags, 0x401000, 0x1000 + o.textOffDelta, 0x100, 0, 0, 16, 0},
		{".rodata", 1, A, 0x402000, 0x2000, 0x100, 0, 0, 16, 0},
		{".data", 1, A | W, 0x403000, 0x3000, 0x100, 0, 0, 16, 0},
		{".rela.dyn", relaTyp, A, 0x403100, 0x3100, uint64(24 * len(o.relas)), 0, 0, 8, 24},
		{".dynamic", 6, A | W, 0x403200, 0x3200, uint64(16 * len(dyn)), 0, 0, 8, 16},
		{".init_array", 14, A | W, 0x403400, 0x3400, uint64(8 * len(o.initArr)), 0, 0, 8, 8},
		{".preinit_array", 16, A | W, 0x403500, 0x3500, uint64(8 * len(o.preinit)), 0, 0, 8, 8},
		{".bss", 8, A | W, 0x404000, 0x4000, 0x100, 0, 0, 16, 0},
		{".shstrtab", 3, 0, 0, 0x4000, uint64(len(shstr)), 0, 0, 1, 0},
		{".symtab", 2, 0, 0, uint64(symOff), uint64(len(symtab)), secStrtab, 1, 8, 24},
		{".strtab", 3, 0, 0, uint64(strOff), uint64(len(strtab)), 0, 0, 1, 0},
	}
	shoff := 0x5800
	for i, s := range secs {
		p := shoff + 64*i
		le.PutUint32(d[p:], nm[s.name])
		le.PutUint32(d[p+4:], uint32(s.typ))
		le.PutUint64(d[p+8:], s.flags)
		le.PutUint64(d[p+16:], s.addr)
		le.PutUint64(d[p+24:], s.off)
		le.PutUint64(d[p+32:], s.size)
		le.PutUint32(d[p+40:], s.link)
		le.PutUint32(d[p+44:], s.info)
		le.PutUint64(d[p+48:], s.align)
		le.PutUint64(d[p+56:], s.entsz)
	}
	// ELF header
	copy(d, []byte{0x7f, 'E', 'L', 'F', 2, 1, 1})
	le.PutUint16(d[16:], uint16(elf.ET_EXEC))
	m := o.machine
	if m == 0 {
		m = elf.EM_X86_64
	}
	le.PutUint16(d[18:], uint16(m))
	le.PutUint32(d[20:], 1)
	le.PutUint64(d[24:], 0x401000)
	le.PutUint64(d[32:], 0x40)
	le.PutUint64(d[40:], uint64(shoff))
	le.PutUint16(d[52:], 64)
	le.PutUint16(d[54:], 56)
	le.PutUint16(d[56:], uint16(len(phs)))
	le.PutUint16(d[58:], 64)
	le.PutUint16(d[60:], uint16(len(secs)))
	le.PutUint16(d[62:], secShstr)
	for i, p := range phs {
		q := 0x40 + 56*i
		le.PutUint32(d[q:], p.typ)
		le.PutUint32(d[q+4:], uint32(p.s.Flags))
		le.PutUint64(d[q+8:], p.s.Off)
		le.PutUint64(d[q+16:], p.s.Vaddr)
		le.PutUint64(d[q+24:], p.s.Vaddr)
		le.PutUint64(d[q+32:], p.s.Filesz)
		le.PutUint64(d[q+40:], p.s.Memsz)
		le.PutUint64(d[q+48:], p.s.Align)
	}
	return d
}

// checkAll runs every load-time defence the way loadBinaryMode does.
func checkAll(t *testing.T, d []byte) (warns []string, err error) {
	t.Helper()
	f, e := elf.NewFile(strings.NewReader(string(d)))
	if e != nil {
		t.Fatalf("synthetic ELF does not parse: %v", e)
	}
	lv, err := validateSegments(f, d, "synth")
	if err != nil {
		return nil, err
	}
	if warns, err = checkDynamic(f, lv, "synth"); err != nil {
		return nil, err
	}
	syms, _ := f.Symbols()
	for _, s := range syms {
		if err := checkSymbolRange(f, s, "synth"); err != nil {
			return warns, err
		}
	}
	return warns, nil
}

func wantReject(t *testing.T, name string, o synth, frag string) {
	t.Helper()
	_, err := checkAll(t, o.build())
	if err == nil {
		t.Errorf("%s: accepted, want rejection containing %q", name, frag)
		return
	}
	if !strings.Contains(err.Error(), frag) {
		t.Errorf("%s: rejected with %q, want it to contain %q", name, err.Error(), frag)
	}
}

func TestElfControlAccepted(t *testing.T) {
	if w, err := checkAll(t, synth{}.build()); err != nil || len(w) != 0 {
		t.Fatalf("base synthetic ELF: err=%v warnings=%v", err, w)
	}
	// relocations into writable data, DT_RELA through the dynamic table, ifunc into the GOT-like data
	o := synth{relas: [][2]uint64{{0x403010, 8}, {0x403018, 37}}, dyn: [][2]uint64{{dtRela, 0x403100}, {dtRelaSz, 48}, {0, 0}}}
	if _, err := checkAll(t, o.build()); err != nil {
		t.Fatalf("relocations into writable data: %v", err)
	}
}

func TestElfLoaderViewRejections(t *testing.T) {
	r, rx, rw := uint64(elf.PF_R), uint64(elf.PF_R|elf.PF_X), uint64(elf.PF_R|elf.PF_W)
	def := func() []loadSeg {
		return []loadSeg{{0x1000, 0x401000, 0x1000, 0x1000, rx, 0x1000}, {0x2000, 0x402000, 0x1000, 0x1000, r, 0x1000}, {0x3000, 0x403000, 0x1000, 0x2000, rw, 0x1000}}
	}
	// O1: a later PT_LOAD maps the code's addresses from different file bytes
	wantReject(t, "overlap", synth{extraLoad: []loadSeg{{0x4000, 0x401000, 0x1000, 0x1000, rx, 0x1000}}}, "overlaps an earlier PT_LOAD")
	wantReject(t, "overlap-64k-align", synth{extraLoad: []loadSeg{{0x10000, 0x410000, 0x1000, 0x1000, rx, 0x10000}, {0x4000, 0x410000, 0x100, 0x100, rx, 0x10000}}}, "")
	wantReject(t, "overlap-partial-page", synth{extraLoad: []loadSeg{{0x4010, 0x401010, 0x10, 0x10, rx, 1}}}, "overlaps an earlier PT_LOAD")
	l := def()
	l[0].Memsz = 0x800
	wantReject(t, "filesz>memsz", synth{loads: l}, "p_filesz > p_memsz")
	l = def()
	l[0].Vaddr += 0x10
	wantReject(t, "misaligned", synth{loads: l}, "not congruent")
	l = def()
	l[0].Align = 0x3000
	wantReject(t, "p_align", synth{loads: l}, "p_align")
	l = def()
	l[0].Flags = 7
	wantReject(t, "W+X segment", synth{loads: l}, "writable and executable")
	l = def()
	l[0].Filesz, l[0].Memsz = 0x9000, 0x9000
	wantReject(t, "beyond file", synth{loads: l}, "beyond the end of the file")
	// S1: section header at a different file offset than the loader map
	wantReject(t, "sh_offset", synth{textOffDelta: 8}, "differs from the bytes the loader maps")
	// S2: code in a writable segment
	l = def()
	l[0].Flags = rw
	wantReject(t, "writable code", synth{loads: l}, "not (executable and non-writable)")
	l = def()
	l[0].Flags = r
	wantReject(t, "non-exec code segment", synth{loads: l}, "not (executable and non-writable)")
	// S5: RELRO over code, RELRO outside any PT_LOAD
	wantReject(t, "relro over text", synth{relro: &[2]uint64{0x401000, 0x100}}, "covers the executable section")
	wantReject(t, "relro outside", synth{relro: &[2]uint64{0x900000, 0x100}}, "not inside a single PT_LOAD")
}

func TestElfDynamicRejections(t *testing.T) {
	rela := func(t uint64) [][2]uint64 { return [][2]uint64{{t, 8}} }
	tab := [][2]uint64{{dtRela, 0x403100}, {dtRelaSz, 24}, {0, 0}}
	// (a) a relocation whose target is in code or read-only data, section and PT_DYNAMIC views
	wantReject(t, "reloc into .text", synth{relas: rela(0x401010)}, "executable section .text")
	wantReject(t, "IRELATIVE into .text", synth{relas: [][2]uint64{{0x401020, 37}}}, "executable section .text")
	wantReject(t, "reloc into .rodata", synth{relas: rela(0x402010)}, "read-only section .rodata")
	wantReject(t, "reloc straddling .text end", synth{relas: rela(0x4010fc)}, "executable section .text")
	wantReject(t, "reloc outside any writable segment", synth{relas: rela(0x700000)}, "not in a writable PT_LOAD")
	wantReject(t, "DT_RELA reloc into .text", synth{relas: rela(0x401010), relaAsRaw: true, dyn: tab}, "executable section .text")
	wantReject(t, "DT_JMPREL reloc into .text", synth{relas: rela(0x401010), relaAsRaw: true, dyn: [][2]uint64{{dtJmpRel, 0x403100}, {dtPltRelSz, 24}, {0, 0}}}, "executable section .text")
	// DT_TEXTREL, DF_TEXTREL, REL tables
	wantReject(t, "DT_TEXTREL", synth{dyn: [][2]uint64{{dtTextRel, 0}, {0, 0}}}, "DT_TEXTREL")
	wantReject(t, "DF_TEXTREL", synth{dyn: [][2]uint64{{dtFlags, dfTextRel}, {0, 0}}}, "DF_TEXTREL")
	wantReject(t, "DT_REL", synth{dyn: [][2]uint64{{dtRel, 0x403100}, {dtRelSz, 16}, {0, 0}}}, "DT_REL")
	wantReject(t, "PLTREL=REL", synth{dyn: [][2]uint64{{dtPltRel, dtRel}, {0, 0}}}, "REL PLT")
}

func TestElfSymbolRangeRejections(t *testing.T) {
	fn := byte(elf.STT_FUNC) | byte(elf.STB_GLOBAL)<<4
	obj := byte(elf.STT_OBJECT) | byte(elf.STB_GLOBAL)<<4
	ok := synth{syms: []synthSym{{"f", 0x401000, 0x10, fn, secText}, {"g", 0x403010, 8, obj, secData}, {"marker", 0x404100, 0, obj, secBss}}}
	if _, err := checkAll(t, ok.build()); err != nil {
		t.Fatalf("sane symbols: %v", err)
	}
	// a boundary marker starting exactly at the section end (Go's __stop_ symbols) is fine
	if _, err := checkAll(t, synth{syms: []synthSym{{"__stop_x", 0x401100, 1, obj, secText}}}.build()); err != nil {
		t.Fatalf("end-of-section marker: %v", err)
	}
	wantReject(t, "symbol past the section end", synth{syms: []synthSym{{"x", 0x401101, 1, obj, secText}}}, "lies outside its section")
	wantReject(t, "func past .text", synth{syms: []synthSym{{"f", 0x4010f8, 0x10, fn, secText}}}, "lies outside its section .text")
	wantReject(t, "func below .text", synth{syms: []synthSym{{"f", 0x400f00, 0x10, fn, secText}}}, "lies outside its section .text")
	wantReject(t, "object in wrong section", synth{syms: []synthSym{{"g", 0x402000, 8, obj, secData}}}, "lies outside its section .data")
	wantReject(t, "size wraps", synth{syms: []synthSym{{"f", 0x401000, ^uint64(0), fn, secText}}}, "lies outside its section")
	// the same name at two addresses is an ambiguity, reported by lookup (never silently picked)
	b := &Binary{Path: "synth", Funcs: []Func{{"dup", 0x401000, 4}, {"dup", 0x401010, 4}}}
	if _, err := b.lookup("dup"); err == nil || !strings.Contains(err.Error(), "ambiguous") {
		t.Fatalf("duplicate symbol: lookup err = %v, want an ambiguity", err)
	}
}

func TestElfInitArrayWarnings(t *testing.T) {
	w, err := checkAll(t, synth{initArr: []uint64{0x401010}}.build())
	if err != nil || len(w) != 0 {
		t.Fatalf("init_array entry inside code: err=%v warnings=%v", err, w)
	}
	w, err = checkAll(t, synth{initArr: []uint64{0x402010}}.build())
	if err != nil || len(w) != 1 || !strings.Contains(w[0], ".init_array") {
		t.Fatalf("init_array entry outside code: err=%v warnings=%v", err, w)
	}
	w, err = checkAll(t, synth{preinit: []uint64{0x401010}}.build())
	if err != nil || len(w) != 1 || !strings.Contains(w[0], ".preinit_array") {
		t.Fatalf("preinit_array: err=%v warnings=%v", err, w)
	}
}

// Segments that are disjoint at 4 KiB but share a 64 KiB page overlap on arm64 kernels with
// 64 KiB pages (the default layout puts all three PT_LOADs in one 64 KiB page); on x86-64,
// where the page size is 4 KiB, the same layout is fine.
func TestElfLargePageOverlapArm64(t *testing.T) {
	if _, err := checkAll(t, synth{}.build()); err != nil {
		t.Fatalf("amd64 4 KiB-disjoint layout: %v", err)
	}
	wantReject(t, "arm64 shared 64k page", synth{machine: elf.EM_AARCH64}, "overlaps an earlier PT_LOAD")
}
