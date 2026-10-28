package main

// The C environment of a cgo executable (docs/FFI.md, sections 2-4): what C code reaches
// besides its own text and read-only data.
//
//   - PLT stubs. A call from C to a shared-library function (memcpy, strlen, malloc, setjmp, ...)
//     goes to its PLT entry, which jumps through a GOT slot the dynamic linker fills. The entry
//     has no symbol. loadCEnv decodes every PLT entry, checks that it has the canonical form
//     (arm64: ADRP X16 / LDR X17, [X16, #lo] / ADD X16, X16, #lo / BR X17; amd64 .plt.sec:
//     ENDBR64 / [BND] JMP [RIP+d]; amd64 .plt without IBT: JMP [RIP+d] / PUSH / JMP) and that
//     its GOT slot is exactly the target of an R_*_JUMP_SLOT relocation, and names the entry
//     "<symbol>@plt". A call to it becomes an external stub (Janus.StubKind.external) whose
//     meaning is a libc contract (Janus.Contracts.Libc). An entry that does not have the
//     canonical form, or whose slot is not a jump slot, is not a stub: the branch stays
//     unresolved and the model faults there (noCode), which is sound.
//   - Statically resolved GOT slots. -fPIC C code loads the address of a global from the GOT.
//     In a non-PIE executable the linker fills a slot of a symbol the executable defines, and
//     no dynamic relocation touches it; the slot lies in PT_GNU_RELRO, which the dynamic linker
//     makes read-only before any user code runs. Such a slot is copied as read-only data
//     (collectData, "got:<symbol>"), like .rodata. A slot with a dynamic relocation
//     (R_*_GLOB_DAT for a libc symbol such as __stack_chk_guard) is not: its run-time value is
//     not in the file.
//   - Writable C data objects (.data/.bss) that C code references, directly or through a
//     static GOT slot: rendered as `Extracted.cdata` (name, address, size, initial bytes), so
//     that a theorem can name them. They are not loaded by `Program.DataLoaded`: their run-time
//     content is not fixed by the binary, and a theorem states what it needs about it.
//   - The TLS image (PT_TLS and the STT_TLS symbols): rendered as `Extracted.tls` when an
//     extracted function reads the thread pointer, so that a theorem can say where a __thread
//     variable lives (Janus.Contracts.TLS).
//   - //export: the C wrapper cgo generates for an exported Go function loads the address of
//     the Go function `pkg._cgoexp_<hash>_F` (through the GOT, or as an immediate) and passes it
//     to crosscall2. The extractor follows that code address so that the Go code is copied too
//     (reachability, untrusted).
//
// Everything here except the byte copy of GOT slots decides only *what* is copied or how a
// call is named; the names are recomputed by `janus check` from the binary, and a wrong
// decision either makes a proof impossible or names a stub by a symbol whose contract the
// theorem states explicitly (see docs/SOUNDNESS.md, "C environment").

import (
	"bytes"
	"debug/elf"
	"encoding/binary"
	"fmt"
	"sort"
	"strings"

	"golang.org/x/arch/x86/x86asm"
)

// cenvInfo is what loadCEnv reads from the ELF file.
type cenvInfo struct {
	plt    map[uint64]string   // PLT entry -> "symbol@plt"
	dynRel []uint64            // r_offset of every dynamic relocation, sorted
	dynSym map[uint64]dynReloc // r_offset -> the relocation (its symbol, type, addend)
	relro  [2]uint64           // PT_GNU_RELRO [start, end), or zero
	goText [2]uint64           // [runtime.text, runtime.etext), or zero
	tls    *tlsImage           // PT_TLS, or nil
}

// dynReloc is one dynamic relocation: its symbol (empty for none), type and addend.
type dynReloc struct {
	Sym    string
	Type   uint32
	Addend uint64
}

// DynGOT is a GOT slot the extracted C code reads that a dynamic relocation fills
// (Janus.DynGOT): its value is the dynamic linker's, so it is not copied; a theorem states it as
// a precondition in terms of the relocation's symbol (Janus.GotBound).
type DynGOT struct {
	Name   string // the relocation's symbol
	Slot   uint64
	Type   uint32 // R_AARCH64_GLOB_DAT (1025), R_X86_64_GLOB_DAT (6), ...
	Addend uint64 // r_addend (two's complement)
}

// tlsImage is the executable's TLS segment (module 1, static TLS).
type tlsImage struct {
	Size  uint64 // p_memsz
	Align uint64 // p_align
	Init  []byte // .tdata (p_filesz bytes); the rest is zero (.tbss)
	Vars  []tlsVar
}

// tlsVar is one STT_TLS symbol: its offset inside the TLS segment and its size.
type tlsVar struct {
	Name string
	Off  uint64
	Size uint64
}

// CData is one writable C data object referenced by extracted C code (Janus.CData).
type CData struct {
	Name    string
	Base    uint64
	Size    uint64
	BSS     bool
	Init    []byte
	Section string
}

const (
	rAarch64JumpSlot = 1026
	rX8664JumpSlot   = 7
	ptGnuRelro       = 0x6474e552
)

// loadCEnv reads the PLT, the dynamic relocations, PT_GNU_RELRO, PT_TLS and the Go text range.
func (b *Binary) loadCEnv(f *elf.File, lv *loaderView, path string) error {
	ci := &cenvInfo{plt: map[uint64]string{}, dynSym: map[uint64]dynReloc{}}
	b.cenv = ci
	for _, p := range f.Progs {
		switch p.Type {
		case ptGnuRelro:
			ci.relro = [2]uint64{p.Vaddr, p.Vaddr + p.Memsz}
		case elf.PT_TLS:
			img := &tlsImage{Size: p.Memsz, Align: p.Align}
			if p.Filesz > 0 {
				buf, err := lv.read(p.Vaddr, p.Filesz)
				if err != nil {
					return elfDiag(path+": the PT_TLS image is not file-backed by a PT_LOAD: "+err.Error(), "")
				}
				img.Init = buf
			}
			ci.tls = img
		}
	}
	if syms, err := f.Symbols(); err == nil {
		for _, s := range syms {
			switch {
			case s.Name == "runtime.text" && s.Section != elf.SHN_UNDEF:
				ci.goText[0] = s.Value
			case s.Name == "runtime.etext" && s.Section != elf.SHN_UNDEF:
				ci.goText[1] = s.Value
			case elf.ST_TYPE(s.Info) == elf.STT_TLS && ci.tls != nil && s.Section != elf.SHN_UNDEF:
				ci.tls.Vars = append(ci.tls.Vars, tlsVar{Name: s.Name, Off: s.Value, Size: s.Size})
			}
		}
	}
	if ci.tls != nil {
		sort.SliceStable(ci.tls.Vars, func(i, j int) bool {
			if ci.tls.Vars[i].Off != ci.tls.Vars[j].Off {
				return ci.tls.Vars[i].Off < ci.tls.Vars[j].Off
			}
			return ci.tls.Vars[i].Name < ci.tls.Vars[j].Name
		})
	}
	dsyms, _ := f.DynamicSymbols()
	slots := map[uint64]string{} // jump-slot GOT address -> symbol
	jumpSlot := uint32(rAarch64JumpSlot)
	if f.Machine == elf.EM_X86_64 {
		jumpSlot = rX8664JumpSlot
	}
	for _, s := range f.Sections {
		if s.Type != elf.SHT_RELA || s.Flags&elf.SHF_ALLOC == 0 {
			continue
		}
		data, err := lv.sectionBytes(s, path)
		if err != nil {
			return err
		}
		for off := 0; off+24 <= len(data); off += 24 {
			rOff := binary.LittleEndian.Uint64(data[off:])
			info := binary.LittleEndian.Uint64(data[off+8:])
			ci.dynRel = append(ci.dynRel, rOff)
			rel := dynReloc{Type: uint32(info), Addend: binary.LittleEndian.Uint64(data[off+16:])}
			if k := int(info >> 32); k >= 1 && k <= len(dsyms) {
				rel.Sym = dsyms[k-1].Name
			}
			ci.dynSym[rOff] = rel
			if uint32(info) == jumpSlot {
				if k := int(info >> 32); k >= 1 && k <= len(dsyms) && dsyms[k-1].Name != "" {
					slots[rOff] = dsyms[k-1].Name
				}
			}
		}
	}
	sort.Slice(ci.dynRel, func(i, j int) bool { return ci.dynRel[i] < ci.dynRel[j] })
	for _, s := range f.Sections {
		if s.Name != ".plt" && s.Name != ".plt.sec" {
			continue
		}
		data, err := lv.sectionBytes(s, path)
		if err != nil {
			return err
		}
		if f.Machine == elf.EM_AARCH64 {
			pltArm64(ci, slots, s.Addr, data)
		} else {
			pltAmd64(ci, slots, s.Name, s.Addr, data)
		}
	}
	return nil
}

// pltArm64 names the canonical 16-byte entries of an arm64 .plt (after its 32-byte header).
func pltArm64(ci *cenvInfo, slots map[uint64]string, base uint64, data []byte) {
	for off := 32; off+16 <= len(data); off += 16 {
		pc := base + uint64(off)
		w := func(i int) uint32 { return binary.LittleEndian.Uint32(data[off+4*i:]) }
		adrp, ldr, add, br := w(0), w(1), w(2), w(3)
		if adrp&0x9f00001f != 0x90000010 || ldr&0xffc003ff != 0xf9400211 || add&0xffc003ff != 0x91000210 || br != 0xd61f0220 {
			continue
		}
		immlo := uint64(adrp>>29) & 3
		immhi := uint64(adrp>>5) & 0x7ffff
		imm := int64((immhi<<2|immlo)<<43) >> 31 // sign-extend the 21-bit page count, times 4096
		page := uint64(int64(pc&^0xfff) + imm)
		lo := uint64(ldr>>10&0xfff) * 8
		if uint64(add>>10&0xfff) != lo {
			continue
		}
		if name, ok := slots[page+lo]; ok {
			ci.plt[pc] = name + "@plt"
		}
	}
}

// pltAmd64 names the canonical 16-byte entries of an amd64 .plt.sec (IBT: ENDBR64; [BND] JMP
// [RIP+d]) or of a .plt without IBT (JMP [RIP+d]; PUSH imm32; JMP rel32, after the 16-byte
// header). In a .plt with IBT the entries (ENDBR64; PUSH; [BND] JMP .plt0) are the lazy path of
// the .plt.sec entries and are not named.
func pltAmd64(ci *cenvInfo, slots map[uint64]string, sec string, base uint64, data []byte) {
	start := 0
	if sec == ".plt" {
		start = 16
	}
	for off := start; off+16 <= len(data); off += 16 {
		e := data[off : off+16]
		pc := base + uint64(off)
		var j int // offset of the FF 25 (JMP [RIP+d32])
		switch {
		case sec == ".plt.sec" && bytes.HasPrefix(e, []byte{0xf3, 0x0f, 0x1e, 0xfa, 0xf2, 0xff, 0x25}):
			j = 5
		case sec == ".plt.sec" && bytes.HasPrefix(e, []byte{0xf3, 0x0f, 0x1e, 0xfa, 0xff, 0x25}):
			j = 4
		case sec == ".plt" && e[0] == 0xff && e[1] == 0x25 && e[6] == 0x68 && e[11] == 0xe9:
			j = 0
		default:
			continue
		}
		next := pc + uint64(j) + 6
		slot := uint64(int64(next) + int64(int32(binary.LittleEndian.Uint32(e[j+2:]))))
		if name, ok := slots[slot]; ok {
			ci.plt[pc] = name + "@plt"
		}
	}
}

// pltName returns the name of the PLT entry at addr ("memcpy@plt"), if it is one.
func (b *Binary) pltName(addr uint64) (string, bool) {
	if b.cenv == nil {
		return "", false
	}
	n, ok := b.cenv.plt[addr]
	return n, ok
}

// isGoCode reports whether addr is Go-compiled or Go-assembly code ([runtime.text,
// runtime.etext)); C code of a cgo binary lies outside.
func (b *Binary) isGoCode(addr uint64) bool {
	if b.cenv == nil || b.cenv.goText[1] == 0 {
		return true
	}
	return addr >= b.cenv.goText[0] && addr < b.cenv.goText[1]
}

// staticGOT reports whether the 8 bytes at addr are a GOT slot the dynamic linker never writes:
// inside .got and PT_GNU_RELRO, 8-aligned, and touched by no dynamic relocation.
func (b *Binary) staticGOT(addr uint64) bool {
	if b.cenv == nil || addr%8 != 0 || addr < b.cenv.relro[0] || addr+8 > b.cenv.relro[1] {
		return false
	}
	sec, ok := b.sectionOf(addr)
	if !ok || sec.Name != ".got" || sec.NoBits || addr+8 > sec.End() {
		return false
	}
	i := sort.Search(len(b.cenv.dynRel), func(i int) bool { return b.cenv.dynRel[i]+8 > addr })
	return i == len(b.cenv.dynRel) || b.cenv.dynRel[i] >= addr+8
}

// gotWord is the word in a static GOT slot.
func (b *Binary) gotWord(addr uint64) (uint64, bool) {
	if !b.staticGOT(addr) {
		return 0, false
	}
	sec, _ := b.sectionOf(addr)
	return binary.LittleEndian.Uint64(sec.data[addr-sec.Addr:]), true
}

// gotName names a static GOT slot by the symbol its word points to ("got:e_counter").
func (b *Binary) gotName(addr uint64) string {
	w, _ := b.gotWord(addr)
	if f, ok := b.containing(w); ok && f.Addr == w {
		return "got:" + f.Name
	}
	if s, ok, _ := b.dataSymbolAt(w); ok {
		if s.Addr == w {
			return "got:" + s.Name
		}
		return fmt.Sprintf("got:%s+0x%x", s.Name, w-s.Addr)
	}
	return fmt.Sprintf("got:0x%x", w)
}

// cgoExportRoots returns the Go functions behind //export wrappers that the C function seg
// refers to: code addresses of `pkg._cgoexp_<hash>_F` loaded from a static GOT slot, computed
// PC-relatively, or (amd64) moved as an immediate.
func cgoExportRoots(b *Binary, seg Segment) []Func {
	if b.isGoCode(seg.Base) {
		return nil
	}
	var cands []uint64
	for _, r := range segmentDataRefs(b, seg) {
		cands = append(cands, r.Target)
		if w, ok := b.gotWord(r.Target); ok {
			cands = append(cands, w)
		}
	}
	if b.GOARCH == "amd64" {
		for _, in := range sweepAmd64(seg.Bytes, seg.Base) {
			for _, a := range in.Inst.Args {
				if imm, ok := a.(x86asm.Imm); ok {
					cands = append(cands, uint64(imm))
				}
			}
		}
	}
	var out []Func
	seen := map[uint64]bool{}
	for _, c := range cands {
		f, ok := b.containing(c)
		// main._cgoexp_… (arm64), or _cgoexp_… as the amd64 linker names it
		if !ok || f.Addr != c || seen[c] || !(strings.Contains(f.Name, "._cgoexp_") || strings.HasPrefix(f.Name, "_cgoexp_")) {
			continue
		}
		seen[c] = true
		out = append(out, f)
	}
	return out
}

// cImmediateRoots lists the C functions whose entry address a C segment materialises as an
// amd64 immediate operand (`mov $f, %rdx` in a non-PIE executable: a function pointer passed
// on, e.g. a qsort-style comparator). On arm64 such addresses are PC-relative (ADR/ADRP+ADD)
// and reach the extraction as "code" references. Only exact entries of functions outside the
// Go text count, so a coincidental constant inside C code is at most an extra function.
func cImmediateRoots(b *Binary, seg Segment) []Func {
	if b.GOARCH != "amd64" || b.isGoCode(seg.Base) {
		return nil
	}
	var out []Func
	seen := map[uint64]bool{}
	for _, in := range sweepAmd64(seg.Bytes, seg.Base) {
		for _, a := range in.Inst.Args {
			imm, ok := a.(x86asm.Imm)
			if !ok || imm <= 0 {
				continue
			}
			c := uint64(imm)
			f, ok := b.containing(c)
			if !ok || f.Addr != c || seen[c] || b.isGoCode(c) || stubLike(f.Name) {
				continue
			}
			seen[c] = true
			out = append(out, f)
		}
	}
	return out
}

// readsThreadPointer reports whether the segment reads the thread pointer (arm64 MRS Xt,
// TPIDR_EL0; amd64 an FS-segment memory operand).
func readsThreadPointer(b *Binary, s Segment) bool {
	if b.GOARCH != "amd64" {
		for _, w := range s.Words {
			if w&0xffffffe0 == 0xd53bd040 {
				return true
			}
		}
		return false
	}
	for _, in := range sweepAmd64(s.Bytes, s.Base) {
		for _, a := range in.Inst.Args {
			if m, ok := a.(x86asm.Mem); ok && m.Segment == x86asm.FS {
				return true
			}
		}
	}
	return false
}

// collectCData lists the writable data objects the extracted C functions reference, directly
// or through a static GOT slot, sorted by address.
func collectCData(b *Binary, x *Extraction) []CData {
	seen := map[uint64]bool{}
	var out []CData
	add := func(addr uint64) {
		sec, ok := b.sectionOf(addr)
		if !ok || !sec.Writable || sec.Exec || b.staticGOT(addr) {
			return
		}
		sym, ok, _ := b.dataSymbolAt(addr)
		if !ok || seen[sym.Addr] || sym.End() > sec.End() {
			return
		}
		seen[sym.Addr] = true
		d := CData{Name: sym.Name, Base: sym.Addr, Size: sym.Size, BSS: sec.NoBits, Section: sec.Name}
		if !sec.NoBits && sym.Size <= maxDataSymbol {
			d.Init = append([]byte(nil), sec.data[sym.Addr-sec.Addr:sym.End()-sec.Addr]...)
		}
		out = append(out, d)
	}
	for _, r := range x.DataRefs {
		if b.isGoCode(r.From) {
			continue
		}
		if w, ok := b.gotWord(r.Target); ok {
			add(w)
			continue
		}
		add(r.Target)
	}
	// amd64: the linker relaxes `mov sym@GOTPCREL(%rip), %r` to `mov $sym, %r` in a non-PIE
	// executable, so C code names its globals by immediates too (a coincidental constant only
	// adds a name: the objects' memory is the precondition's)
	if b.GOARCH == "amd64" {
		for _, s := range x.Segments {
			if b.isGoCode(s.Base) {
				continue
			}
			for _, in := range sweepAmd64(s.Bytes, s.Base) {
				for _, a := range in.Inst.Args {
					if imm, ok := a.(x86asm.Imm); ok && imm > 0 {
						add(uint64(imm))
					}
				}
			}
		}
	}
	sort.Slice(out, func(i, j int) bool { return out[i].Base < out[j].Base })
	return out
}

// collectDynGOT lists the GOT slots with a dynamic relocation that the extracted C functions
// read (an 8-aligned .got slot whose r_offset is the slot and whose relocation names a symbol),
// sorted by address. Not copied: the slot's run-time value is the dynamic linker's binding of
// the symbol, which a theorem states as a precondition (Janus.GotBound).
func collectDynGOT(b *Binary, x *Extraction) []DynGOT {
	if b.cenv == nil {
		return nil
	}
	seen := map[uint64]bool{}
	var out []DynGOT
	for _, r := range x.DataRefs {
		if b.isGoCode(r.From) || r.Target%8 != 0 || seen[r.Target] {
			continue
		}
		sec, ok := b.sectionOf(r.Target)
		if !ok || sec.Name != ".got" || b.staticGOT(r.Target) {
			continue
		}
		rel, ok := b.cenv.dynSym[r.Target]
		if !ok || rel.Sym == "" {
			continue
		}
		seen[r.Target] = true
		out = append(out, DynGOT{Name: rel.Sym, Slot: r.Target, Type: rel.Type, Addend: rel.Addend})
	}
	sort.Slice(out, func(i, j int) bool { return out[i].Slot < out[j].Slot })
	return out
}

// extractionTLS is the TLS image to render: the binary's, when an extracted function reads the
// thread pointer.
func extractionTLS(b *Binary, x *Extraction) *tlsImage {
	if b.cenv == nil || b.cenv.tls == nil {
		return nil
	}
	for _, s := range x.Segments {
		if readsThreadPointer(b, s) {
			return b.cenv.tls
		}
	}
	return nil
}

func writeBytesList(sb *strings.Builder, bs []byte, indent string) {
	sb.WriteString("[")
	multi := len(bs) > bytesPerLine
	for j, v := range bs {
		if j > 0 {
			sb.WriteString(",")
			if !(multi && j%bytesPerLine == 0) {
				sb.WriteString(" ")
			}
		}
		if multi && j%bytesPerLine == 0 {
			sb.WriteString("\n" + indent + "    ")
		}
		fmt.Fprintf(sb, "0x%02x", v)
	}
	sb.WriteString("]")
}

// writeCEnv renders `def cdata`, `def dyngot` and `def tls` (only when present, so that other
// extractions are byte-identical to earlier ones).
func writeCEnv(sb *strings.Builder, x *Extraction) {
	if len(x.DynGOT) > 0 {
		sb.WriteString("/-- GOT slots the extracted C code reads that a dynamic relocation fills (not copied: their\nrun-time value is the dynamic linker's binding of the symbol; see `Janus.GotBound`). -/\n")
		sb.WriteString("def dyngot : List DynGOT := [")
		for i, d := range x.DynGOT {
			if i > 0 {
				sb.WriteString(",")
			}
			fmt.Fprintf(sb, "\n  { name := %s, slot := 0x%x, rtype := %d, addend := %d }", leanString(d.Name), d.Slot, d.Type, d.Addend)
		}
		sb.WriteString(" ]\n\n")
	}
	if len(x.CData) > 0 {
		sb.WriteString("/-- Writable C data objects the extracted C code references (`.data`/`.bss`), with their\ninitial bytes (`.bss`: zero). Not loaded by `Program.DataLoaded`. -/\n")
		sb.WriteString("def cdata : List CData := [")
		for i, d := range x.CData {
			if i > 0 {
				sb.WriteString(",")
			}
			fmt.Fprintf(sb, "\n  { name := %s, base := 0x%x, size := %d, bss := %t, init := ", leanString(d.Name), d.Base, d.Size, d.BSS)
			writeBytesList(sb, d.Init, "  ")
			sb.WriteString(" }")
		}
		sb.WriteString(" ]\n\n")
	}
	if x.TLS != nil {
		sb.WriteString("/-- The executable's TLS segment (`PT_TLS`) and its `STT_TLS` symbols (offsets in the segment). -/\n")
		fmt.Fprintf(sb, "def tls : TLSImage :=\n  { size := %d, align := %d, init := ", x.TLS.Size, x.TLS.Align)
		writeBytesList(sb, x.TLS.Init, "  ")
		sb.WriteString(",\n    vars := [")
		for i, v := range x.TLS.Vars {
			if i > 0 {
				sb.WriteString(", ")
			}
			fmt.Fprintf(sb, "(%s, %d, %d)", leanString(v.Name), v.Off, v.Size)
		}
		sb.WriteString("] }\n\n")
	}
}

// goTLSDisp is the FS displacement of Go's TLS g slot (runtime.tlsg) on amd64: its offset in
// the TLS segment minus the segment size rounded up to its alignment (x86-64 TLS variant II:
// the executable's block ends at the thread pointer).
// An internally linked binary has no PT_TLS; there the Go linker puts the slot at FS:-8.
func (b *Binary) goTLSDisp() (int64, bool) {
	if b.cenv == nil || b.GOARCH != "amd64" {
		return 0, false
	}
	if b.cenv.tls == nil {
		return -8, true
	}
	t := b.cenv.tls
	for _, v := range t.Vars {
		if v.Name == "runtime.tlsg" {
			return int64(v.Off) - int64(roundUp(t.Size, t.Align)), true
		}
	}
	return 0, false
}

// roundUp rounds n up to a multiple of a (a = 0 or 1: n).
func roundUp(n, a uint64) uint64 {
	if a <= 1 {
		return n
	}
	return (n + a - 1) / a * a
}

// tlsgDispOffset returns the offset, in the instruction bytes ib, of the 32-bit displacement of
// an absolute FS-segment memory operand (no base, no index) that addresses Go's TLS g slot.
func (b *Binary) tlsgDispOffset(ib []byte, inst x86asm.Inst) (int, bool) {
	d, ok := b.goTLSDisp()
	if !ok {
		return 0, false
	}
	for _, a := range inst.Args {
		m, isMem := a.(x86asm.Mem)
		if !isMem || m.Segment != x86asm.FS || m.Base != 0 || m.Index != 0 || uint32(m.Disp) != uint32(int32(d)) {
			continue
		}
		var enc [4]byte
		binary.LittleEndian.PutUint32(enc[:], uint32(int32(d)))
		if i := bytes.Index(ib, enc[:]); i >= 0 && bytes.LastIndex(ib, enc[:]) == i {
			return i, true
		}
	}
	return 0, false
}

// checkCgoTLS refuses an amd64 extraction that reaches runtime.cgocall in a binary whose Go TLS
// g slot is not at FS:-8: the amd64 cgo contract (Janus.Amd64.FFI.CgoCall, GoResume, cgoClobber)
// and GoABI.TlsG state the slot at FS:-8, which is where the Go linker puts it unless cgo-linked
// C code has __thread variables of its own (then the slot moves down, and FS:-8 is a C
// variable).
//
// On arm64 the same holds for TPIDR_EL0+16 (Janus.FFI.tlsGOffset): runtime.tls_g must be the
// first variable of a TLS segment aligned to at most 16 (AArch64 variant I: the executable's
// block starts at the thread pointer plus the 16-byte TCB, rounded up to the alignment).
func checkCgoTLS(b *Binary, x *Extraction) error {
	d, ok := b.goTLSDisp()
	want := int64(-8)
	if b.GOARCH == "arm64" {
		ok, want = false, 16
		if t := b.cenv.tls; t != nil {
			for _, v := range t.Vars {
				if v.Name == "runtime.tls_g" {
					d, ok = int64(roundUp(16, t.Align)+v.Off), true
				}
			}
		}
	}
	if !ok || d == want {
		return nil
	}
	for _, s := range x.Stubs {
		if s.Name == "runtime.cgocall" {
			return &diag{
				Msg:   fmt.Sprintf("%s reaches runtime.cgocall, but in %s Go's TLS g slot is at thread pointer %+d, not %+d: the binary's C code has __thread variables. The cgo contract (Janus.FFI.CgoCall, Janus.Amd64.FFI.CgoCall) states the slot at %+d, so it does not describe this binary", x.Entry.Name, b.Path, d, want, want),
				Stage: "code extraction",
				Next:  "Move the C __thread variables into another binary, or extract the C function directly (its TLS accesses are modelled by Janus.Contracts.TLS).",
			}
		}
	}
	return nil
}
