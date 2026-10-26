package main

// Read-only data the extracted code loads: untrusted detection, trusted byte copy.
//
// Go code materialises the address of a global with ADRP+ADD (`MOVD $sym(SB), R`), loads it
// with ADRP+LDR/LDP (`MOVD sym(SB), R`), and occasionally uses ADR or a PC-relative literal
// LDR. dataRefs finds these address computations with golang.org/x/arch/arm64/arm64asm. Like
// reachability, this only decides *which* bytes to copy: if a reference is missed, the bytes
// are absent from Program.data, the precondition `Program.DataLoaded` does not provide them,
// and the access faults as outside every allocation, which is sound. What is trusted is the
// copy itself: the bytes at [base, base+len) of an allocated, non-writable ELF section.
//
// Only read-only sections are copied. Writable data (.noptrdata, .data, .bss, .noptrbss, and
// anything else with SHF_WRITE) is reported, not copied: its run-time content is not fixed by
// the binary. .gopclntab is never copied (it is runtime metadata, not program data).

import (
	"encoding/binary"
	"fmt"
	"regexp"
	"sort"
	"strconv"
	"strings"

	"golang.org/x/arch/arm64/arm64asm"
)

const (
	// A whole data symbol is copied up to this size; larger symbols get a window.
	maxDataSymbol = 4096
	// Bounded window copied when no symbol covers the address, or the symbol is too large.
	dataWindow = 256
)

// DataRef is one detected address computation or PC-relative load in extracted code.
type DataRef struct {
	From   uint64 // address of the instruction that completes the computation
	Target uint64
	Kind   string // "adrp+add", "adrp+ldst", "adr", "ldr-literal"
}

// DataSeg is one copied read-only object (Janus.DataSegment).
type DataSeg struct {
	Name    string
	Base    uint64
	Bytes   []byte
	Section string
}

// SkippedData is a reference whose target is not copied, and why.
type SkippedData struct {
	DataRef
	Section string // "" when the address is in no allocated section
	Symbol  string
	Reason  string // "writable", "gopclntab", "code", "unmapped"
}

var (
	memImmRE   = regexp.MustCompile(`#(-?\d+)\]`)
	immShiftRE = regexp.MustCompile(`^#(0x[0-9a-f]+|\d+)(?:, LSL #(\d+))?$`)
)

// regNo returns the general-purpose register number (0..30) of a register argument and
// whether it is a 64-bit X register. SP/XZR/WZR and non-integer registers return ok = false.
func regNo(a arm64asm.Arg) (n int, x bool, ok bool) {
	switch r := a.(type) {
	case arm64asm.Reg:
		switch {
		case r >= arm64asm.X0 && r <= arm64asm.X30:
			return int(r - arm64asm.X0), true, true
		case r >= arm64asm.W0 && r <= arm64asm.W30:
			return int(r - arm64asm.W0), false, true
		}
	case arm64asm.RegSP:
		rr := arm64asm.Reg(r)
		switch {
		case rr >= arm64asm.X0 && rr <= arm64asm.X30:
			return int(rr - arm64asm.X0), true, true
		case rr >= arm64asm.W0 && rr <= arm64asm.W30:
			return int(rr - arm64asm.W0), false, true
		}
	}
	return 0, false, false
}

// memOffset returns the base register and byte offset of an [Xn, #imm] operand, or ok = false.
// With pre/post-index writeback, wb is true. arm64asm does not export the immediate, so it is
// read from the operand's text (this decoding is untrusted).
func memOffset(m arm64asm.MemImmediate) (base int, off int64, wb bool, ok bool) {
	n, x, ok := regNo(m.Base)
	if !ok || !x {
		return 0, 0, false, false
	}
	switch m.Mode {
	case arm64asm.AddrOffset:
	case arm64asm.AddrPreIndex:
		wb = true
	case arm64asm.AddrPostIndex:
		return n, 0, true, true
	default:
		return 0, 0, false, false
	}
	if g := memImmRE.FindStringSubmatch(m.String()); g != nil {
		off, _ = strconv.ParseInt(g[1], 10, 64)
	}
	return n, off, wb, true
}

func isLoadStore(op arm64asm.Op) bool {
	s := op.String()
	return strings.HasPrefix(s, "LD") || strings.HasPrefix(s, "ST") || s == "PRFM" || s == "PRFUM"
}

// dataRefs scans one function's words for references to fixed addresses. It tracks, within
// straight-line code, registers holding a known address (from ADRP, then ADD #imm); state is
// dropped at every branch, branch target and call, and for every register an instruction may
// write. Losing a reference is sound (see the file comment); a spurious one only copies or
// reports extra read-only bytes.
func dataRefs(ws []uint32, base uint64) []DataRef {
	end := base + 4*uint64(len(ws))
	labels := map[uint64]bool{}
	for i, w := range ws {
		if t, ok := branchTarget(w, base+4*uint64(i)); ok && t >= base && t < end {
			labels[t] = true
		}
	}
	var known [31]*uint64
	clear := func() { known = [31]*uint64{} }
	set := func(r int, v uint64) { known[r] = &v }
	var refs []DataRef
	var buf [4]byte
	for i, w := range ws {
		pc := base + 4*uint64(i)
		if labels[pc] {
			clear()
		}
		binary.LittleEndian.PutUint32(buf[:], w)
		inst, err := arm64asm.Decode(buf[:])
		if err != nil {
			clear()
			continue
		}
		args := inst.Args[:]
		for len(args) > 0 && args[len(args)-1] == nil {
			args = args[:len(args)-1]
		}
		// Destination registers this instruction may write; cleared after it unless set.
		var writes []int
		defer0 := func() {
			for _, r := range writes {
				known[r] = nil
			}
		}
		switch op := inst.Op; {
		case op == arm64asm.ADRP || op == arm64asm.ADR:
			rd, x, ok := regNo(args[0])
			rel, isRel := args[1].(arm64asm.PCRel)
			if !ok || !x || !isRel {
				if ok {
					writes = append(writes, rd)
				}
				break
			}
			t := uint64(int64(pc) + int64(rel))
			if op == arm64asm.ADRP {
				t = uint64(int64(pc&^0xfff) + int64(rel))
				set(rd, t)
			} else {
				refs = append(refs, DataRef{From: pc, Target: t, Kind: "adr"})
				set(rd, t)
			}
			continue
		case op == arm64asm.ADD && len(args) == 3:
			rd, xd, ok1 := regNo(args[0])
			rn, xn, ok2 := regNo(args[1])
			imm, isImm := args[2].(arm64asm.ImmShift)
			if ok1 && ok2 && xd && xn && isImm && known[rn] != nil {
				if g := immShiftRE.FindStringSubmatch(imm.String()); g != nil {
					v, _ := strconv.ParseUint(g[1], 0, 64)
					if g[2] != "" {
						sh, _ := strconv.Atoi(g[2])
						v <<= uint(sh)
					}
					t := *known[rn] + v
					refs = append(refs, DataRef{From: pc, Target: t, Kind: "adrp+add"})
					set(rd, t)
					continue
				}
			}
			if ok1 {
				writes = append(writes, rd)
			}
		case (op == arm64asm.LDR || op == arm64asm.LDRSW) && len(args) == 2:
			if rel, ok := args[1].(arm64asm.PCRel); ok {
				refs = append(refs, DataRef{From: pc, Target: uint64(int64(pc) + int64(rel)), Kind: "ldr-literal"})
				if rd, _, ok := regNo(args[0]); ok {
					writes = append(writes, rd)
				}
				break
			}
			fallthrough
		case isLoadStore(op):
			for _, a := range args {
				if m, ok := a.(arm64asm.MemImmediate); ok {
					if rn, off, wb, ok := memOffset(m); ok {
						if known[rn] != nil {
							refs = append(refs, DataRef{From: pc, Target: uint64(int64(*known[rn]) + off), Kind: "adrp+ldst"})
						}
						if wb {
							writes = append(writes, rn)
						}
					} else if rn, _, ok := regNo(m.Base); ok {
						writes = append(writes, rn)
					}
				} else if _, ok := a.(arm64asm.MemExtend); ok {
					// [Xn, Xm, LSL #k]: base plus a run-time index; not a fixed address.
				} else { // transfer registers (destinations of loads)
					if r, _, ok := regNo(a); ok {
						writes = append(writes, r)
					}
				}
			}
		case op == arm64asm.BL || op == arm64asm.BLR:
			clear()
			continue
		default:
			if _, ok := branchTarget(w, pc); ok || op == arm64asm.BR || op == arm64asm.RET {
				clear()
				continue
			}
			for _, a := range args {
				if r, _, ok := regNo(a); ok {
					writes = append(writes, r)
				}
			}
		}
		defer0()
	}
	return refs
}

func (b *Binary) sectionOf(addr uint64) (section, bool) {
	for _, s := range b.sections {
		if addr >= s.Addr && addr < s.End() {
			return s, true
		}
	}
	return section{}, false
}

// dataSymbolAt returns the data symbol containing addr, and the start of the next data
// symbol after addr (or ^0).
func (b *Binary) dataSymbolAt(addr uint64) (Func, bool, uint64) {
	i := sort.Search(len(b.dataSyms), func(i int) bool { return b.dataSyms[i].Addr > addr })
	next := ^uint64(0)
	if i < len(b.dataSyms) {
		next = b.dataSyms[i].Addr
	}
	// Symbols can nest or overlap; take the smallest one that contains addr.
	var best Func
	found := false
	for j := i - 1; j >= 0 && j >= i-64; j-- {
		s := b.dataSyms[j]
		if addr >= s.Addr && addr < s.End() && (!found || s.Size < best.Size) {
			best, found = s, true
		}
	}
	return best, found, next
}

// collectData resolves references into copied read-only objects and skipped references.
// Overlapping or adjacent objects are merged; the result is sorted by address.
// extra are references not made by the code (dynamic targets named with --targets); they are
// copied like code references but not reported as such.
func collectData(b *Binary, refs []DataRef, extra ...DataRef) ([]DataSeg, []SkippedData) {
	type span struct {
		name, sec  string
		start, end uint64
		// a whole static itab or funcval: kept as its own segment under its symbol name, so a
		// specification can name it (Janus.Spec.ItabIs, dynamic.go)
		atomic bool
	}
	var spans []span
	var skipped []SkippedData
	seenSkip := map[[2]uint64]bool{}
	for _, r := range append(append([]DataRef(nil), refs...), extra...) {
		sec, ok := b.sectionOf(r.Target)
		sym, hasSym, next := b.dataSymbolAt(r.Target)
		skip := func(reason string) {
			k := [2]uint64{r.From, r.Target}
			if seenSkip[k] {
				return
			}
			seenSkip[k] = true
			sd := SkippedData{DataRef: r, Reason: reason}
			if ok {
				sd.Section = sec.Name
			}
			if hasSym {
				sd.Symbol = sym.Name
			}
			skipped = append(skipped, sd)
		}
		switch {
		case !ok:
			skip("unmapped")
			continue
		case sec.Writable && b.staticGOT(r.Target&^7) && r.Target%8 == 0:
			// a GOT slot the dynamic linker never writes, read-only after RELRO (cenv.go)
		case sec.Writable:
			skip("writable")
			continue
		case sec.Name == ".gopclntab":
			skip("gopclntab")
			continue
		case sec.Exec && r.Kind != "ldr-literal":
			// A code address (e.g. a function value); the code itself is a segment, not data.
			skip("code")
			continue
		}
		var sp span
		switch {
		case sec.Writable: // a static GOT slot
			sp = span{b.gotName(r.Target), sec.Name, r.Target, r.Target + 8, true}
		case sec.Exec: // literal pool word in .text
			sp = span{fmt.Sprintf("%s+0x%x", sec.Name, r.Target-sec.Addr), sec.Name, r.Target, r.Target + 8, false}
		case hasSym && sym.Size <= maxDataSymbol:
			_, _, isCode := b.codeWords(sym)
			sp = span{sym.Name, sec.Name, sym.Addr, sym.End(), isCode}
		case hasSym:
			sp = span{fmt.Sprintf("%s+0x%x", sym.Name, r.Target-sym.Addr), sec.Name, r.Target, min(r.Target+dataWindow, sym.End()), false}
		default:
			sp = span{fmt.Sprintf("%s+0x%x", sec.Name, r.Target-sec.Addr), sec.Name, r.Target, min(r.Target+dataWindow, next), false}
		}
		sp.start = max(sp.start, sec.Addr)
		sp.end = min(sp.end, sec.End())
		if sp.end > sp.start {
			spans = append(spans, sp)
		}
	}
	sort.SliceStable(spans, func(i, j int) bool {
		if spans[i].start != spans[j].start {
			return spans[i].start < spans[j].start
		}
		return spans[i].end > spans[j].end
	})
	var merged []span
	for _, sp := range spans {
		if n := len(merged); n > 0 && merged[n-1].atomic && sp.atomic && sp.start == merged[n-1].start && sp.end == merged[n-1].end {
			continue
		}
		if n := len(merged); n > 0 && sp.start <= merged[n-1].end && sp.sec == merged[n-1].sec &&
			!((sp.atomic || merged[n-1].atomic) && sp.start >= merged[n-1].end) {
			merged[n-1].end = max(merged[n-1].end, sp.end)
			continue
		}
		merged = append(merged, sp)
	}
	var segs []DataSeg
	for _, sp := range merged {
		sec, _ := b.sectionOf(sp.start)
		bytes := append([]byte(nil), sec.data[sp.start-sec.Addr:sp.end-sec.Addr]...)
		segs = append(segs, DataSeg{Name: sp.name, Base: sp.start, Bytes: bytes, Section: sp.sec})
	}
	return segs, skipped
}
