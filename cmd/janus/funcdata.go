package main

import (
	"encoding/binary"
	"fmt"
	"sort"
	"strings"
)

// The function metadata the Go 1.26 panic runtime reads (runtime/panic.go, traceback.go,
// symtab.go): for a frame of function f, `initOpenCodedDefers` reads f's
// FUNCDATA_OpenCodedDeferInfo (two varints: the deferBits slot and the first closure slot, as
// byte offsets below the frame's varp), `recovery` resumes at `f.entry() + f._func.deferreturn`,
// and the unwinder finds the frame's size (the caller's SP, from which varp is computed) in the
// pcsp table. `janus extract` reads these from the binary's .gopclntab for every extracted
// function when the extraction leaves the panic runtime (`runtime.gopanic`, `runtime.Goexit`,
// `runtime.deferreturn`) out as a contract, and renders them as `Extracted.funcs`
// (`Janus.Spec.FuncInfo`), so a theorem names the funcdata the runtime uses by
// `Extracted.funcs`, not by numbers it states itself (docs/RUNTIME-CONTRACTS.md, "Panics,
// defer, recover"). `janus check` regenerates them from the binary like every other part of
// Extracted.lean.

// FuncInfo is the panic runtime's view of one extracted function.
type FuncInfo struct {
	Name  string
	Entry uint64
	Size  uint64
	// Frame is the function's frame size: the pcsp value (SP delta from the entry SP) everywhere
	// a frame is established. The pcsp table of every accepted function takes only the values
	// 0 (no frame: the prologue before the frame is pushed, the epilogue after it is popped,
	// the morestack call) and Frame.
	Frame uint64
	// DeferReturn is _func.deferreturn: the offset from Entry of the start of the deferreturn
	// call instruction (0 if the function has none).
	DeferReturn uint64
	// OpenDefer reports FUNCDATA_OpenCodedDeferInfo: BitsOff and SlotsOff are its two varints.
	OpenDefer bool
	BitsOff   uint64
	SlotsOff  uint64
}

// panicFuncdataContracts are the contracts whose statements read the function metadata.
var panicFuncdataContracts = map[string]bool{
	"runtime.gopanic": true, "runtime.Goexit": true, "runtime.deferreturn": true,
}

// wantsFuncInfos reports whether the extraction's contracts include the panic runtime.
func wantsFuncInfos(x *Extraction) bool {
	for _, c := range x.Contracts {
		if panicFuncdataContracts[c.Name] {
			return true
		}
	}
	return false
}

// pclnFuncs locates the Go 1.20+ pclntab: the functab (entry offsets from runtime.text and
// _func offsets) and the tables the _func records point into.
type pclnFuncs struct {
	data      []byte // .gopclntab
	ptrSize   int
	pctab     uint64 // offset of pctab in data
	pcln      uint64 // offset of the functab / _func area in data
	nfunc     int
	gofunc    uint64 // address of go:func.* (moduledata.gofunc)
	textStart uint64 // runtime.text
}

func (b *Binary) pclnFuncTable() (*pclnFuncs, error) {
	var data []byte
	for _, s := range b.sections {
		if s.Name == ".gopclntab" && s.data != nil {
			data = s.data
		}
	}
	if len(data) < 8 {
		return nil, fmt.Errorf("no .gopclntab section")
	}
	if m := binary.LittleEndian.Uint32(data); m != 0xfffffff1 {
		return nil, fmt.Errorf(".gopclntab magic 0x%x is not the Go 1.20+ format", m)
	}
	ps := int(data[7])
	if ps != 8 {
		return nil, fmt.Errorf(".gopclntab pointer size %d", ps)
	}
	word := func(i int) uint64 { return binary.LittleEndian.Uint64(data[8+i*8:]) }
	if len(data) < 8+8*8 {
		return nil, fmt.Errorf(".gopclntab header truncated")
	}
	// pcHeader: magic, pad1, pad2, minLC, ptrSize; nfunc, nfiles, (unused), funcnameOffset,
	// cuOffset, filetabOffset, pctabOffset, pclnOffset.
	t := &pclnFuncs{data: data, ptrSize: ps, nfunc: int(word(0)), pctab: word(6), pcln: word(7)}
	gofunc, ok := b.markerAddr("go:func.*")
	if !ok {
		if ds, ok2 := b.dataSymbol("go:func.*"); ok2 {
			gofunc, ok = ds.Addr, true
		}
	}
	if !ok {
		return nil, fmt.Errorf("no go:func.* symbol (moduledata.gofunc)")
	}
	t.gofunc = gofunc
	t.textStart = b.goText
	if t.pcln+uint64(t.nfunc+1)*8 > uint64(len(data)) || t.pctab > uint64(len(data)) {
		return nil, fmt.Errorf(".gopclntab offsets out of range")
	}
	return t, nil
}

// funcRecord returns the offset in data of the _func of the function at addr.
func (t *pclnFuncs) funcRecord(addr uint64) (uint64, bool) {
	if addr < t.textStart {
		return 0, false
	}
	off := addr - t.textStart
	ent := func(i int) (uint32, uint32) {
		p := t.pcln + uint64(i)*8
		return binary.LittleEndian.Uint32(t.data[p:]), binary.LittleEndian.Uint32(t.data[p+4:])
	}
	i := sort.Search(t.nfunc, func(i int) bool { e, _ := ent(i); return uint64(e) > off }) - 1
	if i < 0 {
		return 0, false
	}
	e, fo := ent(i)
	if uint64(e) != off {
		return 0, false
	}
	return t.pcln + uint64(fo), true
}

// varint reads an unsigned LEB128 varint (runtime.readvarint).
func varint(p []byte) (uint64, int, bool) {
	var v uint64
	var shift uint
	for i, c := range p {
		if shift > 56 {
			return 0, 0, false
		}
		v |= uint64(c&0x7f) << shift
		if c < 0x80 {
			return v, i + 1, true
		}
		shift += 7
	}
	return 0, 0, false
}

// pcValues decodes the pc-value table at pctab+off (runtime.step): (start offset from the
// entry, end offset, value) triples covering the function.
func (t *pclnFuncs) pcValues(off uint32, minLC uint64) ([][3]int64, error) {
	if off == 0 {
		return nil, nil
	}
	p := t.data[t.pctab+uint64(off):]
	var out [][3]int64
	var pc, val int64
	val = -1
	first := true
	for {
		uv, n, ok := varint(p)
		if !ok {
			return nil, fmt.Errorf("bad pc-value table")
		}
		if uv == 0 && !first {
			return out, nil
		}
		p = p[n:]
		d := int64(uv >> 1)
		if uv&1 != 0 {
			d = ^d
		}
		val += d
		pd, n, ok := varint(p)
		if !ok {
			return nil, fmt.Errorf("bad pc-value table")
		}
		p = p[n:]
		out = append(out, [3]int64{pc, pc + int64(pd*minLC), val})
		pc += int64(pd * minLC)
		first = false
	}
}

// funcInfo reads the panic-runtime metadata of the function f.
func (b *Binary) funcInfo(t *pclnFuncs, f Func) (FuncInfo, error) {
	fi := FuncInfo{Name: f.Name, Entry: f.Addr, Size: f.Size}
	rec, ok := t.funcRecord(f.Addr)
	if !ok {
		return fi, fmt.Errorf("%s: no pclntab entry at 0x%x", f.Name, f.Addr)
	}
	d := t.data
	if rec+44 > uint64(len(d)) {
		return fi, fmt.Errorf("%s: _func truncated", f.Name)
	}
	u32 := func(o uint64) uint32 { return binary.LittleEndian.Uint32(d[rec+o:]) }
	fi.DeferReturn = uint64(u32(12))
	pcsp := u32(16)
	npcdata := uint64(u32(28))
	nfuncdata := uint64(d[rec+43])
	minLC := uint64(d[6])
	vals, err := t.pcValues(pcsp, minLC)
	if err != nil {
		return fi, fmt.Errorf("%s: pcsp: %v", f.Name, err)
	}
	// On amd64 the frame pointer is pushed first (SP delta 8) and popped last, so the delta
	// takes the value 8 in the prologue and the epilogue and the frame size in the body: the
	// frame size is the one other value.
	var maxv int64
	for _, v := range vals {
		if v[2] > maxv {
			maxv = v[2]
		}
	}
	for _, v := range vals {
		if v[2] < 0 {
			return fi, fmt.Errorf("%s: negative pcsp value %d", f.Name, v[2])
		}
		if v[2] != 0 {
			if b.GOARCH == "amd64" && v[2] == 8 && maxv > 8 {
				continue
			}
			if fi.Frame != 0 && uint64(v[2]) != fi.Frame {
				return fi, fmt.Errorf("%s: pcsp takes two non-zero values (%d, %d); the panic contracts need one frame size", f.Name, fi.Frame, v[2])
			}
			fi.Frame = uint64(v[2])
		}
	}
	const openCodedDeferInfo = 4
	if nfuncdata > openCodedDeferInfo {
		p := rec + 44 + 4*npcdata + 4*openCodedDeferInfo
		if p+4 > uint64(len(d)) {
			return fi, fmt.Errorf("%s: funcdata truncated", f.Name)
		}
		if off := binary.LittleEndian.Uint32(d[p:]); off != ^uint32(0) {
			addr := t.gofunc + uint64(off)
			sec, ok := b.sectionOf(addr)
			if !ok || sec.data == nil || addr >= sec.End() {
				return fi, fmt.Errorf("%s: FUNCDATA_OpenCodedDeferInfo at 0x%x is not in a section with contents", f.Name, addr)
			}
			raw := sec.data[addr-sec.Addr:]
			bits, n, ok1 := varint(raw)
			slots, _, ok2 := varint(raw[n:])
			if !ok1 || !ok2 {
				return fi, fmt.Errorf("%s: bad FUNCDATA_OpenCodedDeferInfo", f.Name)
			}
			if fi.DeferReturn == 0 {
				return fi, fmt.Errorf("%s: open-coded defers without a deferreturn call", f.Name)
			}
			fi.OpenDefer, fi.BitsOff, fi.SlotsOff = true, bits, slots
		}
	}
	return fi, nil
}

// panicFuncInfos reads the metadata of every extracted function (entry first, in segment order)
// for an extraction whose contracts include the panic runtime; nil otherwise.
func (b *Binary) panicFuncInfos(x *Extraction) ([]FuncInfo, error) {
	if !wantsFuncInfos(x) {
		return nil, nil
	}
	t, err := b.pclnFuncTable()
	if err != nil {
		return nil, &diag{Msg: "cannot read the function metadata the panic runtime uses: " + err.Error(),
			Stage: "funcdata", Next: "Use an unmodified, unstripped Go 1.26 executable."}
	}
	var out []FuncInfo
	for _, s := range x.Segments {
		f, ok := b.containing(s.Base)
		if !ok || f.Addr != s.Base || strings.HasPrefix(s.Name, ".") {
			continue
		}
		fi, err := b.funcInfo(t, f)
		if err != nil {
			return nil, &diag{Msg: "cannot read the function metadata the panic runtime uses: " + err.Error(),
				Stage: "funcdata", Next: "The panic contracts need Go 1.26 pclntab metadata for every extracted function."}
		}
		fi.Size = s.Size
		out = append(out, fi)
	}
	return out, nil
}

// writeFuncInfos renders `def funcs` (only for extractions with a panic-runtime contract).
func writeFuncInfos(sb *strings.Builder, fs []FuncInfo) {
	if len(fs) == 0 {
		return
	}
	sb.WriteString("/-- The function metadata the panic runtime reads (from .gopclntab: the frame size of the pcsp\n")
	sb.WriteString("table, `_func.deferreturn`, `FUNCDATA_OpenCodedDeferInfo`). -/\n")
	sb.WriteString("def funcs : List Spec.FuncInfo := [")
	for i, f := range fs {
		if i > 0 {
			sb.WriteString(",")
		}
		od := "none"
		if f.OpenDefer {
			od = fmt.Sprintf("some (%d, %d)", f.BitsOff, f.SlotsOff)
		}
		fmt.Fprintf(sb, "\n  { name := %s, entry := 0x%x, size := %d, frame := %d, deferreturn := 0x%x,\n    openDefer := %s }",
			leanString(f.Name), f.Entry, f.Size, f.Frame, f.DeferReturn, od)
	}
	sb.WriteString(" ]\n\n")
}
