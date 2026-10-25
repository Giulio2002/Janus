package main

// Frame records (R7, stack growth): what the Go runtime's unwinder and stack copier read about
// each function from the pclntab (runtime/symtab.go, stkframe.go, stack.go): its SP delta at
// each pc (pcsp), the stack-map index at each pc (PCDATA_StackMapIndex), the argument and local
// pointer maps (FUNCDATA_ArgsPointerMaps, FUNCDATA_LocalsPointerMaps), the stack objects
// (FUNCDATA_StackObjects), the argument size, flags and FuncID. `janus extract --frames`
// renders them as `Extracted.frames`; a stack-growth theorem assumes its frame table agrees
// with them (`Janus.Spec.Stack.FrameTable.Agrees`), so the stack maps a proof relies on are
// the binary's own, checked by `janus check` like the code.

import (
	"encoding/binary"
	"fmt"
	"strings"
)

// pcRun is a run of a pc-value table: Value holds for the pcs below Limit (and at or above the
// previous run's Limit, the function's entry for the first run).
type pcRun struct {
	Limit uint64
	Value int64
}

type stackObj struct {
	Off  int32
	Ptrs []bool
}

// FrameRec is one function's unwinding and stack-map information.
type FrameRec struct {
	Name      string
	Entry     uint64
	Size      uint64
	Args      int32
	FuncID    uint8
	Flag      uint8
	MaxSPD    int64
	PCSP      []pcRun
	StackIdx  []pcRun
	ArgMaps   [][]bool
	LocalMaps [][]bool
	Objs      []stackObj
}

// pclnHeader is the Go 1.20+ pcHeader (runtime/symtab.go) for a 64-bit binary.
type pclnHeader struct {
	quantum   uint64
	nfunc     uint64
	textStart uint64
	pctabOff  uint64
	pclnOff   uint64
}

func (b *Binary) pclnData() ([]byte, error) {
	for _, s := range b.sections {
		if s.Name == ".gopclntab" && s.data != nil {
			return s.data, nil
		}
	}
	return nil, fmt.Errorf("no .gopclntab section")
}

func readPclnHeader(d []byte) (pclnHeader, error) {
	if len(d) < 72 || binary.LittleEndian.Uint32(d) != 0xfffffff1 || d[7] != 8 {
		return pclnHeader{}, fmt.Errorf("not a Go 1.20+ 64-bit pclntab")
	}
	u := func(off int) uint64 { return binary.LittleEndian.Uint64(d[off:]) }
	// textStart (offset 24) is no longer written by the linker; entries are relative to
	// runtime.text (Binary.goText).
	return pclnHeader{quantum: uint64(d[6]), nfunc: u(8), pctabOff: u(56), pclnOff: u(64)}, nil
}

func uvarint(p []byte) (uint64, int, error) {
	var v uint64
	for i := 0; i < len(p) && i < 10; i++ {
		v |= uint64(p[i]&0x7f) << (7 * uint(i))
		if p[i]&0x80 == 0 {
			return v, i + 1, nil
		}
	}
	return 0, 0, fmt.Errorf("bad varint")
}

// pcTable decodes the pc-value table at off of pctab (runtime.pcvalue / step) into runs.
func pcTable(pctab []byte, off uint32, entry, quantum uint64) ([]pcRun, error) {
	if off == 0 {
		return nil, nil
	}
	if int(off) >= len(pctab) {
		return nil, fmt.Errorf("pc-value table offset out of range")
	}
	p := pctab[off:]
	val, pc := int64(-1), entry
	var runs []pcRun
	for first := true; ; first = false {
		uv, n, err := uvarint(p)
		if err != nil {
			return nil, err
		}
		p = p[n:]
		if uv == 0 && !first {
			return runs, nil
		}
		var dv int64
		if uv&1 != 0 {
			dv = ^int64(uv >> 1)
		} else {
			dv = int64(uv >> 1)
		}
		val += dv
		pd, n, err := uvarint(p)
		if err != nil {
			return nil, err
		}
		p = p[n:]
		pc += pd * quantum
		runs = append(runs, pcRun{pc, val})
		if len(runs) > 1<<20 {
			return nil, fmt.Errorf("pc-value table too long")
		}
	}
}

// readAt copies n bytes at the virtual address addr of a file-backed allocated section.
func (b *Binary) readAt(addr, n uint64) ([]byte, bool) {
	sec, ok := b.sectionOf(addr)
	if !ok || sec.NoBits || sec.data == nil || addr+n > sec.End() {
		return nil, false
	}
	return sec.data[addr-sec.Addr : addr-sec.Addr+n], true
}

// symAddr is the address of the symbol name (a function, data object or marker).
func (b *Binary) symAddr(name string) (uint64, bool) {
	for _, s := range b.dataSyms {
		if s.Name == name {
			return s.Addr, true
		}
	}
	for _, s := range b.markers {
		if s.Name == name {
			return s.Addr, true
		}
	}
	return 0, false
}

// stackMap reads a runtime.stackmap (n int32, nbit int32, n bitmaps of nbit bits) at addr. A
// map with nbit = 0 marks nothing: each of its entries is empty.
func (b *Binary) stackMap(addr uint64) ([][]bool, error) {
	hdr, ok := b.readAt(addr, 8)
	if !ok {
		return nil, fmt.Errorf("stack map at 0x%x is not in the binary", addr)
	}
	n, nbit := int32(binary.LittleEndian.Uint32(hdr)), int32(binary.LittleEndian.Uint32(hdr[4:]))
	if n < 0 || nbit < 0 || n > 1<<16 || nbit > 1<<20 {
		return nil, fmt.Errorf("stack map at 0x%x has %d maps of %d bits", addr, n, nbit)
	}
	per := uint64((nbit + 7) / 8)
	data, ok := b.readAt(addr+8, uint64(n)*per)
	if !ok {
		return nil, fmt.Errorf("stack map at 0x%x is not in the binary", addr)
	}
	maps := make([][]bool, n)
	for i := range maps {
		maps[i] = []bool{}
		for j := int32(0); j < nbit; j++ {
			maps[i] = append(maps[i], data[uint64(i)*per+uint64(j/8)]>>(uint(j)%8)&1 != 0)
		}
	}
	return maps, nil
}

// frameRec reads the frame record of the function at entry from the pclntab.
func (b *Binary) frameRec(f Func) (FrameRec, error) {
	d, err := b.pclnData()
	if err != nil {
		return FrameRec{}, err
	}
	h, err := readPclnHeader(d)
	if err != nil {
		return FrameRec{}, err
	}
	h.textStart = b.goText
	if h.pclnOff+(h.nfunc+1)*8 > uint64(len(d)) || f.Addr < h.textStart {
		return FrameRec{}, fmt.Errorf("pclntab function table out of range")
	}
	ft := d[h.pclnOff:]
	want := uint32(f.Addr - h.textStart)
	funcOff := uint64(0)
	found := false
	for i := uint64(0); i < h.nfunc; i++ {
		if binary.LittleEndian.Uint32(ft[i*8:]) == want {
			funcOff, found = uint64(binary.LittleEndian.Uint32(ft[i*8+4:])), true
			break
		}
	}
	if !found {
		return FrameRec{}, fmt.Errorf("%s at 0x%x has no pclntab entry", f.Name, f.Addr)
	}
	if h.pclnOff+funcOff+44 > uint64(len(d)) {
		return FrameRec{}, fmt.Errorf("pclntab _func of %s out of range", f.Name)
	}
	fn := d[h.pclnOff+funcOff:]
	u32 := func(off int) uint32 { return binary.LittleEndian.Uint32(fn[off:]) }
	npcdata, nfuncdata := u32(28), uint32(fn[43])
	if 44+4*uint64(npcdata+nfuncdata) > uint64(len(fn)) {
		return FrameRec{}, fmt.Errorf("pclntab _func of %s out of range", f.Name)
	}
	pctab := d[h.pctabOff:]
	r := FrameRec{Name: f.Name, Entry: f.Addr, Size: f.Size, Args: int32(u32(8)), FuncID: fn[40], Flag: fn[41]}
	if r.PCSP, err = pcTable(pctab, u32(16), f.Addr, h.quantum); err != nil {
		return FrameRec{}, fmt.Errorf("pcsp of %s: %v", f.Name, err)
	}
	for _, run := range r.PCSP {
		if run.Value > r.MaxSPD {
			r.MaxSPD = run.Value
		}
	}
	if npcdata > 1 {
		if r.StackIdx, err = pcTable(pctab, u32(44+4*1), f.Addr, h.quantum); err != nil {
			return FrameRec{}, fmt.Errorf("stack map index of %s: %v", f.Name, err)
		}
	}
	funcdata := func(i uint32) (uint64, bool, error) {
		if i >= nfuncdata {
			return 0, false, nil
		}
		off := u32(int(44 + 4*npcdata + 4*i))
		if off == ^uint32(0) {
			return 0, false, nil
		}
		base, ok := b.symAddr("go:func.*")
		if !ok {
			return 0, false, fmt.Errorf("no go:func.* symbol")
		}
		return base + uint64(off), true, nil
	}
	for i, dst := range []*[][]bool{&r.ArgMaps, &r.LocalMaps} {
		addr, ok, err := funcdata(uint32(i))
		if err != nil {
			return FrameRec{}, err
		}
		if ok {
			if *dst, err = b.stackMap(addr); err != nil {
				return FrameRec{}, fmt.Errorf("%s: %v", f.Name, err)
			}
		}
	}
	if addr, ok, err := funcdata(2); err != nil {
		return FrameRec{}, err
	} else if ok {
		hdr, ok := b.readAt(addr, 8)
		if !ok {
			return FrameRec{}, fmt.Errorf("stack objects of %s are not in the binary", f.Name)
		}
		n := binary.LittleEndian.Uint64(hdr)
		if n > 1<<12 {
			return FrameRec{}, fmt.Errorf("%s has %d stack objects", f.Name, n)
		}
		rodata, okr := b.symAddr("runtime.rodata")
		for i := uint64(0); i < n; i++ {
			rec, ok := b.readAt(addr+8+16*i, 16)
			if !ok || !okr {
				return FrameRec{}, fmt.Errorf("stack object %d of %s is not readable", i, f.Name)
			}
			off, ptrBytes := int32(binary.LittleEndian.Uint32(rec)), int32(binary.LittleEndian.Uint32(rec[8:]))
			gc := uint64(binary.LittleEndian.Uint32(rec[12:]))
			o := stackObj{Off: off, Ptrs: []bool{}}
			if ptrBytes < 0 || ptrBytes > 1<<20 {
				return FrameRec{}, fmt.Errorf("stack object %d of %s has %d pointer bytes", i, f.Name, ptrBytes)
			}
			words := uint64(ptrBytes) / 8
			bits, ok := b.readAt(rodata+gc, (words+7)/8)
			if !ok {
				return FrameRec{}, fmt.Errorf("stack object %d of %s: pointer bitmap not readable", i, f.Name)
			}
			for w := uint64(0); w < words; w++ {
				o.Ptrs = append(o.Ptrs, bits[w/8]>>(w%8)&1 != 0)
			}
			r.Objs = append(r.Objs, o)
		}
	}
	return r, nil
}

// frameRecs reads the frame records of every extracted function (amd64: also the functions'
// code bytes), in segment order.
func (x *Extraction) frameRecs() ([]FrameRec, error) {
	var recs []FrameRec
	for _, s := range x.Segments {
		size := uint64(4 * len(s.Words))
		if len(s.Bytes) > 0 {
			size = uint64(len(s.Bytes))
		}
		r, err := x.Bin.frameRec(Func{Name: s.Name, Addr: s.Base, Size: size})
		if err != nil {
			return nil, &diag{Msg: fmt.Sprintf("cannot read the frame record of %s: %v", s.Name, err),
				Stage: "frame records (--frames)"}
		}
		recs = append(recs, r)
	}
	return recs, nil
}

func leanBools(bs []bool) string {
	parts := make([]string, len(bs))
	for i, b := range bs {
		parts[i] = fmt.Sprint(b)
	}
	return "[" + strings.Join(parts, ", ") + "]"
}

func leanRuns(rs []pcRun) string {
	parts := make([]string, len(rs))
	for i, r := range rs {
		parts[i] = fmt.Sprintf("(0x%x, %d)", r.Limit, r.Value)
	}
	return "[" + strings.Join(parts, ", ") + "]"
}

// writeFrames renders `def frames` (only with --frames).
func writeFrames(sb *strings.Builder, recs []FrameRec) {
	sb.WriteString("def frames : List Janus.Spec.Stack.FuncRec := [")
	for i, r := range recs {
		if i > 0 {
			sb.WriteString(",")
		}
		maps := func(ms [][]bool) string {
			parts := make([]string, len(ms))
			for j, m := range ms {
				parts[j] = leanBools(m)
			}
			return "[" + strings.Join(parts, ", ") + "]"
		}
		objs := make([]string, len(r.Objs))
		for j, o := range r.Objs {
			objs[j] = fmt.Sprintf("(%d, %s)", o.Off, leanBools(o.Ptrs))
		}
		fmt.Fprintf(sb, "\n  { name := %s, entry := 0x%x, size := %d, args := %d, funcID := %d, flag := %d, maxspd := %d,\n",
			leanString(r.Name), r.Entry, r.Size, r.Args, r.FuncID, r.Flag, r.MaxSPD)
		fmt.Fprintf(sb, "    pcsp := %s,\n    stackIdx := %s,\n    argMaps := %s, localMaps := %s, objs := [%s] }",
			leanRuns(r.PCSP), leanRuns(r.StackIdx), maps(r.ArgMaps), maps(r.LocalMaps), strings.Join(objs, ", "))
	}
	sb.WriteString(" ]\n\n")
}

// applyFrames reads the frame records and renders them into the extraction (`--frames`).
func applyFrames(x *Extraction) error {
	recs, err := x.frameRecs()
	if err != nil {
		return err
	}
	x.Frames, x.FrameRecs = true, recs
	if x.Bin.GOARCH == "amd64" {
		x.Lean = renderLeanAmd64(x)
	} else {
		x.Lean = renderLean(x)
	}
	return nil
}
