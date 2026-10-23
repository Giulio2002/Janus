// Package gen classifies AArch64 instruction words into encoding classes, builds test
// states for them, and generates randomised encodings per class.
//
// The classifier only looks at the fixed opcode bits of the top-level A64 encoding tables
// (Arm ARM C4.1); it never decides what an instruction does. It exists to (a) group the
// results, (b) pick register values that make memory accesses land in the data buffer and
// register branches land in the code page, and (c) drop SIMD/FP and system encodings.
package gen

// Class names, in the order the report prints them.
var Classes = []string{
	"dpi.pcrel", "dpi.addsub", "dpi.logical", "dpi.movewide", "dpi.bitfield", "dpi.extract", "dpi.other",
	"br.imm", "br.cond", "br.cmp", "br.test", "br.reg", "br.other",
	"dpr.logical", "dpr.addsub", "dpr.addsubext", "dpr.adc", "dpr.ccmp", "dpr.csel",
	"dpr.dp1", "dpr.dp2", "dpr.dp3", "dpr.other",
	"ls.uimm", "ls.imm9", "ls.regoff", "ls.pair", "ls.literal", "ls.excl", "ls.atomic", "ls.other",
	"sys.hint", "sys.barrier", "sys.mrs", "sys.sys", "system", "simd", "reserved",
}

// Classify returns the encoding class of w.
func Classify(w uint32) string {
	switch {
	case w&0x18000000 == 0: // op0 = 00xx: reserved, SME, SVE
		return "reserved"
	case w&0x1C000000 == 0x10000000: // op0 = 100x: data processing, immediate
		switch {
		case w&0x1F000000 == 0x10000000:
			return "dpi.pcrel"
		case w&0x1F800000 == 0x11000000:
			return "dpi.addsub"
		case w&0x1F800000 == 0x12000000:
			return "dpi.logical"
		case w&0x1F800000 == 0x12800000:
			return "dpi.movewide"
		case w&0x1F800000 == 0x13000000:
			return "dpi.bitfield"
		case w&0x1F800000 == 0x13800000:
			return "dpi.extract"
		}
		return "dpi.other"
	case w&0x1C000000 == 0x14000000: // op0 = 101x: branches, exception generation, system
		switch {
		case w&0x7C000000 == 0x14000000:
			return "br.imm"
		case w&0xFF000000 == 0x54000000:
			return "br.cond"
		case w&0x7E000000 == 0x34000000:
			return "br.cmp"
		case w&0x7E000000 == 0x36000000:
			return "br.test"
		case w&0xFE000000 == 0xD6000000:
			return "br.reg"
		case w&0xFFFFF01F == 0xD503201F: // HINT (NOP, YIELD, BTI, PAC*SP, ...)
			return "sys.hint"
		case w&0xFFFFF01F == 0xD503301F: // CLREX, DSB, DMB, ISB, SB
			return "sys.barrier"
		case w&0xFFF00000 == 0xD5300000: // MRS (system register reads, e.g. DCZID_EL0)
			return "sys.mrs"
		case w&0xFFF8F000 == 0xD5087000: // SYS #op1, C7, Cm, #op2: cache maintenance (DC ZVA, ...)
			return "sys.sys"
		case w&0xFE000000 == 0xD4000000: // exception generation, other system
			return "system"
		}
		return "br.other"
	case w&0x0E000000 == 0x0A000000: // op0 = x101: data processing, register
		switch {
		case w&0x1F000000 == 0x0A000000:
			return "dpr.logical"
		case w&0x1F200000 == 0x0B000000:
			return "dpr.addsub"
		case w&0x1F200000 == 0x0B200000:
			return "dpr.addsubext"
		case w&0x1FE00000 == 0x1A000000:
			return "dpr.adc"
		case w&0x1FE00000 == 0x1A400000:
			return "dpr.ccmp"
		case w&0x1FE00000 == 0x1A800000:
			return "dpr.csel"
		case w&0x5FE00000 == 0x1AC00000:
			return "dpr.dp2"
		case w&0x5FE00000 == 0x5AC00000:
			return "dpr.dp1"
		case w&0x1F000000 == 0x1B000000:
			return "dpr.dp3"
		}
		return "dpr.other"
	case w&0x0E000000 == 0x0E000000: // op0 = x111: SIMD and FP data processing
		return "simd"
	case w&0x0A000000 == 0x08000000: // op0 = x1x0: loads and stores
		if w&0x04000000 != 0 {
			return "simd"
		}
		switch {
		case w&0x3F000000 == 0x08000000:
			return "ls.excl"
		case w&0x3B000000 == 0x18000000:
			return "ls.literal"
		case w&0x3A000000 == 0x28000000:
			return "ls.pair"
		case w&0x3B000000 == 0x39000000:
			return "ls.uimm"
		case w&0x3B200000 == 0x38000000:
			return "ls.imm9"
		case w&0x3B200C00 == 0x38200000:
			return "ls.atomic"
		case w&0x3B200C00 == 0x38200800:
			return "ls.regoff"
		}
		return "ls.other"
	}
	return "reserved"
}

// Tested reports whether the class is in scope (not SIMD/FP, not system other than MRS and
// the C7 cache-maintenance SYS space).
func Tested(class string) bool {
	return class != "simd" && class != "system"
}

// Conditional reports whether the result of the class depends on NZCV, so each word is
// run under all 16 flag combinations.
func Conditional(class string) bool {
	switch class {
	case "br.cond", "dpr.ccmp", "dpr.csel", "dpr.adc":
		return true
	}
	return false
}

func bits(w uint32, hi, lo int) uint32 { return (w >> lo) & (1<<(hi-lo+1) - 1) }

// Unpredictable reports encodings that are CONSTRAINED UNPREDICTABLE in a way that lets
// real implementations differ (writeback with Rt == Rn, load pair with Rt == Rt2,
// store-exclusive status register overlapping its operands, CASP with odd registers).
// The generator never emits them; harvested ones are tagged, and their verdicts are
// reported separately.
func Unpredictable(w uint32) bool {
	rt, rn, rt2, rs := bits(w, 4, 0), bits(w, 9, 5), bits(w, 14, 10), bits(w, 20, 16)
	switch Classify(w) {
	case "ls.imm9":
		idx := bits(w, 11, 10)
		return (idx == 1 || idx == 3) && rt == rn && rn != 31
	case "ls.pair":
		load := bits(w, 22, 22) == 1
		idx := bits(w, 24, 23)
		if load && rt == rt2 {
			return true
		}
		return (idx == 1 || idx == 3) && rn != 31 && (rn == rt || rn == rt2)
	case "ls.excl":
		o2, l, o1 := bits(w, 23, 23), bits(w, 22, 22), bits(w, 21, 21)
		if o2 == 0 && o1 == 1 { // CASP / exclusive pair
			sz := bits(w, 31, 30)
			if sz < 2 && w&0x00007C00 == 0x00007C00 { // CASP: Rt2 == 11111
				return rs%2 == 1 || rt%2 == 1
			}
			if l == 1 && rt == rt2 { // LDXP / LDAXP
				return true
			}
			if l == 0 && (rs == rt || rs == rt2 || rs == rn && rn != 31) { // STXP
				return true
			}
			return false
		}
		if o2 == 0 && o1 == 0 && l == 0 { // STXR / STLXR
			return rs == rt || rs == rn && rn != 31
		}
	}
	return false
}
