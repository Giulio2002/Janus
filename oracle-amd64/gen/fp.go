package gen

import (
	"math/rand/v2"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
	"golang.org/x/arch/x86/x86asm"
)

// SSE scalar floating point: the instruction classes whose states come from the IEEE
// edge-value generator, with the width (32 or 64) of their floating-point source lanes.
// `packed` classes (the bitwise ANDPD/ORPD/...) get edge values in every lane.
type fpInfo struct {
	width  int  // 32 or 64: the floating-point lane width of the XMM operands
	packed bool // fill every lane, not only the low one
	gprSrc bool // CVTSI2SD/SS: the source is an integer register or memory operand
	fma    bool // scalar FMA3 (three sources, setupFMA)
}

var fpClasses = map[string]fpInfo{}

func init() {
	for _, m := range []string{"addsd", "subsd", "mulsd", "divsd", "sqrtsd", "minsd", "maxsd", "ucomisd", "comisd",
		"cvttsd2si", "cvtsd2si", "cvtsd2ss", "roundsd", "cmpsd_xmm", "roundpd", "cmppd", "addpd", "subpd", "mulpd",
		"divpd", "sqrtpd", "minpd", "maxpd", "cvtpd2ps", "cvttpd2dq", "cvtpd2dq"} {
		fpClasses[m] = fpInfo{width: 64}
	}
	for _, m := range []string{"addss", "subss", "mulss", "divss", "sqrtss", "minss", "maxss", "ucomiss", "comiss",
		"cvttss2si", "cvtss2si", "cvtss2sd", "roundss", "cmpss", "roundps", "cmpps", "addps", "subps", "mulps",
		"divps", "sqrtps", "minps", "maxps", "cvtps2pd", "cvttps2dq", "cvtps2dq"} {
		fpClasses[m] = fpInfo{width: 32}
	}
	for _, m := range []string{"andpd", "andnpd", "orpd", "xorpd"} {
		fpClasses[m] = fpInfo{width: 64, packed: true}
	}
	for _, m := range []string{"andps", "andnps", "orps", "xorps"} {
		fpClasses[m] = fpInfo{width: 32, packed: true}
	}
	fpClasses["cvtsi2sd"] = fpInfo{width: 64, gprSrc: true}
	fpClasses["cvtsi2ss"] = fpInfo{width: 32, gprSrc: true}
	// packed lanes for the packed arithmetic neighbours
	for m, i := range fpClasses {
		switch m {
		case "roundpd", "cmppd", "addpd", "subpd", "mulpd", "divpd", "sqrtpd", "minpd", "maxpd", "cvtpd2ps",
			"cvttpd2dq", "cvtpd2dq", "roundps", "cmpps", "addps", "subps", "mulps", "divps", "sqrtps", "minps",
			"maxps", "cvtps2pd", "cvttps2dq", "cvtps2dq":
			i.packed = true
			fpClasses[m] = i
		}
	}
}

// IsFP reports whether cls (a Classify result) is an SSE floating-point class.
func IsFP(cls string) bool { _, ok := fpClasses[cls]; return ok }

// fmtE, fmtF are the exponent and fraction widths of binary32 / binary64.
func fmtEF(width int) (int, int) {
	if width == 32 {
		return 8, 23
	}
	return 11, 52
}

func mkFP(width int, sign uint64, exp uint64, frac uint64) uint64 {
	e, f := fmtEF(width)
	return sign<<(e+f) | (exp&(1<<e-1))<<f | frac&(1<<f-1)
}

// intToFP is the exact encoding of the integer n (|n| < 2^(F+1) * 2^k, rounded towards zero
// otherwise) in the given width: only used to build edge values, exactness is not needed.
func intToFP(width int, neg bool, n uint64) uint64 {
	if n == 0 {
		return mkFP(width, b2u(neg), 0, 0)
	}
	_, f := fmtEF(width)
	bias := uint64(127)
	if width == 64 {
		bias = 1023
	}
	hb := 63
	for n>>hb == 0 {
		hb--
	}
	var frac uint64
	if hb >= f {
		frac = n >> (hb - f)
	} else {
		frac = n << (f - hb)
	}
	return mkFP(width, b2u(neg), bias+uint64(hb), frac)
}

func b2u(b bool) uint64 {
	if b {
		return 1
	}
	return 0
}

// FPEdge returns an IEEE binary32 (width 32) or binary64 edge value as raw bits.
func FPEdge(r *rand.Rand, width int) uint64 {
	e, f := fmtEF(width)
	maxE := uint64(1)<<e - 1
	bias := maxE / 2
	s := uint64(r.IntN(2))
	fr := func() uint64 { return r.Uint64() & (1<<f - 1) }
	switch r.IntN(22) {
	case 0:
		return mkFP(width, s, 0, 0)
	case 1:
		return mkFP(width, s, 0, 1)
	case 2:
		return mkFP(width, s, 0, 1<<f-1)
	case 3:
		v := fr()
		if r.IntN(2) == 0 {
			v >>= uint(r.IntN(f))
		}
		return mkFP(width, s, 0, max(v, 1))
	case 4:
		return mkFP(width, s, 1, []uint64{0, 1, fr()}[r.IntN(3)])
	case 5:
		return mkFP(width, s, maxE-1, []uint64{1<<f - 1, 1<<f - 2, fr()}[r.IntN(3)])
	case 6:
		// ±1, ±2, ±0.5, ±1.5, ±3, ±0.75
		ex := bias + uint64(r.IntN(3)) - 1
		return mkFP(width, s, ex, []uint64{0, 1 << (f - 1), 0}[r.IntN(3)])
	case 7:
		// one ulp around a power of two
		ex := 1 + uint64(r.IntN(int(maxE-1)))
		return mkFP(width, s, ex, []uint64{0, 1, 1<<f - 1}[r.IntN(3)])
	case 8:
		return mkFP(width, s, maxE, 0)
	case 9:
		// default quiet NaN, x86 indefinite
		return mkFP(width, s, maxE, 1<<(f-1))
	case 10:
		return mkFP(width, s, maxE, 1<<(f-1)|fr())
	case 11, 12:
		// signalling NaN, non-zero payload
		p := fr() &^ (1 << (f - 1))
		if r.IntN(3) == 0 {
			p &= 1<<uint(1+r.IntN(8)) - 1
		}
		return mkFP(width, s, maxE, max(p, 1))
	case 13:
		// integers around 2^k for the conversion boundaries
		k := []int{8, 15, 16, 24, 31, 32, 52, 53, 62, 63, 64}[r.IntN(11)]
		ex := bias + uint64(k)
		if r.IntN(2) == 0 {
			ex--
			return mkFP(width, s, ex, 1<<f-uint64(r.IntN(4))-1)
		}
		return mkFP(width, s, ex, uint64(r.IntN(4)))
	case 14:
		// halfway values n + 0.5, n + 0.25, n + 0.75 and small integers
		n := uint64(r.IntN(1 << uint(1+r.IntN(min(f, 30)))))
		q := uint64(r.IntN(4))
		if n == 0 && q == 0 {
			q = 2
		}
		v := intToFP(width, s == 1, n*4+q)
		// divide by 4: exponent - 2 (n*4+q is exact for these small values)
		ex := (v >> f) & maxE
		if ex > 2 {
			v = v&^(maxE<<f) | (ex-2)<<f
		}
		return v
	case 15:
		return intToFP(width, s == 1, uint64(r.IntN(1<<20)))
	case 16, 17:
		return mkFP(width, s, 1+uint64(r.IntN(int(maxE-1))), fr())
	case 18:
		// near the underflow threshold
		return mkFP(width, s, uint64(r.IntN(4)), fr())
	case 19:
		// near the overflow threshold
		return mkFP(width, s, maxE-1-uint64(r.IntN(3)), fr())
	case 20:
		// moderate magnitudes
		return mkFP(width, s, bias-20+uint64(r.IntN(40)), fr())
	default:
		if width == 32 {
			return uint64(r.Uint32())
		}
		return r.Uint64()
	}
}

// fpPair crafts the second operand b for the first operand a: halfway rounding, cancellation,
// underflow and overflow boundaries, equal and opposite values.
func fpPair(r *rand.Rand, width int, a uint64) uint64 {
	e, f := fmtEF(width)
	maxE := uint64(1)<<e - 1
	bias := maxE / 2
	sa := a >> (e + f) & 1
	ea := a >> f & maxE
	fr := func() uint64 { return r.Uint64() & (1<<f - 1) }
	s := uint64(r.IntN(2))
	switch r.IntN(9) {
	case 0: // half an ulp of a (add/sub ties), possibly a little more or less
		if ea > uint64(f)+1 {
			return mkFP(width, s, ea-uint64(f)-1, []uint64{0, 0, 1, 1<<f - 1}[r.IntN(4)])
		}
	case 1: // cancellation: -a, or -a one ulp away
		return a ^ 1<<(e+f) + uint64(r.IntN(3)) - 1
	case 2:
		return a
	case 3: // product/quotient near the underflow threshold
		d := int64(r.IntN(70)) - 60
		eb := int64(1) + d - (int64(ea) - int64(bias)) + int64(bias)
		if eb >= 1 && eb < int64(maxE) {
			return mkFP(width, s, uint64(eb), fr())
		}
	case 4: // quotient near the underflow threshold
		d := int64(r.IntN(70)) - 60
		eb := int64(ea) - (1 + d)
		if eb >= 1 && eb < int64(maxE) {
			return mkFP(width, s, uint64(eb), fr())
		}
	case 5: // product near overflow
		eb := int64(maxE-1) - (int64(ea) - int64(bias)) + int64(r.IntN(3)) - 1
		if eb >= 1 && eb < int64(maxE) {
			return mkFP(width, s, uint64(eb), fr())
		}
	case 6: // sum near overflow / near the underflow threshold with the opposite sign
		if ea >= maxE-2 {
			return mkFP(width, sa, maxE-1, fr())
		}
		return mkFP(width, 1-sa, ea, fr())
	case 7: // same exponent, random fraction (exact differences, ties in mul)
		return mkFP(width, s, ea, fr())
	}
	return FPEdge(r, width)
}

// fpLane writes v into lane `lane` (of width bits) of the 128-bit value x.
func fpLane(x *[2]uint64, width, lane int, v uint64) {
	if width == 64 {
		x[lane] = v
		return
	}
	w, sh := lane/2, uint(32*(lane%2))
	x[w] = x[w]&^(0xFFFFFFFF<<sh) | (v&0xFFFFFFFF)<<sh
}

func fpLaneGet(x [2]uint64, width, lane int) uint64 {
	if width == 64 {
		return x[lane]
	}
	return x[lane/2] >> uint(32*(lane%2)) & 0xFFFFFFFF
}

// fpXMM fills an XMM value: edge values in the FP lanes (all lanes when packed), random upper
// bits otherwise, so preservation of bits 127:width is visible.
func fpXMM(r *rand.Rand, info fpInfo) [2]uint64 {
	x := [2]uint64{r.Uint64(), r.Uint64()}
	if r.IntN(8) == 0 {
		x = [2]uint64{0, 0}
	}
	n := 1
	if info.packed {
		n = 128 / info.width
	}
	for l := 0; l < n; l++ {
		fpLane(&x, info.width, l, FPEdge(r, info.width))
	}
	return x
}

var intEdges = []uint64{0, 1, 2, 3, 0x7fffffff, 0x80000000, 0x80000001, 0xffffffff, 0xfffffffe, 0x100000000,
	0x7fffffffffffffff, 0x8000000000000000, 0x8000000000000001, 0xffffffffffffffff, 0xfffffffffffffffe,
	1<<24 + 1, 1<<24 - 1, 1 << 24, 1<<53 + 1, 1<<53 - 1, 1 << 53, 1<<54 + 1, 1<<54 + 2, 1<<54 + 3, 1<<63 + 1<<10, 1<<63 - 1<<9,
	0xffffffff00000000, 0xfffffffff0000000, 1<<25 + 1, 1<<25 + 3, 1<<26 + 2}

// FPInt is an integer edge value for CVTSI2SD/SS sources.
func FPInt(r *rand.Rand) uint64 {
	switch r.IntN(6) {
	case 0, 1:
		return intEdges[r.IntN(len(intEdges))]
	case 2:
		v := r.Uint64() >> uint(r.IntN(64))
		if r.IntN(2) == 0 {
			v = -v
		}
		return v
	case 3:
		// halfway cases for binary32/binary64: odd multiples of 2^k with k low bits
		k := uint(r.IntN(40))
		v := (uint64(r.IntN(1<<24))<<1 | 1) << k
		if r.IntN(2) == 0 {
			v = -v
		}
		return v
	default:
		return r.Uint64()
	}
}

// RandMXCSR draws an MXCSR value: rounding control uniform, FTZ and DAZ about 30% each, all
// exceptions masked in about 70% of the cases (random masks otherwise), random initial flags.
func RandMXCSR(r *rand.Rand) uint32 {
	m := uint32(r.IntN(4)) << 13
	if r.IntN(10) < 3 {
		m |= 1 << 15
	}
	if r.IntN(10) < 3 {
		m |= 1 << 6
	}
	if r.IntN(10) < 7 {
		m |= 0x3F << 7
	} else {
		m |= uint32(r.IntN(64)) << 7
	}
	if r.IntN(2) == 0 {
		m |= uint32(r.IntN(64))
	}
	return m
}

// FPVariants returns k copies of s with different MXCSR values (the first with every
// exception masked), so each FP encoding runs under several rounding/flush/mask settings.
func FPVariants(r *rand.Rand, s State, k int) []State {
	out := make([]State, 0, k)
	for i := 0; i < k; i++ {
		t := s
		t.Init = append([][2]int(nil), s.Init...)
		m := RandMXCSR(r)
		if i == 0 {
			m |= 0x3F << 7
		}
		t.SetMXCSR(m)
		out = append(out, t)
	}
	return out
}

func regVal(s *State, a x86asm.Reg) (uint64, bool) {
	n, hi, ok := regNum(a)
	if !ok || hi {
		return 0, false
	}
	return s.Regs[n], true
}

// effAddr is the effective address of m in state s (no segment, no RIP).
func effAddr(s *State, inst x86asm.Inst, m x86asm.Mem) (uint64, bool) {
	if m.Base == x86asm.RIP || m.Segment != 0 || inst.AddrSize == 32 {
		return 0, false
	}
	for _, p := range inst.Prefix {
		if p&0xFF == x86asm.PrefixFS || p&0xFF == x86asm.PrefixGS {
			return 0, false
		}
	}
	var ea uint64
	if m.Base != 0 {
		v, ok := regVal(s, m.Base)
		if !ok {
			return 0, false
		}
		ea += v
	}
	if m.Index != 0 {
		v, ok := regVal(s, m.Index)
		if !ok {
			return 0, false
		}
		ea += v * uint64(m.Scale)
	}
	return ea + uint64(m.Disp), true
}

func plantLE(s *State, ea uint64, v [2]uint64, n int) {
	if ea < L.DataBase || ea > L.DataBase+L.DataSize-uint64(n) {
		return
	}
	off := int(ea - L.DataBase)
	for k := 0; k < n; k++ {
		s.Init = append(s.Init, [2]int{off + k, int(v[k/8] >> (8 * uint(k%8)) & 0xff)})
	}
}

// setupFP replaces the XMM state of an FP instruction by edge values, crafts its operand pair,
// plants edge values in a memory operand and draws an MXCSR.
func setupFP(r *rand.Rand, s *State, inst x86asm.Inst, info fpInfo) {
	for i := range s.XMM {
		s.XMM[i] = fpXMM(r, info)
	}
	var dst, src x86asm.Arg
	if inst.Args[0] != nil {
		dst = inst.Args[0]
	}
	if inst.Args[1] != nil {
		src = inst.Args[1]
	}
	xn := func(a x86asm.Arg) int {
		if g, ok := a.(x86asm.Reg); ok && g >= x86asm.X0 && g <= x86asm.X15 {
			return int(g - x86asm.X0)
		}
		return -1
	}
	// the floating-point value of the destination (first source), for pairing
	a := FPEdge(r, info.width)
	if d := xn(dst); d >= 0 {
		a = fpLaneGet(s.XMM[d], info.width, 0)
	}
	pair := r.IntN(10) < 4
	switch sv := src.(type) {
	case x86asm.Reg:
		if n := xn(sv); n >= 0 && pair && !info.gprSrc {
			fpLane(&s.XMM[n], info.width, 0, fpPair(r, info.width, a))
		} else if g, hi, ok := regNum(sv); ok && !hi && info.gprSrc && g != 4 {
			s.Regs[g] = FPInt(r)
		}
	case x86asm.Mem:
		// legacy-SSE 16-byte memory operands must be aligned: mostly align them
		if inst.MemBytes == 16 && r.IntN(4) != 0 {
			if ea, ok := effAddr(s, inst, sv); ok && ea >= L.DataBase && ea < L.DataBase+L.DataSize {
				if bn, _, bok := regNum(sv.Base); bok && bn != 4 {
					s.Regs[bn] -= ea & 15
				}
			}
		}
		if ea, ok := effAddr(s, inst, sv); ok {
			var v [2]uint64
			switch {
			case info.gprSrc:
				v = [2]uint64{FPInt(r), 0}
			default:
				v = fpXMM(r, info)
				if pair {
					fpLane(&v, info.width, 0, fpPair(r, info.width, a))
				}
			}
			n := inst.MemBytes
			if n <= 0 || n > 16 {
				n = info.width / 8
			}
			plantLE(s, ea, v, n)
		}
	}
	s.SetMXCSR(RandMXCSR(r))
}

func fpSpecs() []Spec {
	var s []Spec
	add := func(name string, pre []byte, op []byte, mod int) {
		s = append(s, Spec{Name: name, Pre: pre, Op: op, Reg: -1, Mod3: mod})
	}
	b := func(x ...byte) []byte { return x }
	// arithmetic, square root, min/max: F2 = SD, F3 = SS; 66 / none are the packed
	// neighbours (not in the scalar subset)
	for _, o := range []byte{0x58, 0x59, 0x5C, 0x5E, 0x51, 0x5D, 0x5F} {
		for _, mod := range []int{1, 1, 2, 0} {
			add("fp/arith", b(0xF2), b(0x0F, o), mod)
			add("fp/arith", b(0xF3), b(0x0F, o), mod)
		}
		add("fp/packed", b(0x66), b(0x0F, o), 0)
		add("fp/packed", nil, b(0x0F, o), 0)
	}
	// UCOMISD/COMISD (66), UCOMISS/COMISS (none); F2/F3 neighbours
	for _, o := range []byte{0x2E, 0x2F} {
		for _, mod := range []int{1, 1, 2} {
			add("fp/comi", b(0x66), b(0x0F, o), mod)
			add("fp/comi", nil, b(0x0F, o), mod)
		}
		add("fp/other", b(0xF2), b(0x0F, o), 0)
		add("fp/other", b(0xF3), b(0x0F, o), 0)
	}
	// CVTSI2SD/SS (2A), CVTTSD2SI/CVTTSS2SI (2C), CVTSD2SI/CVTSS2SI (2D); REX.W is random in
	// Targeted; 66 / none are MMX conversions
	for _, o := range []byte{0x2A, 0x2C, 0x2D} {
		for _, mod := range []int{1, 1, 2, 0} {
			add("fp/cvt", b(0xF2), b(0x0F, o), mod)
			add("fp/cvt", b(0xF3), b(0x0F, o), mod)
		}
		add("fp/other", b(0x66), b(0x0F, o), 0)
	}
	// CVTSD2SS (F2 5A), CVTSS2SD (F3 5A); CVTPD2PS / CVTPS2PD neighbours
	for _, mod := range []int{1, 1, 2, 0} {
		add("fp/cvt", b(0xF2), b(0x0F, 0x5A), mod)
		add("fp/cvt", b(0xF3), b(0x0F, 0x5A), mod)
	}
	add("fp/packed", b(0x66), b(0x0F, 0x5A), 0)
	add("fp/packed", nil, b(0x0F, 0x5A), 0)
	// ROUNDSS (66 0F 3A 0A), ROUNDSD (0B); ROUNDPS/PD (08/09) neighbours; the imm8 is random
	for _, mod := range []int{1, 1, 2, 0} {
		add("fp/round", b(0x66), b(0x0F, 0x3A, 0x0B), mod)
		add("fp/round", b(0x66), b(0x0F, 0x3A, 0x0A), mod)
	}
	add("fp/packed", b(0x66), b(0x0F, 0x3A, 0x08), 0)
	add("fp/packed", b(0x66), b(0x0F, 0x3A, 0x09), 0)
	add("fp/other", nil, b(0x0F, 0x3A, 0x0B), 0)
	// CMPSD (F2 0F C2) / CMPSS (F3); CMPPD/CMPPS neighbours
	for _, mod := range []int{1, 1, 2, 0} {
		add("fp/cmp", b(0xF2), b(0x0F, 0xC2), mod)
		add("fp/cmp", b(0xF3), b(0x0F, 0xC2), mod)
	}
	add("fp/packed", b(0x66), b(0x0F, 0xC2), 0)
	add("fp/packed", nil, b(0x0F, 0xC2), 0)
	// bitwise ANDPS/ANDNPS/ORPS (none) and ANDPD/ANDNPD/ORPD (66); F2/F3 neighbours
	for _, o := range []byte{0x54, 0x55, 0x56} {
		for _, mod := range []int{1, 2, 0} {
			add("fp/logic", nil, b(0x0F, o), mod)
			add("fp/logic", b(0x66), b(0x0F, o), mod)
		}
		add("fp/other", b(0xF2), b(0x0F, o), 0)
		add("fp/other", b(0xF3), b(0x0F, o), 0)
	}
	return s
}

// FPSpecs is the targeted SSE floating-point table (also part of Specs).
var FPSpecs = fpSpecs()

func init() { Specs = append(Specs, FPSpecs...) }

// FPVexSpecs are VEX forms of the scalar FP instructions: AVX, outside the model (they must
// be rejected).
var FPVexSpecs = []VexSpec{
	{"vex/fp", 1, 3, 0x58, 0}, // VADDSD
	{"vex/fp", 1, 2, 0x59, 0}, // VMULSS
	{"vex/fp", 1, 3, 0x51, 0}, // VSQRTSD
	{"vex/fp", 1, 1, 0x2E, 0}, // VUCOMISD
	{"vex/fp", 1, 3, 0x2C, 0}, // VCVTTSD2SI
	{"vex/fp", 1, 3, 0x2A, 0}, // VCVTSI2SD
	{"vex/fp", 3, 1, 0x0B, 0}, // VROUNDSD
	{"vex/fp", 1, 1, 0x54, 0}, // VANDPD
	{"vex/fp", 1, 3, 0xC2, 0}, // VCMPSD
}

func init() { VexSpecs = append(VexSpecs, FPVexSpecs...) }

// fpRR encodes an SSE register-register instruction: [pre] [REX] op modrm [imm].
func fpRR(pre []byte, op []byte, w64 bool, reg, rm int, imm []byte) []byte {
	var out []byte
	out = append(out, pre...)
	out = append(out, rexFor(map[bool]int{true: 64, false: 32}[w64], reg, 0, rm, false)...)
	out = append(out, op...)
	out = append(out, modrmRR(reg, rm))
	return append(out, imm...)
}

// FPEdges are the systematic SSE floating-point families: every scalar operation on crafted
// operand pairs under all four rounding modes crossed with FTZ/DAZ (all masked), and under each
// single unmasked exception; conversions of out-of-range values; ROUNDSD/ROUNDSS for every
// imm8 low nibble; CMPSD/CMPSS for every predicate.
func FPEdges(r *rand.Rand, n int) []EdgeCase {
	var out []EdgeCase
	emit := func(class string, b []byte, s State) {
		if OK(b) {
			out = append(out, EdgeCase{"edge/" + class, b, s})
		}
	}
	base := func() State {
		var s State
		for i := range s.Regs {
			s.Regs[i] = RandValue(r)
		}
		s.Regs[4] = L.DataBase + 1024 + 8*uint64(r.IntN(256))
		s.RFlags = RandFlags(r)
		s.Seed = uint64(r.IntN(1 << 20))
		return s
	}
	// variants: all 16 RC x {FTZ,DAZ} with every exception masked (random initial flags),
	// then each exception unmasked alone
	variants := func(s State, emitOne func(State)) {
		for k := 0; k < 16; k++ {
			t := s
			m := uint32(k&3)<<13 | 0x3F<<7
			if k&4 != 0 {
				m |= 1 << 15
			}
			if k&8 != 0 {
				m |= 1 << 6
			}
			if r.IntN(3) == 0 {
				m |= uint32(r.IntN(64))
			}
			t.SetMXCSR(m)
			emitOne(t)
		}
		for e := 0; e < 6; e++ {
			t := s
			m := uint32(r.IntN(4))<<13 | (0x3F&^(1<<e))<<7
			if r.IntN(4) == 0 {
				m |= 1 << 15
			}
			if r.IntN(4) == 0 {
				m |= 1 << 6
			}
			t.SetMXCSR(m)
			emitOne(t)
		}
	}
	type op struct {
		cls   string
		pre   byte
		op    []byte
		width int
		imm   bool
	}
	ops := []op{}
	for _, o := range []byte{0x58, 0x59, 0x5C, 0x5E, 0x51, 0x5D, 0x5F} {
		ops = append(ops, op{"fp-arith", 0xF2, []byte{0x0F, o}, 64, false}, op{"fp-arith", 0xF3, []byte{0x0F, o}, 32, false})
	}
	ops = append(ops,
		op{"fp-comi", 0x66, []byte{0x0F, 0x2E}, 64, false}, op{"fp-comi", 0x66, []byte{0x0F, 0x2F}, 64, false},
		op{"fp-comi", 0, []byte{0x0F, 0x2E}, 32, false}, op{"fp-comi", 0, []byte{0x0F, 0x2F}, 32, false},
		op{"fp-cvt", 0xF2, []byte{0x0F, 0x5A}, 64, false}, op{"fp-cvt", 0xF3, []byte{0x0F, 0x5A}, 32, false},
		op{"fp-cmp", 0xF2, []byte{0x0F, 0xC2}, 64, true}, op{"fp-cmp", 0xF3, []byte{0x0F, 0xC2}, 32, true},
		op{"fp-round", 0x66, []byte{0x0F, 0x3A, 0x0B}, 64, true}, op{"fp-round", 0x66, []byte{0x0F, 0x3A, 0x0A}, 32, true})
	for round := 0; round < n; round++ {
		for _, o := range ops {
			d, sr := r.IntN(16), r.IntN(16)
			for sr == d && r.IntN(4) != 0 {
				sr = r.IntN(16)
			}
			var imm []byte
			if o.imm {
				if o.cls == "fp-round" {
					imm = []byte{byte(round%16) | byte(r.IntN(16))<<4&[]byte{0, 0xF0}[r.IntN(2)]}
				} else {
					imm = []byte{byte(round % 8)}
				}
			}
			var pre []byte
			if o.pre != 0 {
				pre = []byte{o.pre}
			}
			b := fpRR(pre, o.op, false, d, sr, imm)
			s := base()
			info := fpInfo{width: o.width}
			for i := range s.XMM {
				s.XMM[i] = fpXMM(r, info)
			}
			a := fpLaneGet(s.XMM[d], o.width, 0)
			if d != sr {
				fpLane(&s.XMM[sr], o.width, 0, fpPair(r, o.width, a))
			}
			variants(s, func(t State) { emit(o.cls, b, t) })
		}
		// conversions to integer: CVTTSD2SI/CVTSD2SI/CVTTSS2SI/CVTSS2SI, 32/64-bit destination,
		// with out-of-range, NaN and boundary sources
		for _, pre := range []byte{0xF2, 0xF3} {
			width := 64
			if pre == 0xF3 {
				width = 32
			}
			for _, o := range []byte{0x2C, 0x2D} {
				for _, w64 := range []bool{false, true} {
					d, sr := randReg(r, true), r.IntN(16)
					b := fpRR([]byte{pre}, []byte{0x0F, o}, w64, d, sr, nil)
					s := base()
					for i := range s.XMM {
						s.XMM[i] = fpXMM(r, fpInfo{width: width})
					}
					variants(s, func(t State) { emit("fp-cvt2si", b, t) })
				}
			}
			// CVTSI2SD/SS from 32/64-bit registers
			for _, w64 := range []bool{false, true} {
				d, sr := r.IntN(16), randReg(r, true)
				b := fpRR([]byte{pre}, []byte{0x0F, 0x2A}, w64, d, sr, nil)
				s := base()
				for i := range s.XMM {
					s.XMM[i] = fpXMM(r, fpInfo{width: width})
				}
				s.Regs[sr] = FPInt(r)
				variants(s, func(t State) { emit("fp-cvtsi2", b, t) })
			}
		}
	}
	return out
}

// The SSE floating-point instructions in the model's scope count as modelled classes (harvested
// up to -per-class, not -per-other).
func init() {
	for _, m := range []string{"addsd", "subsd", "mulsd", "divsd", "sqrtsd", "minsd", "maxsd", "addss", "subss",
		"mulss", "divss", "sqrtss", "minss", "maxss", "ucomisd", "comisd", "ucomiss", "comiss", "cvtsi2sd",
		"cvtsi2ss", "cvttsd2si", "cvttss2si", "cvtsd2si", "cvtss2si", "cvtsd2ss", "cvtss2sd", "roundsd", "roundss",
		"cmpsd_xmm", "cmpss", "andpd", "andnpd", "orpd", "andps", "andnps", "orps"} {
		Modeled[m] = true
	}
}
