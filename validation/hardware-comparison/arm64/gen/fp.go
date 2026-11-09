package gen

// Scalar floating-point classes: classification, encodings and IEEE edge-value states.
//
// The FP data-processing space is `M 0 S 11110 ftype 1 ...` (`sf` instead of `M` for the
// conversions) plus `M 0 S 11111` (3 source). The class only groups results and picks
// states; it never decides what an instruction does.

import (
	"math"
	"math/rand/v2"
)

// classifyFP returns the fp.* class of a word of the x111 group, or "".
func classifyFP(w uint32) string {
	switch {
	case w&0x5F000000 == 0x1F000000:
		return "fp.dp3"
	case w&0x5F200000 == 0x1E000000:
		return "fp.cvtfix"
	case w&0x5F200000 != 0x1E200000:
		return ""
	case w&0x7C00 == 0x4000: // bits 14:10 = 10000
		return "fp.dp1"
	case w&0x3C00 == 0x2000: // bits 13:10 = 1000
		return "fp.cmp"
	case w&0x1C00 == 0x1000: // bits 12:10 = 100
		return "fp.imm"
	case w&0x0C00 == 0x0400:
		return "fp.ccmp"
	case w&0x0C00 == 0x0800:
		return "fp.dp2"
	case w&0x0C00 == 0x0C00:
		return "fp.csel"
	case w&0xFC00 == 0x0000 && w&0x40000000 == 0:
		return "fp.cvtint"
	}
	return ""
}

// IsFP reports whether the class is one of the scalar floating-point classes.
func IsFP(class string) bool { return len(class) > 3 && class[:3] == "fp." }

// ftypeOf picks a precision field: mostly S (00) and D (01), sometimes 10 (unallocated)
// and 11 (half precision, FEAT_FP16).
func ftypeOf(r *rand.Rand) uint32 {
	switch p := r.IntN(100); {
	case p < 46:
		return 0
	case p < 92:
		return 1
	case p < 95:
		return 2
	}
	return 3
}

// mS: the M (bit 31) and S (bit 29) fields, almost always 0.
func mS(r *rand.Rand) uint32 {
	if r.IntN(25) == 0 {
		return u(r, 1)<<31 | u(r, 1)<<29
	}
	return 0
}

func init() {
	Targeted["fp.dp1"] = func(r *rand.Rand) uint32 {
		op := mostly(r, pick(r, 0, 1, 2, 3, 3, 4, 5, 7, 8, 9, 10, 11, 12, 14, 15, 8, 9, 10, 11, 12, 14, 15,
			13, 16, 17, 18, 19, 6), 6)
		return 0x1E204000 | mS(r) | ftypeOf(r)<<22 | op<<15 | vreg(r)<<5 | vreg(r)
	}
	Targeted["fp.dp2"] = func(r *rand.Rand) uint32 {
		op := mostly(r, uint32(r.IntN(9)), 4)
		return 0x1E200800 | mS(r) | ftypeOf(r)<<22 | vreg(r)<<16 | op<<12 | vreg(r)<<5 | vreg(r)
	}
	Targeted["fp.dp3"] = func(r *rand.Rand) uint32 {
		return 0x1F000000 | mS(r) | ftypeOf(r)<<22 | u(r, 1)<<21 | vreg(r)<<16 | u(r, 1)<<15 | vreg(r)<<10 | vreg(r)<<5 | vreg(r)
	}
	Targeted["fp.cmp"] = func(r *rand.Rand) uint32 {
		op2 := mostly(r, pick(r, 0, 8, 16, 24), 5)
		rm := vreg(r)
		if op2&8 != 0 && r.IntN(4) != 0 {
			rm = 0
		}
		return 0x1E202000 | mS(r) | ftypeOf(r)<<22 | rm<<16 | mostly(r, 0, 2)<<14 | vreg(r)<<5 | op2
	}
	Targeted["fp.ccmp"] = func(r *rand.Rand) uint32 {
		return 0x1E200400 | mS(r) | ftypeOf(r)<<22 | vreg(r)<<16 | u(r, 4)<<12 | vreg(r)<<5 | u(r, 1)<<4 | u(r, 4)
	}
	Targeted["fp.csel"] = func(r *rand.Rand) uint32 {
		return 0x1E200C00 | mS(r) | ftypeOf(r)<<22 | vreg(r)<<16 | u(r, 4)<<12 | vreg(r)<<5 | vreg(r)
	}
	Targeted["fp.imm"] = func(r *rand.Rand) uint32 {
		return 0x1E201000 | mS(r) | ftypeOf(r)<<22 | u(r, 8)<<13 | mostly(r, 0, 5)<<5 | vreg(r)
	}
	Targeted["fp.cvtint"] = func(r *rand.Rand) uint32 {
		// rmode:opcode of the allocated forms: FCVT{N,P,M,Z}{S,U} (any rmode, opcode 000/001),
		// SCVTF/UCVTF (00, 010/011), FCVTA{S,U} (00, 100/101), FMOV (110/111) and FJCVTZS
		// (11, 110).
		var rm, op uint32
		switch p := r.IntN(100); {
		case p < 45:
			rm, op = u(r, 2), u(r, 1)
		case p < 75:
			rm, op = 0, 2+u(r, 1)
		case p < 88:
			rm, op = 0, 4+u(r, 1)
		case p < 93:
			rm, op = pick(r, 0, 1, 3), 6+u(r, 1)
		default:
			rm, op = u(r, 2), u(r, 3)
		}
		w := u(r, 1)<<31 | 0x1E200000 | ftypeOf(r)<<22 | rm<<19 | op<<16
		if op == 2 || op == 3 || op == 7 { // integer source
			return w | reg(r)<<5 | vreg(r)
		}
		return w | vreg(r)<<5 | reg(r)
	}
	Targeted["fp.cvtfix"] = func(r *rand.Rand) uint32 {
		rm, op := pick(r, 0, 3, 3), u(r, 1)
		if rm == 0 {
			op = 2 + u(r, 1)
		}
		if r.IntN(8) == 0 {
			rm, op = u(r, 2), u(r, 3)
		}
		w := u(r, 1)<<31 | 0x1E000000 | ftypeOf(r)<<22 | rm<<19 | op<<16 | u(r, 6)<<10
		if op >= 2 {
			return w | reg(r)<<5 | vreg(r)
		}
		return w | vreg(r)<<5 | reg(r)
	}
}

// RandFPCR draws an FPCR value from the bits a reference keeps: RMode (23:22) uniform; FZ
// (24), DN (25), AH (1), FIZ (0), NEP (2) each with probability 0.3; rarely FZ16 (19) and
// AHP (26), which do not affect single or double precision.
func RandFPCR(r *rand.Rand) uint32 {
	v := u(r, 2) << 22
	for _, b := range []uint{24, 25, 1, 0, 2} {
		if r.IntN(10) < 3 {
			v |= 1 << b
		}
	}
	if r.IntN(10) == 0 {
		v |= 1 << 19
	}
	if r.IntN(10) == 0 {
		v |= 1 << 26
	}
	return v
}

// RandFPSR draws an initial FPSR: zero half of the time, otherwise a random subset of the
// cumulative flags IOC DZC OFC UFC IXC IDC (bits 0-4, 7), sometimes with QC (27).
func RandFPSR(r *rand.Rand) uint32 {
	if r.IntN(2) == 0 {
		return 0
	}
	v := u(r, 8) & 0x9F
	if r.IntN(10) == 0 {
		v |= 1 << 27
	}
	return v
}

// IEEE formats: exponent and fraction widths.
type fmtF struct{ e, f uint }

var (
	f32 = fmtF{8, 23}
	f64 = fmtF{11, 52}
)

func (t fmtF) bias() uint64     { return 1<<(t.e-1) - 1 }
func (t fmtF) expMax() uint64   { return 1<<t.e - 1 }
func (t fmtF) fracMask() uint64 { return 1<<t.f - 1 }
func (t fmtF) sign() uint64     { return 1 << (t.e + t.f) }
func (t fmtF) mk(s, e, m uint64) uint64 {
	return s<<(t.e+t.f) | (e&t.expMax())<<t.f | m&t.fracMask()
}

// fromFloat converts an exactly representable value (or rounds with Go's RNE).
func (t fmtF) fromFloat(x float64) uint64 {
	if t == f32 {
		return uint64(math.Float32bits(float32(x)))
	}
	return math.Float64bits(x)
}

func (t fmtF) toFloat(v uint64) float64 {
	if t == f32 {
		return float64(math.Float32frombits(uint32(v)))
	}
	return math.Float64frombits(v)
}

// FPEdge draws one IEEE edge value of format t (as raw bits).
func (t fmtF) edge(r *rand.Rand) uint64 {
	s := u64(r, 1)
	fm := t.fracMask()
	switch p := r.IntN(100); {
	case p < 6:
		return t.mk(s, 0, 0) // ±0
	case p < 10:
		return t.mk(s, 0, 1) // min subnormal
	case p < 13:
		return t.mk(s, 0, fm) // max subnormal
	case p < 20:
		return t.mk(s, 0, 1+r.Uint64()%fm) // random subnormal
	case p < 24:
		return t.mk(s, 1, 0) // min normal
	case p < 26:
		return t.mk(s, 1, r.Uint64()&3) // just above min normal
	case p < 30:
		return t.mk(s, t.expMax()-1, fm-r.Uint64()%3) // max normal and below
	case p < 36:
		return t.mk(s, t.bias()+uint64(r.IntN(3))-1, r.Uint64()%3) // 0.5, 1, 2 (+ulps)
	case p < 40:
		// one ulp around a power of two
		e := 1 + r.Uint64()%(t.expMax()-2)
		if r.IntN(2) == 0 {
			return t.mk(s, e, 0)
		}
		return t.mk(s, e-1, fm)
	case p < 45:
		return t.mk(s, t.expMax(), 0) // ±inf
	case p < 49:
		return t.mk(s, t.expMax(), 1<<(t.f-1)) // default-style quiet NaN
	case p < 53:
		return t.mk(s, t.expMax(), 1<<(t.f-1)|r.Uint64()&(fm>>1)) // quiet NaN with payload
	case p < 59:
		pl := r.Uint64() & (fm >> 1)
		if pl == 0 {
			pl = 1 << r.IntN(int(t.f-1))
		}
		return t.mk(s, t.expMax(), pl) // signalling NaN
	case p < 70:
		// integers and halfway values for conversions and FRINT
		var x float64
		switch q := r.IntN(6); q {
		case 0:
			x = float64(r.IntN(9)) / 2
		case 1:
			x = float64(r.IntN(1<<12)) + 0.5*float64(r.IntN(2))
		case 2:
			k := uint(pick(r, 24, 31, 32, 53, 63, 64))
			x = math.Ldexp(1, int(k)) + float64(r.IntN(5)-2)*math.Ldexp(1, int(k)-int(t.f))
		case 3:
			k := uint(pick(r, 31, 32, 63, 64))
			x = math.Ldexp(1, int(k))
		case 4:
			x = float64(int64(r.Uint64()>>(r.IntN(60)+4))) + 0.5
		default:
			x = 0.5 + float64(r.IntN(4))
		}
		if s == 1 {
			x = -x
		}
		return t.fromFloat(x)
	case p < 88:
		return t.mk(s, 1+r.Uint64()%(t.expMax()-1), r.Uint64()) // random normal
	}
	return r.Uint64() & (t.sign()<<1 - 1) // random bit pattern
}

func u64(r *rand.Rand, n int) uint64 { return r.Uint64() & (1<<n - 1) }

// craft makes (a, b, c) operand values with an interesting relationship for format t:
// halfway sums, exact-zero differences, products that tie, sums and products at the
// underflow and overflow boundaries, and FMA cancellations.
func (t fmtF) craft(r *rand.Rand) (uint64, uint64, uint64) {
	a := t.mk(u64(r, 1), 1+r.Uint64()%(t.expMax()-1), r.Uint64())
	ea := (a >> t.f) & t.expMax()
	c := t.edge(r)
	switch r.IntN(9) {
	case 0: // b is half an ulp of a (times an odd multiple, possibly negative): sum ties
		eb := int64(ea) - int64(t.f) - 1
		if eb < 1 {
			eb = 1
		}
		return a, t.mk(u64(r, 1), uint64(eb), uint64(r.IntN(2))), c
	case 1: // a - a, a + (-a): exact zero, sign from the rounding mode
		return a, a ^ t.sign()*u64(r, 1), c
	case 2: // product ties: 3 * odd significand
		p := t.f + 1
		lo := uint64(1) << (p - 1)
		hi := (uint64(1) << (p + 1)) / 3
		m := lo + r.Uint64()%(hi-lo)
		m |= 1
		x := t.mk(u64(r, 1), t.bias()+1, 1<<(t.f-1)) // 3.0
		y := t.mk(u64(r, 1), t.bias()+uint64(r.IntN(5)), m&t.fracMask())
		return x, y, c
	case 3: // sum near the min normal
		mn := t.mk(0, 1, r.Uint64()%4)
		d := t.mk(1, uint64(r.IntN(2)), 1+r.Uint64()%8)
		return mn, d, c
	case 4: // product near the min normal: 2^k * 2^(emin-k) with random significands
		k := int64(r.IntN(int(t.bias()))) - int64(t.bias())/2
		ex := int64(t.bias()) + k
		ey := 1 - k + int64(r.IntN(3)) - 1
		if ey < 1 {
			ey = 1
		}
		return t.mk(u64(r, 1), uint64(ex), r.Uint64()), t.mk(u64(r, 1), uint64(ey), r.Uint64()&7), c
	case 5: // overflow boundary
		return t.mk(u64(r, 1), t.expMax()-1, t.fracMask()-r.Uint64()%4), t.mk(u64(r, 1), t.expMax()-1-uint64(r.IntN(int(t.f)+2)), r.Uint64()), c
	case 6: // fma cancellation: c = -(a*b) rounded, so a*b + c is the exact rounding error
		b := t.mk(u64(r, 1), t.bias()+uint64(r.IntN(9))-4, r.Uint64())
		x, y := t.toFloat(a)/math.Ldexp(1, int(ea)-int(t.bias())), t.toFloat(b)
		pr := x * y
		if t == f32 {
			pr = float64(float32(x) * float32(y))
		}
		return t.fromFloat(x), b, t.fromFloat(-pr)
	case 7: // denormal operands
		return t.mk(u64(r, 1), 0, r.Uint64()), t.edge(r), t.mk(u64(r, 1), 0, r.Uint64())
	}
	return t.edge(r), t.edge(r), c
}

// IntEdge are integer values for SCVTF/UCVTF sources: powers of two, ties of the float
// roundings (2^24+1, 2^53+1, ...), boundaries of the integer ranges.
var IntEdge = []uint64{
	0, 1, 2, 3, 0xffffffffffffffff, 0xfffffffffffffffe, 1 << 24, 1<<24 + 1, 1<<24 + 3, 1<<25 + 2,
	1 << 53, 1<<53 + 1, 1<<53 + 3, 1<<54 + 2, 0x7fffffff, 0x80000000, 0x80000001, 0xffffffff,
	0x100000000, 0x7fffffffffffffff, 0x8000000000000000, 0x8000000000000001, 0xffffffff00000000,
	0x00000000ffffff80, 0xffffffffffffff80, 0x7fffff80, 0xffffff7f, 0x7ffffffffffffc00,
	0xfffffffffffff800, 0xfffffffffffffc00,
}

func intEdge(r *rand.Rand) uint64 {
	switch p := r.IntN(100); {
	case p < 50:
		return IntEdge[r.IntN(len(IntEdge))]
	case p < 65:
		return uint64(int64(r.IntN(2001) - 1000))
	case p < 80:
		k := uint(r.IntN(40) + 24)
		return (r.Uint64() >> (64 - k)) | 1<<k>>1 | uint64(r.IntN(2))
	}
	return r.Uint64()
}

// setupFP fills a state for a scalar FP word: V registers from the edge-value generator in the
// word's precision (random bits above it, so zeroing and merging are observed), crafted
// operand relationships between Rn, Rm and Ra, integer edge values in the general registers,
// and random FPCR/FPSR.
func setupFP(r *rand.Rand, w uint32, s *State) {
	t := f64
	ft := bits(w, 23, 22)
	if ft == 0 || (ft != 1 && r.IntN(2) == 0) {
		t = f32
	}
	for i := range s.V {
		lo := t.edge(r)
		if t == f32 {
			lo |= uint64(r.Uint32()) << 32 * u64(r, 1)
		}
		hi := r.Uint64()
		if r.IntN(4) == 0 {
			hi = 0
		}
		s.V[i] = [2]uint64{lo, hi}
	}
	setLo := func(i uint32, v uint64) {
		if t == f32 {
			s.V[i][0] = s.V[i][0]&^0xffffffff | v
		} else {
			s.V[i][0] = v
		}
	}
	rn, rm, ra := bits(w, 9, 5), bits(w, 20, 16), bits(w, 14, 10)
	if r.IntN(10) < 5 {
		a, b, c := t.craft(r)
		if r.IntN(2) == 0 {
			a, b = b, a
		}
		setLo(rn, a)
		setLo(rm, b)
		if Classify(w) == "fp.dp3" {
			setLo(ra, c)
		}
	}
	for i := range s.X {
		if r.IntN(2) == 0 {
			s.X[i] = intEdge(r)
		}
	}
	s.FPCR, s.FPSR = RandFPCR(r), RandFPSR(r)
	if r.IntN(4) == 0 { // the Go default: round to nearest, nothing else
		s.FPCR = 0
	}
}
