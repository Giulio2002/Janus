package gen

import (
	"math"
	"math/rand/v2"
	"strings"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
	"golang.org/x/arch/x86/x86asm"
)

// GOAMD64=v3 scalar extensions: BMI1 (ANDN BLSR BLSMSK BLSI BEXTR; TZCNT is in the targets),
// BMI2 (SHLX SHRX SARX RORX MULX BZHI PDEP PEXT), MOVBE, scalar FMA3
// (VF{,N}M{ADD,SUB}{132,213,231}{SD,SS}) and SSSE3 PSHUFB/PSIGNB on XMM.

// V3Classes are the classes (x86asm mnemonics, lower case) of the v3 extensions in the model.
var V3Classes = strings.Fields(`andn blsr blsmsk blsi bextr bzhi shlx shrx sarx rorx mulx pdep pext movbe
	pshufb psignb`)

// FMAClasses are the 48 scalar FMA3 classes.
var FMAClasses []string

func init() {
	for _, n := range []string{"vfmadd", "vfmsub", "vfnmadd", "vfnmsub"} {
		for _, f := range []string{"132", "213", "231"} {
			for _, t := range []string{"sd", "ss"} {
				FMAClasses = append(FMAClasses, n+f+t)
			}
		}
	}
	for _, m := range V3Classes {
		Modeled[m] = true
	}
	for _, m := range FMAClasses {
		Modeled[m] = true
		w := 64
		if strings.HasSuffix(m, "ss") {
			w = 32
		}
		fpClasses[m] = fpInfo{width: w, fma: true}
	}
}

// V3Regexp matches the v3 classes (for `harvest -only`).
func V3Regexp() string {
	return "^(" + strings.Join(V3Classes, "|") + "|vfn?m(add|sub)(132|213|231)s[sd])$"
}

func v3Specs() []Spec {
	var s []Spec
	add := func(name string, pre []byte, op []byte, mod int) {
		s = append(s, Spec{Name: name, Pre: pre, Op: op, Reg: -1, Mod3: mod})
	}
	b := func(x ...byte) []byte { return x }
	// MOVBE load/store (memory forms; the register forms are #UD), the 16-bit form (66), and
	// the CRC32 (F2) / reserved (F3) neighbours
	for _, o := range []byte{0xF0, 0xF1} {
		for _, mod := range []int{2, 2, 2, 0} {
			add("v3/movbe", nil, b(0x0F, 0x38, o), mod)
		}
		add("v3/movbe", b(0x66), b(0x0F, 0x38, o), 2)
		add("v3/movbe", b(0x66), b(0x0F, 0x38, o), 0)
		add("v3/movbe", b(0xF2), b(0x0F, 0x38, o), 0)
		add("v3/movbe", b(0xF3), b(0x0F, 0x38, o), 0)
	}
	// SSSE3 PSHUFB / PSIGNB (66: XMM; no prefix: MMX, rejected), and neighbours
	for _, o := range []byte{0x00, 0x08} {
		for _, mod := range []int{1, 1, 2, 0} {
			add("v3/ssse3", b(0x66), b(0x0F, 0x38, o), mod)
		}
		add("v3/ssse3", nil, b(0x0F, 0x38, o), 0)
		add("v3/ssse3", b(0xF3), b(0x0F, 0x38, o), 0)
	}
	for _, o := range []byte{0x01, 0x04, 0x09, 0x0A, 0x0B, 0x1C} {
		add("v3/ssse3", b(0x66), b(0x0F, 0x38, o), 0)
	}
	return s
}

// V3Specs are the legacy-encoded v3 targets (also part of Specs).
var V3Specs = v3Specs()

func init() { Specs = append(Specs, V3Specs...) }

func v3VexSpecs() []VexSpec {
	var s []VexSpec
	add := func(name string, mp, pp, op byte, mod int) { s = append(s, VexSpec{name, mp, pp, op, mod}) }
	for _, mod := range []int{1, 1, 2, 0} {
		add("v3/bmi", 2, 0, 0xF2, mod) // ANDN
		add("v3/bmi", 2, 0, 0xF3, mod) // BLSR/BLSMSK/BLSI (group 17)
		add("v3/bmi", 2, 0, 0xF3, mod)
		add("v3/bmi", 2, 0, 0xF5, mod) // BZHI
		add("v3/bmi", 2, 2, 0xF5, mod) // PEXT
		add("v3/bmi", 2, 3, 0xF5, mod) // PDEP
		add("v3/bmi", 2, 3, 0xF6, mod) // MULX
		add("v3/bmi", 2, 0, 0xF7, mod) // BEXTR
		add("v3/bmi", 2, 1, 0xF7, mod) // SHLX
		add("v3/bmi", 2, 2, 0xF7, mod) // SARX
		add("v3/bmi", 2, 3, 0xF7, mod) // SHRX
		add("v3/bmi", 3, 3, 0xF0, mod) // RORX
	}
	// neighbours that must be rejected
	add("v3/bmi-other", 2, 1, 0xF2, 0)
	add("v3/bmi-other", 2, 1, 0xF5, 0)
	add("v3/bmi-other", 2, 0, 0xF6, 0)
	add("v3/bmi-other", 2, 1, 0xF6, 0) // (ADCX is legacy 66 0F 38 F6)
	add("v3/bmi-other", 2, 2, 0xF6, 0)
	add("v3/bmi-other", 3, 0, 0xF0, 0)
	add("v3/bmi-other", 2, 0, 0xF4, 0)
	// scalar FMA (66 0F38 W0 = SS, W1 = SD, drawn by the generator), and the packed neighbours
	for hi := byte(0x90); hi <= 0xB0; hi += 0x10 {
		for _, lo := range []byte{0x9, 0xB, 0xD, 0xF} {
			add("v3/fma", 2, 1, hi|lo, 1)
			add("v3/fma", 2, 1, hi|lo, 0)
		}
		for _, lo := range []byte{0x8, 0xA, 0xC, 0xE, 0x6, 0x7} {
			add("v3/fma-other", 2, 1, hi|lo, 0)
		}
	}
	return s
}

// V3VexSpecs are the VEX-encoded v3 targets.
var V3VexSpecs = v3VexSpecs()

// vexEnc encodes a 3-byte VEX instruction: rex = W R X B (un-inverted), map, vvvv (register
// number, un-inverted), L, pp, opcode, then the tail (ModRM, ...).
func vexEnc(rex int, mp byte, vvvv int, l int, pp byte, op byte, tail ...byte) []byte {
	r, x, bb, w := rex>>2&1, rex>>1&1, rex&1, rex>>3&1
	b1 := byte(1-r)<<7 | byte(1-x)<<6 | byte(1-bb)<<5 | mp
	b2 := byte(w)<<7 | (^byte(vvvv)&15)<<3 | byte(l)<<2 | pp
	return append([]byte{0xC4, b1, b2, op}, tail...)
}

// V3Targeted produces one encoding of sp: VEX.vvvv uniform (it is a register operand of BMI
// and FMA), VEX.L mostly 0, VEX.W uniform; sometimes a stray prefix, another map or pp.
func V3Targeted(r *rand.Rand, sp VexSpec) []byte {
	var out []byte
	if r.IntN(16) == 0 {
		out = append(out, []byte{0x66, 0xF2, 0xF3, 0xF0, 0x40, 0x48, 0x2E, 0x64, 0x67}[r.IntN(9)])
	}
	l := 0
	if r.IntN(8) == 0 {
		l = 1
	}
	mp, pp := sp.Map, sp.PP
	if r.IntN(24) == 0 {
		mp = byte(r.IntN(4))
	}
	if r.IntN(24) == 0 {
		pp = byte(r.IntN(4))
	}
	vvvv := r.IntN(16)
	if sp.Map == 3 && r.IntN(4) != 0 {
		vvvv = 0 // RORX: VEX.vvvv must be 1111
	}
	modrm := byte(r.IntN(256))
	switch sp.Mod3 {
	case 1:
		modrm |= 0xC0
	case 2:
		if modrm>>6 == 3 {
			modrm &^= 0xC0
		}
	default:
		if r.IntN(3) == 0 {
			modrm |= 0xC0
		}
	}
	tail := make([]byte, 12)
	for i := range tail {
		tail[i] = byte(r.IntN(256))
		if r.IntN(2) == 0 && i > 0 {
			tail[i] = []byte{0, 0, 0xff, 1, 0x20, 0x10, 0x80, 0xe0, 7, 31, 32, 63}[r.IntN(12)]
		}
	}
	tail[0] = modrm
	out = append(out, vexEnc(r.IntN(16), mp, vvvv, l, pp, sp.Op, tail...)...)
	return trim(out)
}

var bmiCounts = []uint64{0, 1, 2, 7, 8, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 200, 255}

// setupV3 steers the operands of the BMI/SSSE3 classes: the VEX.vvvv count / control /
// index register of SHLX SHRX SARX BEXTR BZHI gets interesting values, PSIGNB sources get zero,
// positive and negative bytes, and the FMA classes get IEEE edge values (setupFMA).
func setupV3(r *rand.Rand, s *State, inst x86asm.Inst, cls string) {
	switch cls {
	case "shlx", "shrx", "sarx", "bextr", "bzhi":
		g, ok := inst.Args[2].(x86asm.Reg)
		if !ok || r.IntN(4) == 0 {
			return
		}
		n, _, ok := regNum(g)
		if !ok || n == 4 {
			return
		}
		v := bmiCounts[r.IntN(len(bmiCounts))]
		if cls == "bextr" {
			v |= bmiCounts[r.IntN(len(bmiCounts))] << 8
		}
		if r.IntN(2) == 0 {
			v |= r.Uint64() &^ 0xFFFF
		}
		s.Regs[n] = v
	case "psignb", "pshufb":
		if x, ok := inst.Args[1].(x86asm.Reg); ok && x >= x86asm.X0 && x <= x86asm.X15 && r.IntN(2) == 0 {
			var v [2]uint64
			for i := 0; i < 16; i++ {
				b := []uint64{0, 0, 1, 0x7f, 0x80, 0xff, 0x0f, 0x8f, uint64(r.IntN(256))}[r.IntN(9)]
				v[i/8] |= b << (8 * (i % 8))
			}
			s.XMM[x-x86asm.X0] = v
		}
	case "pdep", "pext":
		// masks: sparse, dense, contiguous
		if m, ok := inst.Args[2].(x86asm.Reg); ok && r.IntN(2) == 0 {
			if n, _, ok := regNum(m); ok && n != 4 {
				k := uint(r.IntN(64))
				s.Regs[n] = []uint64{r.Uint64() & r.Uint64() & r.Uint64(), r.Uint64() | r.Uint64(), (1<<k - 1) << uint(r.IntN(64-int(k)+1)), 0, ^uint64(0)}[r.IntN(5)]
			}
		}
	}
}

// fmaRoles returns the XMM argument indexes (0 = dst, 1 = src2, 2 = src3) of the two
// multiplicands and the addend of an FMA class.
func fmaRoles(cls string) (a, b, c int) {
	switch {
	case strings.Contains(cls, "132"):
		return 0, 2, 1
	case strings.Contains(cls, "213"):
		return 1, 0, 2
	}
	return 1, 2, 0
}

// fmaAddend crafts the addend c for the multiplicands a, b: the negated rounded product (so the
// sum is the product's rounding error, which only a fused operation keeps), the product one
// ulp away, half an ulp of the product (ties), or an edge value.
func fmaAddend(r *rand.Rand, width int, a, b uint64) uint64 {
	var p uint64
	if width == 64 {
		p = math.Float64bits(math.Float64frombits(a) * math.Float64frombits(b))
	} else {
		p = uint64(math.Float32bits(math.Float32frombits(uint32(a)) * math.Float32frombits(uint32(b))))
	}
	e, f := fmtEF(width)
	maxE := uint64(1)<<e - 1
	ep := p >> f & maxE
	sign := uint64(1) << (e + f)
	switch r.IntN(8) {
	case 0, 1:
		return p ^ sign
	case 2:
		return p ^ sign + uint64(r.IntN(3)) - 1
	case 3:
		if ep > uint64(f)+1 && ep < maxE {
			return mkFP(width, uint64(r.IntN(2)), ep-uint64(f)-1, []uint64{0, 0, 1, 1<<f - 1}[r.IntN(4)])
		}
	case 4:
		return p
	case 5:
		return fpPair(r, width, a)
	}
	return FPEdge(r, width)
}

// setupFMA fills the XMM registers with edge values, pairs the multiplicands, crafts the addend
// (also in a memory operand) and draws an MXCSR.
func setupFMA(r *rand.Rand, s *State, inst x86asm.Inst, cls string, info fpInfo) {
	for i := range s.XMM {
		s.XMM[i] = fpXMM(r, info)
	}
	w := info.width
	ra, rb, rc := fmaRoles(cls)
	var vals [3]uint64
	vals[ra] = FPEdge(r, w)
	vals[rb] = FPEdge(r, w)
	if r.IntN(10) < 4 {
		vals[rb] = fpPair(r, w, vals[ra])
	}
	vals[rc] = FPEdge(r, w)
	if r.IntN(10) < 6 {
		vals[rc] = fmaAddend(r, w, vals[ra], vals[rb])
	}
	// write in reverse order so that, for repeated registers, the destination's value wins
	for k := 2; k >= 0; k-- {
		switch a := inst.Args[k].(type) {
		case x86asm.Reg:
			if a >= x86asm.X0 && a <= x86asm.X15 {
				fpLane(&s.XMM[a-x86asm.X0], w, 0, vals[k])
			}
		case x86asm.Mem:
			if ea, ok := effAddr(s, inst, a); ok {
				plantLE(s, ea, [2]uint64{vals[k], 0}, w/8)
			}
		}
	}
	s.SetMXCSR(RandMXCSR(r))
}

// FMAEdges are the systematic scalar FMA families: each of the 48 forms on crafted
// register triples (distinct, and sometimes repeated registers) under the 16 RC x FTZ/DAZ
// settings (all masked) and with each exception unmasked alone.
func FMAEdges(r *rand.Rand, n int) []EdgeCase {
	var out []EdgeCase
	for round := 0; round < n; round++ {
		for hi := byte(0x90); hi <= 0xB0; hi += 0x10 {
			for _, lo := range []byte{0x9, 0xB, 0xD, 0xF} {
				for _, w64 := range []bool{false, true} {
					d, s2, s3 := r.IntN(16), r.IntN(16), r.IntN(16)
					if r.IntN(4) != 0 {
						for s2 == d {
							s2 = r.IntN(16)
						}
						for s3 == d || s3 == s2 {
							s3 = r.IntN(16)
						}
					}
					rex := (d >> 3 << 2) | (s3 >> 3)
					if w64 {
						rex |= 8
					}
					b := vexEnc(rex, 2, s2, 0, 1, hi|lo, modrmRR(d, s3))
					cls := Classify(b)
					inst, ok := Decode(b)
					if !ok || !OK(b) {
						continue
					}
					var s State
					for i := range s.Regs {
						s.Regs[i] = RandValue(r)
					}
					s.Regs[4] = L.DataBase + 1024 + 8*uint64(r.IntN(256))
					s.RFlags = RandFlags(r)
					s.Seed = uint64(r.IntN(1 << 20))
					info := fpClasses[cls]
					setupFMA(r, &s, inst, cls, info)
					for k := 0; k < 22; k++ {
						t := s
						var m uint32
						if k < 16 {
							m = uint32(k&3)<<13 | 0x3F<<7
							if k&4 != 0 {
								m |= 1 << 15
							}
							if k&8 != 0 {
								m |= 1 << 6
							}
							if r.IntN(3) == 0 {
								m |= uint32(r.IntN(64))
							}
						} else {
							e := k - 16
							m = uint32(r.IntN(4))<<13 | (0x3F&^(1<<e))<<7
							if r.IntN(4) == 0 {
								m |= 1 << 15
							}
							if r.IntN(4) == 0 {
								m |= 1 << 6
							}
						}
						t.SetMXCSR(m)
						out = append(out, EdgeCase{"edge/fma", b, t})
					}
				}
			}
		}
	}
	return out
}
