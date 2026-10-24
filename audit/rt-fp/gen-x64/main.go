// Command genx64 writes the amd64 SSE floating-point red-team corpus (docs/AUDIT-FP.md, rows
// X64-*): special-operand grids crossed with every MXCSR exception-mask combination (several
// unmasked at once, for the #XM precedence), DAZ/FTZ under each rounding mode, CMPSD/CMPSS
// predicates, UCOMIS vs COMIS, conversions at the integer and format boundaries, ROUNDSD ties.
// One instruction per case (layout.Case JSON per line), run by `oracle run` against the host CPU.
//
//	genx64 -o cases.jsonl [-seed 1] [-only REGEX]
package main

import (
	"bufio"
	"encoding/json"
	"flag"
	"fmt"
	"math"
	"math/rand/v2"
	"os"
	"regexp"

	"github.com/Giulio2002/Janus/oracle-amd64/gen"
	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
)

type ff struct{ e, f uint }

var (
	fS = ff{8, 23}
	fD = ff{11, 52}
)

func (t ff) emax() uint64  { return 1<<t.e - 1 }
func (t ff) fmask() uint64 { return 1<<t.f - 1 }
func (t ff) qbit() uint64  { return 1 << (t.f - 1) }
func (t ff) signb() uint64 { return 1 << (t.e + t.f) }
func (t ff) mk(s, e, m uint64) uint64 {
	return s<<(t.e+t.f) | (e&t.emax())<<t.f | m&t.fmask()
}
func (t ff) neg(x uint64) uint64 { return x ^ t.signb() }
func (t ff) width() int {
	if t == fS {
		return 32
	}
	return 64
}

// fl is the encoding of x; ok=false when x is not exact in t.
func (t ff) fl(x float64) (uint64, bool) {
	if t == fS {
		v := float32(x)
		return uint64(math.Float32bits(v)), float64(v) == x
	}
	return math.Float64bits(x), true
}

func (t ff) special() []uint64 {
	one, _ := t.fl(1.5)
	m3, _ := t.fl(-3)
	return []uint64{
		t.mk(0, 0, 0), t.mk(1, 0, 0), t.mk(0, t.emax(), 0), t.mk(1, t.emax(), 0),
		one, m3, t.mk(1, 0, 5), t.mk(0, 0, t.fmask()), t.mk(0, 1, 0), t.mk(1, t.emax()-1, t.fmask()),
		t.mk(1, t.emax(), t.qbit()), // the indefinite
		t.mk(0, t.emax(), t.qbit()|0x1234), t.mk(0, t.emax(), 0x21), t.mk(1, t.emax(), 7),
	}
}

const (
	daz = 1 << 6
	ftz = 1 << 15
)

func rc(k uint32) uint32 { return k << 13 }

// masks: the exception mask field (bits 12:7) for the 6-bit set of masked exceptions.
func masks(m uint32) uint32 { return (m & 0x3F) << 7 }

type emitter struct {
	w    *bufio.Writer
	enc  *json.Encoder
	id   int
	r    *rand.Rand
	only *regexp.Regexp
	n    map[string]int
}

func (e *emitter) base() gen.State {
	var s gen.State
	for i := range s.Regs {
		s.Regs[i] = e.r.Uint64()
	}
	s.Regs[4] = L.DataBase + 1024 + 8*uint64(e.r.IntN(256))
	s.RFlags = gen.RandFlags(e.r)
	s.Seed = uint64(e.r.IntN(1 << 20))
	for i := range s.XMM {
		s.XMM[i] = [2]uint64{e.r.Uint64(), e.r.Uint64()}
	}
	return s
}

// emit: XMM1 = a (destination / first source), XMM2 = b, GPR 2 (RDX) = x for integer sources.
func (e *emitter) emit(class string, code []byte, t ff, mx uint32, a, b uint64, x uint64) {
	if e.only != nil && !e.only.MatchString(class) {
		return
	}
	s := e.base()
	set := func(i int, v uint64) {
		if t == fS {
			s.XMM[i][0] = s.XMM[i][0]&^0xffffffff | v
		} else {
			s.XMM[i][0] = v
		}
	}
	set(1, a)
	set(2, b)
	s.Regs[2] = x
	if e.r.IntN(2) == 0 {
		mx |= uint32(e.r.IntN(64)) // random initial flags
	}
	s.SetMXCSR(mx)
	c := gen.Case(e.id, class, code, s)
	e.id++
	e.n[class]++
	e.enc.Encode(&c)
}

// mxGrid: all 16 RC x FTZ x DAZ settings with everything masked, then all 64 mask subsets
// under a random RC/FTZ/DAZ.
func (e *emitter) mxGrid() []uint32 {
	var out []uint32
	for k := uint32(0); k < 16; k++ {
		m := rc(k&3) | masks(0x3F)
		if k&4 != 0 {
			m |= ftz
		}
		if k&8 != 0 {
			m |= daz
		}
		out = append(out, m)
	}
	for mk := uint32(0); mk < 64; mk++ {
		m := rc(uint32(e.r.IntN(4))) | masks(mk)
		if e.r.IntN(3) == 0 {
			m |= ftz
		}
		if e.r.IntN(3) == 0 {
			m |= daz
		}
		out = append(out, m)
	}
	return out
}

func pre(t ff) byte {
	if t == fS {
		return 0xF3
	}
	return 0xF2
}

func main() {
	out := flag.String("o", "", "output file")
	seed := flag.Uint64("seed", 1, "seed")
	only := flag.String("only", "", "only classes matching")
	flag.Parse()
	f, err := os.Create(*out)
	if err != nil {
		panic(err)
	}
	e := &emitter{w: bufio.NewWriter(f), r: rand.New(rand.NewPCG(*seed, 99)), n: map[string]int{}}
	e.enc = json.NewEncoder(e.w)
	if *only != "" {
		e.only = regexp.MustCompile(*only)
	}
	fmts := []ff{fS, fD}
	const mrr = 0xCA // ModRM: reg = XMM1, rm = XMM2

	// X64-ARITH: ADD MUL SUB DIV SQRT MIN MAX SD/SS over the special grid, every mask subset.
	for _, t := range fmts {
		g := t.special()
		for _, op := range []byte{0x58, 0x59, 0x5C, 0x5E, 0x51, 0x5D, 0x5F} {
			code := []byte{pre(t), 0x0F, op, mrr}
			for _, a := range g {
				for _, b := range g {
					for _, mx := range e.mxGrid() {
						e.emit("rtfp.x.arith.grid", code, t, mx, a, b, 0)
					}
				}
			}
		}
	}
	// X64-MULTI: operand pairs that raise several exceptions at once (DE with UE/PE, OE with PE,
	// ZE with DE, IE with DE, tiny exact results), every mask subset x RC x FTZ x DAZ.
	for _, t := range fmts {
		one := t.mk(0, (1<<(t.e-1))-2, t.fmask()) // 1 - ulp/2
		big := t.mk(0, t.emax()-1, t.fmask())
		two, _ := t.fl(2)
		three, _ := t.fl(3)
		pairs := [][2]uint64{
			{t.mk(0, 1, 0), one}, {t.mk(0, 1, 3), one}, {t.mk(0, 0, 9), one}, {t.mk(0, 0, 8), t.mk(0, (1<<(t.e-1))-2, 0)},
			{big, two}, {big, big}, {two, three}, {t.mk(0, 0, 3), t.mk(0, 0, 0)}, {t.mk(0, t.emax(), 1), t.mk(0, 0, 3)},
			{t.mk(0, 0, 3), t.mk(0, t.emax(), 1)}, {t.mk(0, 0, 0), t.mk(0, 0, 0)}, {t.mk(0, t.emax(), 0), t.mk(0, 0, 3)},
			{t.mk(1, 0, 3), t.mk(0, 0, 0)}, {t.mk(0, 1, 0), t.mk(1, 0, 1)}, {t.mk(0, 0, 4), t.mk(0, (1<<(t.e-1))-2, 0)},
		}
		for _, op := range []byte{0x58, 0x59, 0x5C, 0x5E, 0x51, 0x5D, 0x5F} {
			code := []byte{pre(t), 0x0F, op, mrr}
			for _, p := range pairs {
				for mk := uint32(0); mk < 64; mk++ {
					for k := 0; k < 4; k++ {
						m := rc(uint32(e.r.IntN(4))) | masks(mk)
						if k&1 != 0 {
							m |= ftz
						}
						if k&2 != 0 {
							m |= daz
						}
						e.emit("rtfp.x.multi", code, t, m, p[0], p[1], 0)
					}
				}
			}
		}
	}
	// X64-COMI: UCOMISD/COMISD/UCOMISS/COMISS over the grid, every mask subset (flags, IE/DE).
	for _, t := range fmts {
		g := t.special()
		var p []byte
		if t == fD {
			p = []byte{0x66}
		}
		for _, op := range []byte{0x2E, 0x2F} {
			code := append(append([]byte{}, p...), 0x0F, op, mrr)
			for _, a := range g {
				for _, b := range g {
					for _, mx := range e.mxGrid() {
						e.emit("rtfp.x.comi", code, t, mx, a, b, 0)
					}
				}
			}
		}
	}
	// X64-CMP: CMPSD/CMPSS with every predicate over the grid, DAZ and IE masked or not.
	for _, t := range fmts {
		g := t.special()
		for pr := byte(0); pr < 8; pr++ {
			code := []byte{pre(t), 0x0F, 0xC2, mrr, pr}
			for _, a := range g {
				for _, b := range g {
					for _, mx := range []uint32{masks(0x3F), masks(0x3F) | daz, masks(0x3E), masks(0x3D) | daz, masks(0x3C), masks(0)} {
						e.emit("rtfp.x.cmp", code, t, mx, a, b, 0)
					}
				}
			}
		}
	}
	// X64-CVTSI2F: CVTSI2SD/SS of 32/64-bit integers, negative ones included, at the ties.
	{
		var ints []uint64
		for k := 20; k < 64; k++ {
			p := uint64(1) << k
			for _, d := range []uint64{0, 1, p >> 24, p>>24 + 1, p >> 53, p>>53 + 1, 3 * (p >> 24), 3 * (p >> 53)} {
				ints = append(ints, p+d, p-d, -(p + d), -(p - d))
			}
		}
		ints = append(ints, 0, 1, ^uint64(0), 1<<63, 1<<63|1, 0x80000000, 0xFFFFFFFF80000000, 0x7FFFFFFF, 0xFFFFFFFF)
		for _, t := range fmts {
			for _, w := range []bool{false, true} {
				code := []byte{pre(t), 0x0F, 0x2A, 0xCA} // reg = XMM1, rm = RDX
				if w {
					code = []byte{pre(t), 0x48, 0x0F, 0x2A, 0xCA}
				}
				for _, x := range ints {
					for k := uint32(0); k < 4; k++ {
						for _, m := range []uint32{masks(0x3F), masks(0x1F)} { // PE unmasked too
							e.emit("rtfp.x.cvtsi2f", code, t, rc(k)|m, uint64(e.r.Uint64()), 0, x)
						}
					}
				}
			}
		}
	}
	// X64-CVT2SI: CVTTSD2SI/CVTSD2SI/... to 32/64 bits at +-2^31, +-2^63, 2^64, ties, denormals
	// under DAZ in each rounding mode, NaNs; IE/PE masked or not.
	{
		Ld := math.Ldexp
		for _, t := range fmts {
			var vals []uint64
			add := func(x float64) {
				if v, ok := t.fl(x); ok {
					vals = append(vals, v, t.neg(v))
				}
			}
			for _, k := range []int{31, 32, 63, 64} {
				p := Ld(1, k)
				u := Ld(1, k-int(t.f))
				for _, x := range []float64{p, p + u, p - u/2, p - u, p - 0.5, p - 1, p + 0.5, p - 1.5} {
					add(x)
				}
			}
			for _, x := range []float64{0.5, 1.5, 2.5, 0.25, 0.75, 1, Ld(1, 52) - 0.5, Ld(1, 23) - 0.5, 1e30} {
				add(x)
			}
			vals = append(vals, t.mk(0, 0, 1), t.mk(1, 0, 3), t.mk(0, 0, 0), t.mk(1, 0, 0), t.mk(0, t.emax(), 0),
				t.mk(1, t.emax(), 0), t.mk(1, t.emax(), t.qbit()), t.mk(0, t.emax(), 1))
			for _, op := range []byte{0x2C, 0x2D} {
				for _, w := range []bool{false, true} {
					code := []byte{pre(t), 0x0F, op, 0xC2} // reg = RAX, rm = XMM2
					if w {
						code = []byte{pre(t), 0x48, 0x0F, op, 0xC2}
					}
					for _, v := range vals {
						for k := uint32(0); k < 4; k++ {
							for _, m := range []uint32{masks(0x3F), masks(0x3F) | daz, masks(0x3E), masks(0x1F) | daz, masks(0x3D)} {
								e.emit("rtfp.x.cvt2si", code, t, rc(k)|m, 0, v, 0)
							}
						}
					}
				}
			}
		}
	}
	// X64-CVTFF: CVTSD2SS at the single underflow/overflow boundaries and ties, NaN payloads;
	// CVTSS2SD of S denormals and NaNs; every RC x FTZ x DAZ, UE/OE/PE unmasked.
	{
		Ld := math.Ldexp
		mn := Ld(1, -126)
		maxS := Ld(2-Ld(1, -23), 127)
		var dv []uint64
		for _, x := range []float64{
			mn, mn - Ld(1, -150), mn - Ld(1, -151), mn - Ld(1, -152), mn - Ld(1, -149), mn + Ld(1, -151),
			mn - Ld(1, -151) - Ld(1, -200), mn - Ld(1, -151) + Ld(1, -200), Ld(1, -149), Ld(1, -150),
			Ld(1, -150) + Ld(1, -200), Ld(1, -151), Ld(3, -151), maxS, maxS + Ld(1, 103), maxS + Ld(1, 103) - Ld(1, 60),
			maxS + Ld(1, 102), Ld(1, 128), 1 + Ld(1, -24), 1 + Ld(3, -24),
		} {
			v, _ := fD.fl(x)
			dv = append(dv, v, fD.neg(v))
		}
		dv = append(dv, fD.mk(0, 0, 1), fD.mk(1, 0, fD.fmask()), fD.mk(0, fD.emax(), fD.qbit()|1),
			fD.mk(1, fD.emax(), 1<<28), fD.mk(0, fD.emax(), 1<<29), fD.mk(0, fD.emax(), 1), fD.mk(1, fD.emax(), 0))
		sv := []uint64{fS.mk(0, 0, 1), fS.mk(1, 0, fS.fmask()), fS.mk(0, fS.emax(), 1), fS.mk(1, fS.emax(), fS.qbit()|0x3FFFFF),
			fS.mk(0, fS.emax(), 0x200000), fS.mk(1, 1, 0)}
		mxs := func() []uint32 {
			var o []uint32
			for k := uint32(0); k < 16; k++ {
				m := rc(k&3) | masks(0x3F)
				if k&4 != 0 {
					m |= ftz
				}
				if k&8 != 0 {
					m |= daz
				}
				o = append(o, m)
			}
			for _, mk := range []uint32{0x2F, 0x37, 0x3B, 0x1F, 0x3D, 0x3E, 0x07, 0} {
				o = append(o, rc(uint32(e.r.IntN(4)))|masks(mk)|uint32(e.r.IntN(2))*ftz)
			}
			return o
		}
		for _, v := range dv {
			for _, m := range mxs() {
				e.emit("rtfp.x.cvtff", []byte{0xF2, 0x0F, 0x5A, mrr}, fD, m, e.r.Uint64(), v, 0)
			}
		}
		for _, v := range sv {
			for _, m := range mxs() {
				e.emit("rtfp.x.cvtff", []byte{0xF3, 0x0F, 0x5A, mrr}, fS, m, e.r.Uint64(), v, 0)
			}
		}
	}
	// X64-ROUND: ROUNDSD/ROUNDSS with every imm8 low nibble on ties, denormals (DAZ), NaNs.
	{
		Ld := math.Ldexp
		for _, t := range fmts {
			var vals []uint64
			add := func(x float64) {
				if v, ok := t.fl(x); ok {
					vals = append(vals, v, t.neg(v))
				}
			}
			for _, x := range []float64{0.5, 1.5, 2.5, 0.25, 0.75, 0.5 - Ld(1, -25), Ld(1, 23) - 0.5, Ld(1, 52) - 0.5, Ld(1, 53), 1e30} {
				add(x)
			}
			vals = append(vals, t.mk(0, 0, 1), t.mk(1, 0, 3), t.mk(0, 0, 0), t.mk(1, 0, 0), t.mk(0, t.emax(), 0),
				t.mk(1, t.emax(), t.qbit()), t.mk(0, t.emax(), 1))
			op := byte(0x0B)
			if t == fS {
				op = 0x0A
			}
			for imm := byte(0); imm < 16; imm++ {
				code := []byte{0x66, 0x0F, 0x3A, op, mrr, imm}
				for _, v := range vals {
					for k := uint32(0); k < 4; k++ {
						for _, m := range []uint32{masks(0x3F), masks(0x3F) | daz, masks(0x1F), masks(0x3E) | daz, masks(0x3D) | daz} {
							e.emit("rtfp.x.round", code, t, rc(k)|m, e.r.Uint64(), v, 0)
						}
					}
				}
			}
		}
	}
	// DEC-X64: legacy-prefix and REX combinations (repeated, reordered, mixed mandatory
	// prefixes, REX before a legacy prefix, address-size, segment, LOCK) on every SSE opcode
	// of the 0F map the FP decoder handles and their neighbours; a register and a memory form.
	{
		pfx := [][]byte{{}, {0x66}, {0xF2}, {0xF3}, {0xF0}, {0x66, 0xF2}, {0xF2, 0x66}, {0xF3, 0xF2}, {0xF2, 0xF3},
			{0xF2, 0xF2}, {0xF3, 0xF3}, {0x66, 0x66}, {0x2E, 0xF2}, {0xF2, 0x2E}, {0x3E, 0xF3}, {0x64, 0xF2},
			{0xF2, 0x64}, {0x26, 0xF2}, {0x36, 0xF3}, {0xF2, 0x40}, {0xF2, 0x48}, {0xF2, 0x41}, {0xF2, 0x4C},
			{0xF3, 0x48}, {0x66, 0x48}, {0x48}, {0x40, 0xF2}, {0x48, 0xF2}, {0xF2, 0x48, 0x48}, {0xF2, 0x66, 0x48},
			{0x66, 0xF3, 0x48}, {0x67, 0xF2}, {0xF2, 0x67}, {0xF0, 0xF2}, {0xF2, 0xF0}, {0x66, 0x67}, {0x66, 0x4A},
			{0xF3, 0x66}, {0x66, 0xF3}}
		var ops [][]byte
		for _, o := range []byte{0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D,
			0x2E, 0x2F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E,
			0x5F, 0xC2, 0xE6, 0xD6, 0x7E, 0xD0, 0x7C, 0x7D} {
			ops = append(ops, []byte{0x0F, o})
		}
		for _, o := range []byte{0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D} {
			ops = append(ops, []byte{0x0F, 0x3A, o})
		}
		for _, p := range pfx {
			for _, op := range ops {
				for _, mod := range [][]byte{{0xCA}, {0x4C, 0x24, 0x10}, {0xC1}} {
					code := append(append(append([]byte{}, p...), op...), mod...)
					if op[len(op)-1] == 0xC2 || len(op) == 3 {
						code = append(code, byte(e.r.IntN(8)))
					}
					if !gen.OK(code) {
						continue
					}
					for k := 0; k < 3; k++ {
						t := fD
						if k == 1 {
							t = fS
						}
						g := t.special()
						m := masks(0x3F) | rc(uint32(e.r.IntN(4)))
						if k == 2 {
							m = uint32(e.r.IntN(1 << 16)) & 0xFFFF
						}
						e.emit("rtfp.x.prefix", code, t, m, g[e.r.IntN(len(g))], g[e.r.IntN(len(g))], e.r.Uint64())
					}
				}
			}
		}
	}
	e.w.Flush()
	f.Close()
	tot := 0
	for k, v := range e.n {
		fmt.Fprintf(os.Stderr, "%-20s %d\n", k, v)
		tot += v
	}
	fmt.Fprintf(os.Stderr, "total %d\n", tot)
}
