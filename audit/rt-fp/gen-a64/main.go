// Command gena64 writes the arm64 floating-point red-team corpus (docs/AUDIT-FP.md, rows
// A64-*): systematic grids of special operands crossed with FPCR modes the random corpus of
// scripts/oracle.sh fp samples only sparsely. Every case is an ordinary oracle case (one
// instruction, layout.Case JSON per line), run by `oracle run` against qemu and replayed on Sail.
//
//	gena64 -o cases.jsonl [-seed 1] [-only REGEX] [-scale 1]
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

	"github.com/Giulio2002/Janus/oracle/gen"
	L "github.com/Giulio2002/Janus/oracle/layout"
)

type ff struct{ e, f uint }

var (
	fS = ff{8, 23}
	fD = ff{11, 52}
)

func (t ff) bias() uint64  { return 1<<(t.e-1) - 1 }
func (t ff) emax() uint64  { return 1<<t.e - 1 }
func (t ff) fmask() uint64 { return 1<<t.f - 1 }
func (t ff) qbit() uint64  { return 1 << (t.f - 1) }
func (t ff) signb() uint64 { return 1 << (t.e + t.f) }
func (t ff) mk(s, e, m uint64) uint64 {
	return s<<(t.e+t.f) | (e&t.emax())<<t.f | m&t.fmask()
}

// fl is the encoding of the exactly representable value x (Ldexp-built).
func (t ff) fl(x float64) uint64 {
	if t == fS {
		v := float32(x)
		if float64(v) != x && !math.IsNaN(x) {
			panic(fmt.Sprintf("not exact in S: %g", x))
		}
		return uint64(math.Float32bits(v))
	}
	return math.Float64bits(x)
}

func (t ff) neg(x uint64) uint64 { return x ^ t.signb() }

// special is the operand grid for NaN/sign/infinity/zero/denormal combinations.
func (t ff) special() []uint64 {
	return []uint64{
		t.mk(0, 0, 0), t.mk(1, 0, 0), // +0 -0
		t.mk(0, t.emax(), 0), t.mk(1, t.emax(), 0), // +inf -inf
		t.fl(1.5), t.fl(-3.0),
		t.mk(1, 0, 5),                      // negative denormal
		t.mk(0, t.emax(), t.qbit()|0x1234), // +qNaN payload
		t.mk(1, t.emax(), t.qbit()|0x55),   // -qNaN payload
		t.mk(0, t.emax(), 0x21),            // +sNaN payload
		t.mk(1, t.emax(), 7),               // -sNaN payload
	}
}

// grid2 adds two more values for the 2-source grids: the min normal and a positive denormal.
func (t ff) grid2() []uint64 {
	return append(t.special(), t.mk(0, 1, 0), t.mk(0, 0, t.fmask()))
}

const (
	bFIZ = 1 << 0
	bAH  = 1 << 1
	bNEP = 1 << 2
	bFZ  = 1 << 24
	bDN  = 1 << 25
)

// fpcrAll: every RMode crossed with every subset of FZ, DN, AH, FIZ (64 values).
func fpcrAll() []uint32 {
	var out []uint32
	for rm := uint32(0); rm < 4; rm++ {
		for k := 0; k < 16; k++ {
			v := rm << 22
			for i, b := range []uint32{bFZ, bDN, bAH, bFIZ} {
				if k>>i&1 == 1 {
					v |= b
				}
			}
			out = append(out, v)
		}
	}
	return out
}

// fpcrSome: RMode RNE/RMI crossed with the flag subsets that matter most together.
func fpcrSome() []uint32 {
	var out []uint32
	for _, rm := range []uint32{0, 2} {
		for _, f := range []uint32{0, bFZ, bDN, bAH, bFIZ, bFZ | bDN, bFZ | bAH, bDN | bAH, bFZ | bDN | bAH,
			bFZ | bDN | bAH | bFIZ, bFIZ | bAH, bNEP | bAH | bDN} {
			out = append(out, rm<<22|f)
		}
	}
	return out
}

type emitter struct {
	w    *bufio.Writer
	enc  *json.Encoder
	id   int
	r    *rand.Rand
	only *regexp.Regexp
	n    map[string]int
}

// emit writes one case: V0..V31 get random contents (so merging and zeroing are visible),
// then the operands are placed; FPSR starts at 0 or random cumulative flags.
func (e *emitter) emit(class string, w uint32, t ff, fpcr uint32, ops map[int]uint64, xs map[int]uint64) {
	if e.only != nil && !e.only.MatchString(class) {
		return
	}
	var s gen.State
	for i := range s.X {
		s.X[i] = e.r.Uint64()
	}
	s.SP = L.DataBase + 16*uint64(16+e.r.IntN(224))
	s.NZCV = e.r.IntN(16)
	for i := range s.V {
		s.V[i] = [2]uint64{e.r.Uint64(), e.r.Uint64()}
	}
	for i, v := range ops {
		if t == fS {
			s.V[i][0] = s.V[i][0]&^0xffffffff | v
		} else {
			s.V[i][0] = v
		}
	}
	for i, v := range xs {
		s.X[i] = v
	}
	s.FPCR = fpcr
	if e.r.IntN(2) == 0 {
		s.FPSR = uint32(e.r.Uint64() & 0x9F)
	}
	c := gen.Case(e.id, class, w, s)
	e.id++
	e.n[class]++
	e.enc.Encode(&c)
}

func ftype(t ff) uint32 {
	if t == fS {
		return 0
	}
	return 1
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
	e := &emitter{w: bufio.NewWriter(f), r: rand.New(rand.NewPCG(*seed, 77)), n: map[string]int{}}
	e.enc = json.NewEncoder(e.w)
	if *only != "" {
		e.only = regexp.MustCompile(*only)
	}
	fmts := []ff{fS, fD}

	// A64-FMA: FMADD/FMSUB/FNMADD/FNMSUB over the special grid cubed (sign, NaN selection with
	// the addend first, AH's own NaN rules, invalid 0*inf + qNaN, -0 results).
	for _, t := range fmts {
		sp := t.special()
		for o := uint32(0); o < 4; o++ {
			w := 0x1F000000 | ftype(t)<<22 | (o>>1)<<21 | 2<<16 | (o&1)<<15 | 3<<10 | 1<<5 | 0
			for _, a := range sp {
				for _, n := range sp {
					for _, m := range sp {
						for _, c := range fpcrSome() {
							e.emit("rtfp.fma.grid", w, t, c, map[int]uint64{3: a, 1: n, 2: m}, nil)
						}
					}
				}
			}
		}
	}
	// A64-FMA-ZERO: exact cancellation a*b + c = 0 (sign from the rounding mode, and from
	// FNMADD/FNMSUB negation), and tiny fused results at the underflow boundary.
	for _, t := range fmts {
		for o := uint32(0); o < 4; o++ {
			w := 0x1F000000 | ftype(t)<<22 | (o>>1)<<21 | 2<<16 | (o&1)<<15 | 3<<10 | 1<<5 | 0
			for _, c := range fpcrAll() {
				for _, sg := range []float64{1, -1} {
					// 3 * 5 - 15
					e.emit("rtfp.fma.cancel", w, t, c, map[int]uint64{1: t.fl(3 * sg), 2: t.fl(5), 3: t.fl(-15 * sg)}, nil)
					e.emit("rtfp.fma.cancel", w, t, c, map[int]uint64{1: t.fl(3 * sg), 2: t.fl(5), 3: t.fl(15 * sg)}, nil)
					// zero product + zero addend of either sign
					e.emit("rtfp.fma.cancel", w, t, c, map[int]uint64{1: t.fl(0) | t.signb()*uint64(b2i(sg < 0)), 2: t.fl(5), 3: t.fl(0)}, nil)
					e.emit("rtfp.fma.cancel", w, t, c, map[int]uint64{1: t.fl(0) | t.signb()*uint64(b2i(sg < 0)), 2: t.fl(5), 3: t.neg(t.fl(0))}, nil)
				}
				// tiny: minNormal * (1 - ulp) + tiny of either sign, and the product alone
				mn := t.mk(0, 1, 0)
				one := t.mk(0, t.bias()-1, t.fmask()) // 1 - ulp/2
				for _, a := range []uint64{t.mk(0, 0, 0), t.mk(1, 0, 1), t.mk(0, 0, 1), t.mk(1, 0, 3)} {
					e.emit("rtfp.fma.tiny", w, t, c, map[int]uint64{1: mn, 2: one, 3: a}, nil)
					e.emit("rtfp.fma.tiny", w, t, c, map[int]uint64{1: t.mk(0, 1, 1), 2: one, 3: a}, nil)
				}
			}
		}
	}

	// A64-DP2: FMUL FDIV FADD FSUB FMAX FMIN FMAXNM FMINNM FNMUL over the 13x13 grid.
	for _, t := range fmts {
		g := t.grid2()
		for op := uint32(0); op <= 8; op++ {
			w := 0x1E200800 | ftype(t)<<22 | 2<<16 | op<<12 | 1<<5 | 0
			for _, a := range g {
				for _, b := range g {
					for _, c := range fpcrSome() {
						e.emit("rtfp.dp2.grid", w, t, c, map[int]uint64{1: a, 2: b}, nil)
					}
				}
			}
			// underflow boundary: minNormal * (1 - k ulp) (tiny before rounding, maybe not after),
			// minNormal - tiny, and their quotients, under every FPCR
			mn := t.mk(0, 1, 0)
			for _, c := range fpcrAll() {
				for k := uint64(0); k < 3; k++ {
					for _, sg := range []uint64{0, 1} {
						one := t.mk(sg, t.bias()-1, t.fmask()-k)
						e.emit("rtfp.dp2.tiny", w, t, c, map[int]uint64{1: t.mk(0, 1, k), 2: one}, nil)
						e.emit("rtfp.dp2.tiny", w, t, c, map[int]uint64{1: mn, 2: t.mk(sg^1, 0, 1+k)}, nil)
						e.emit("rtfp.dp2.tiny", w, t, c, map[int]uint64{1: t.mk(sg, 1, k), 2: t.mk(0, t.bias(), 1+k)}, nil)
					}
				}
			}
		}
	}

	// A64-CMP: FCMP / FCMP #0 / FCMPE / FCMPE #0 over the grid; FZ/FIZ make denormals equal 0.
	for _, t := range fmts {
		g := t.grid2()
		for opc := uint32(0); opc < 4; opc++ {
			for _, a := range g {
				for _, b := range g {
					rm := uint32(2)
					if opc&1 == 1 {
						rm = 0
					}
					w := 0x1E202000 | ftype(t)<<22 | rm<<16 | 1<<5 | opc<<3
					for _, c := range []uint32{0, bFZ, bFIZ, bAH, bFZ | bAH, bDN | bAH | bFIZ} {
						e.emit("rtfp.cmp.grid", w, t, c, map[int]uint64{1: a, 2: b}, nil)
					}
				}
			}
		}
	}

	// A64-SQRT: FSQRT of -0, negative denormals (flushed or not), -inf, NaNs, under every FPCR.
	for _, t := range fmts {
		w := 0x1E204000 | ftype(t)<<22 | 3<<15 | 1<<5 | 0
		vals := append(t.grid2(), t.mk(1, 1, 0), t.mk(1, 0, t.fmask()), t.fl(4), t.fl(2), t.mk(0, t.emax()-1, t.fmask()))
		for _, v := range vals {
			for _, c := range fpcrAll() {
				e.emit("rtfp.sqrt", w, t, c, map[int]uint64{1: v}, nil)
				e.emit("rtfp.sqrt", w, t, c|bNEP, map[int]uint64{1: v}, nil)
			}
		}
	}

	// A64-FCVT: D->S at the single-precision underflow and overflow boundaries (tininess before
	// vs after rounding: FZ with AH 0/1), ties, D denormals, NaN payloads in the truncated bits;
	// S->D of S denormals and NaN payloads.
	{
		d2s := uint32(0x1E204000) | 1<<22 | 4<<15 | 1<<5 | 0
		s2d := uint32(0x1E204000) | 0<<22 | 5<<15 | 1<<5 | 0
		L := math.Ldexp
		mn := L(1, -126)
		maxS := L(2-L(1, -23), 127)
		var dv []uint64
		for _, x := range []float64{
			mn, mn - L(1, -150), mn - L(1, -151), mn - L(1, -152), mn - L(1, -149), mn + L(1, -151),
			mn - L(3, -152), mn - L(1, -151) - L(1, -200), mn - L(1, -151) + L(1, -200),
			L(1, -149), L(1, -150), L(1, -150) + L(1, -200), L(1, -151), L(3, -151), L(5, -151), L(1, -149) - L(1, -200),
			maxS, maxS + L(1, 103), maxS + L(1, 103) - L(1, 60), maxS + L(1, 103) + L(1, 60), maxS + L(1, 102), L(1, 128),
			1 + L(1, -24), 1 + L(3, -24), 1 + L(1, -24) + L(1, -50), 1 - L(1, -25), 1.5, 3,
		} {
			dv = append(dv, fD.fl(x), fD.neg(fD.fl(x)))
		}
		dv = append(dv, fD.mk(0, 0, 1), fD.mk(1, 0, fD.fmask()), fD.mk(0, 0, 0), fD.mk(1, 0, 0),
			fD.mk(0, fD.emax(), 0), fD.mk(1, fD.emax(), 0),
			fD.mk(0, fD.emax(), fD.qbit()|1), fD.mk(1, fD.emax(), 1<<28), fD.mk(0, fD.emax(), 1<<29), fD.mk(0, fD.emax(), 1),
			fD.mk(1, fD.emax(), fD.qbit()|0x1FFFFFFF), fD.mk(0, fD.emax(), fD.fmask()), fD.mk(1, fD.emax(), 0x2AAAAAAAAAAAA))
		for _, v := range dv {
			for _, c := range fpcrAll() {
				e.emit("rtfp.fcvt.d2s", d2s, fD, c, map[int]uint64{1: v}, nil)
			}
			e.emit("rtfp.fcvt.d2s", d2s, fD, bNEP|bAH, map[int]uint64{1: v}, nil)
		}
		sv := []uint64{fS.mk(0, 0, 1), fS.mk(1, 0, fS.fmask()), fS.mk(0, 0, 0x400000), fS.mk(1, 1, 0),
			fS.mk(0, fS.emax(), 1), fS.mk(1, fS.emax(), fS.qbit()|0x3FFFFF), fS.mk(0, fS.emax(), 0x200000), fS.mk(1, fS.emax(), 0),
			fS.mk(0, fS.emax()-1, fS.fmask())}
		for _, v := range sv {
			for _, c := range fpcrAll() {
				e.emit("rtfp.fcvt.s2d", s2d, fS, c, map[int]uint64{1: v}, nil)
			}
		}
	}

	// A64-CVTINT: FCVT{N,P,M,Z,A}{S,U} to W and X at the exact integer boundaries (+-2^31,
	// +-2^63, 2^32, 2^64 and one ulp either side, 2^64 - 0.5ulp, ties at .5).
	{
		type rmop struct{ rm, op uint32 }
		forms := []rmop{{0, 0}, {0, 1}, {1, 0}, {1, 1}, {2, 0}, {2, 1}, {3, 0}, {3, 1}, {0, 4}, {0, 5}}
		L := math.Ldexp
		for _, t := range fmts {
			var vals []uint64
			add := func(x float64) {
				if t == fS && float64(float32(x)) != x {
					return
				}
				vals = append(vals, t.fl(x), t.neg(t.fl(x)))
			}
			for _, k := range []int{31, 32, 63, 64} {
				p := L(1, k)
				u := L(1, k-int(t.f)) // ulp at 2^k
				add(p)
				add(p + u)
				add(p - u/2)
				add(p - u)
				add(p + 2*u)
				add(p - 0.5)
				add(p - 1)
				add(p + 0.5)
				add(p - 1.5)
			}
			for _, x := range []float64{0.5, 1.5, 2.5, 3.5, 0.25, 0.75, 1, 2, L(1, 23) - 0.5, L(1, 23) + 1, L(1, 52) - 0.5,
				L(1, 52) + 1, L(1, 22) + 0.5, 1 - L(1, -24), 0.5 + L(1, -24), L(1, 53), 1e30, L(1, -1022), L(1, -126), 4294967295.5} {
				add(x)
			}
			vals = append(vals, t.mk(0, 0, 1), t.mk(1, 0, 3), t.mk(0, 0, 0), t.mk(1, 0, 0), t.mk(0, t.emax(), 0),
				t.mk(1, t.emax(), 0), t.mk(0, t.emax(), t.qbit()), t.mk(1, t.emax(), 1))
			for _, sf := range []uint32{0, 1} {
				for _, fm := range forms {
					w := sf<<31 | 0x1E200000 | ftype(t)<<22 | fm.rm<<19 | fm.op<<16 | 1<<5 | 0
					for _, v := range vals {
						for _, c := range []uint32{0, bFZ, bFIZ, bAH, bFZ | bAH, 3 << 22} {
							e.emit("rtfp.cvt.f2i", w, t, c, map[int]uint64{1: v}, nil)
						}
					}
				}
			}
		}
		// SCVTF/UCVTF of integers at the rounding ties of S and D, all rounding modes
		var ints []uint64
		for k := 20; k < 64; k++ {
			p := uint64(1) << k
			for _, d := range []uint64{0, 1, p >> 24, p>>24 + 1, p>>24 - 1, p >> 53, p>>53 + 1, 3 * (p >> 24), 3 * (p >> 53)} {
				ints = append(ints, p+d, p-d, -(p + d), -(p - d))
			}
		}
		ints = append(ints, 0, 1, ^uint64(0), 1<<63, 1<<63|1, 1<<64-1<<10, 1<<64-1<<39, 1<<64-1<<40)
		for _, t := range fmts {
			for _, sf := range []uint32{0, 1} {
				for _, op := range []uint32{2, 3} {
					w := sf<<31 | 0x1E200000 | ftype(t)<<22 | op<<16 | 1<<5 | 0
					for _, x := range ints {
						for rm := uint32(0); rm < 4; rm++ {
							e.emit("rtfp.cvt.i2f", w, t, rm<<22|uint32(e.r.IntN(2))*bNEP, nil, map[int]uint64{1: x})
						}
					}
				}
			}
		}
	}

	// A64-FRINT: FRINT{N,P,M,Z,A,X,I} ties and near-ties at every magnitude, denormals, NaNs.
	{
		L := math.Ldexp
		for _, t := range fmts {
			var vals []uint64
			add := func(x float64) {
				if t == fS && float64(float32(x)) != x {
					return
				}
				vals = append(vals, t.fl(x), t.neg(t.fl(x)))
			}
			for _, x := range []float64{0.5, 1.5, 2.5, 3.5, 0.25, 0.75, 1.25, 0.5 - L(1, -25), 0.5 + L(1, -23),
				L(1, 22) + 0.5, L(1, 23) - 0.5, L(1, 23) + 1, L(1, 24) + 2, L(1, 51) + 0.5, L(1, 52) - 0.5, L(1, 52) + 1,
				L(1, 53), 1e300, L(1, -126), L(1, -1022), 1, 2, 4097.5, 4098.5} {
				add(x)
			}
			vals = append(vals, t.mk(0, 0, 1), t.mk(1, 0, t.fmask()), t.mk(0, 0, 0), t.mk(1, 0, 0), t.mk(0, t.emax(), 0),
				t.mk(1, t.emax(), 0), t.mk(0, t.emax(), t.qbit()|3), t.mk(1, t.emax(), 5))
			for _, op := range []uint32{8, 9, 10, 11, 12, 14, 15} {
				w := 0x1E204000 | ftype(t)<<22 | op<<15 | 1<<5 | 0
				for _, v := range vals {
					for rm := uint32(0); rm < 4; rm++ {
						for _, fl := range []uint32{0, bFZ, bAH, bFIZ, bFZ | bAH, bDN} {
							e.emit("rtfp.frint", w, t, rm<<22|fl, map[int]uint64{1: v}, nil)
						}
					}
				}
			}
		}
	}

	e.w.Flush()
	f.Close()
	tot := 0
	for k, v := range e.n {
		fmt.Fprintf(os.Stderr, "%-18s %d\n", k, v)
		tot += v
	}
	fmt.Fprintf(os.Stderr, "total %d\n", tot)
}

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}
