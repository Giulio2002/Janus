package gen

import (
	"fmt"
	"math/rand/v2"

	L "github.com/Giulio2002/Janus/oracle/layout"
)

// DCZID is the DCZID_EL0 value written into every case: the reference machine's own (the
// runner prints it with -dczid; qemu -cpu max reports 7). Set from the gen/harvest flag.
var DCZID = 7

// State is the initial machine state of one case.
type State struct {
	X     [31]uint64
	SP    uint64
	NZCV  int
	Seed  uint64
	V     [32][2]uint64 // V0..V31 as (low, high) 64-bit halves
	TPIDR uint64
	FPCR  uint32
	FPSR  uint32
}

// vecEdge are edge 64-bit halves for vector registers.
var vecEdge = []uint64{0, ^uint64(0), 0x8000000000000000, 0x7fffffffffffffff, 0x8080808080808080,
	0x7f7f7f7f7f7f7f7f, 0x0101010101010101, 0x8000800080008000, 0x8000000080000000,
	0x00000000ffffffff, 0xff00ff00ff00ff00, 0x0f0e0d0c0b0a0908, 0x0706050403020100}

// vecHalf draws one 64-bit half of a vector register: random, edge values, or bytes from a
// small alphabet (so that element comparisons hit equal elements).
func vecHalf(r *rand.Rand, alpha []byte) uint64 {
	switch p := r.IntN(100); {
	case p < 35:
		return r.Uint64()
	case p < 55:
		return vecEdge[r.IntN(len(vecEdge))]
	default:
		var v uint64
		for k := 0; k < 8; k++ {
			v = v<<8 | uint64(alpha[r.IntN(len(alpha))])
		}
		return v
	}
}

// setupV fills the vector registers. A third of them are copies of another register with a
// few bytes changed, so equal/unequal element pairs are both common.
func setupV(r *rand.Rand, s *State) {
	alpha := []byte{0, 1, 0x7f, 0x80, 0xfe, 0xff, byte(r.IntN(256)), byte(r.IntN(256))}
	for i := range s.V {
		s.V[i] = [2]uint64{vecHalf(r, alpha), vecHalf(r, alpha)}
	}
	for i := range s.V {
		if r.IntN(3) == 0 {
			v := s.V[r.IntN(32)]
			for k := r.IntN(3); k > 0; k-- {
				h, b := r.IntN(2), r.IntN(8)
				v[h] ^= uint64(1+r.IntN(255)) << (8 * b)
			}
			s.V[i] = v
		}
	}
}

// Edge values for registers.
var Edge = []uint64{
	0, 1, 2, 3, 31, 32, 63, 64, 0x7f, 0x80, 0xff, 0x100, 0x7fff, 0x8000, 0xffff, 0x10000,
	0x7fffffff, 0x80000000, 0xffffffff, 0x100000000, 0x1_0000_0001,
	0x7fffffffffffffff, 0x8000000000000000, 0x8000000000000001,
	0xffffffffffffffff, 0xfffffffffffffffe, 0xffffffff80000000, 0xffffffff7fffffff,
	0x00000000ffffffff, 0xffffffff00000000, 0x5555555555555555, 0xaaaaaaaaaaaaaaaa,
}

// Value draws a register value: edge values, full-width and 32-bit random values, small
// signed values and pointers into the data buffer.
func Value(r *rand.Rand) uint64 {
	switch p := r.IntN(100); {
	case p < 35:
		return Edge[r.IntN(len(Edge))]
	case p < 60:
		return r.Uint64()
	case p < 72:
		return uint64(r.Uint32())
	case p < 85:
		return uint64(int64(r.IntN(129) - 64))
	default:
		return L.DataBase + uint64(r.IntN(L.DataSize))
	}
}

// pickEA chooses an effective address for an access of `size` bytes: mostly aligned and
// inside the buffer, sometimes straddling its ends, misaligned, or wild.
func pickEA(r *rand.Rand, size uint64) uint64 {
	if size == 0 {
		size = 1
	}
	switch p := r.IntN(100); {
	case p < 80:
		ea := L.DataBase + 256 + uint64(r.IntN(L.DataSize-512))
		return ea &^ (size - 1)
	case p < 86:
		return L.DataBase + L.DataSize - size + uint64(int64(r.IntN(17)-8))
	case p < 92:
		return L.DataBase + uint64(int64(r.IntN(33)-16))
	case p < 97:
		return L.DataBase + 1024 + uint64(r.IntN(64))
	default:
		return Value(r)
	}
}

func sext(v uint64, n int) uint64 { return uint64(int64(v<<(64-n)) >> (64 - n)) }

func memValue(seed, ea uint64, n int) uint64 {
	var v uint64
	for k := n - 1; k >= 0; k-- {
		a := ea + uint64(k)
		var b byte
		if a >= L.DataBase && a < L.DataBase+L.DataSize {
			b = L.Pattern(seed, a-L.DataBase)
		}
		v = v<<8 | uint64(b)
	}
	return v
}

// Setup builds an initial state for word w: random registers, plus class-specific choices
// so memory accesses mostly land in the buffer and register branches in the code page.
func Setup(r *rand.Rand, w uint32) State {
	var s State
	for i := range s.X {
		s.X[i] = Value(r)
	}
	s.SP = L.DataBase + 16*uint64(16+r.IntN(224))
	s.NZCV = r.IntN(16)
	s.Seed = uint64(r.IntN(1 << 20))
	setupV(r, &s)
	s.TPIDR = Value(r)
	if r.IntN(100) < 15 {
		s.FPCR, s.FPSR = RandFPCR(r), RandFPSR(r)
	}
	if IsFP(Classify(w)) {
		setupFP(r, w, &s)
		return s
	}
	rt, rn, rm := bits(w, 4, 0), bits(w, 9, 5), bits(w, 20, 16)
	setBase := func(base uint64) {
		if rn == 31 {
			s.SP = base &^ 15
		} else {
			s.X[rn] = base
		}
	}
	switch Classify(w) {
	case "br.reg":
		if rn != 31 {
			switch p := r.IntN(100); {
			case p < 85:
				k := r.IntN(801) - 400
				if k == 0 {
					k = 2
				}
				s.X[rn] = uint64(int64(L.TestPC) + 4*int64(k))
			case p < 93:
				s.X[rn] = L.TestPC + 8 + uint64(1+r.IntN(3))
			}
		}
	case "br.cmp":
		if r.IntN(100) < 40 && rt != 31 {
			if bits(w, 31, 31) == 0 {
				s.X[rt] &^= 0xffffffff
			} else {
				s.X[rt] = 0
			}
		}
	case "br.test":
		if rt != 31 && r.IntN(2) == 0 {
			s.X[rt] ^= 1 << (bits(w, 31, 31)<<5 | bits(w, 23, 19))
		}
	case "ls.uimm":
		size := bits(w, 31, 30)
		ea := pickEA(r, 1<<size)
		setBase(ea - uint64(bits(w, 21, 10))<<size)
	case "ls.imm9":
		size := bits(w, 31, 30)
		ea := pickEA(r, 1<<size)
		if bits(w, 11, 10) == 1 {
			setBase(ea)
		} else {
			setBase(ea - sext(uint64(bits(w, 20, 12)), 9))
		}
	case "ls.regoff":
		size := bits(w, 31, 30)
		ea := pickEA(r, 1<<size)
		v := uint64(int64(r.IntN(129) - 64))
		if r.IntN(10) == 0 {
			v = Value(r)
		}
		if rm != 31 {
			s.X[rm] = v
		} else {
			v = 0
		}
		var ext uint64
		switch bits(w, 15, 13) {
		case 2:
			ext = uint64(uint32(v))
		case 6:
			ext = sext(uint64(uint32(v)), 32)
		default:
			ext = v
		}
		if bits(w, 12, 12) == 1 {
			ext <<= size
		}
		if rm != rn {
			setBase(ea - ext)
		}
	case "ls.pair":
		scale := uint32(2)
		if bits(w, 31, 30) == 2 {
			scale = 3
		}
		ea := pickEA(r, 1<<scale)
		if bits(w, 24, 23) == 1 {
			setBase(ea)
		} else {
			setBase(ea - sext(uint64(bits(w, 21, 15)), 7)<<scale)
		}
	case "sys.sys":
		if rt != 31 {
			s.X[rt] = pickEA(r, 1)
		}
	case "vls.uimm", "vls.imm9", "vls.regoff":
		scale := bits(w, 23, 23)<<2 | bits(w, 31, 30)
		if scale > 4 {
			scale = 4
		}
		size := uint64(1) << scale
		ea := pickEA(r, size)
		switch Classify(w) {
		case "vls.uimm":
			setBase(ea - uint64(bits(w, 21, 10))<<scale)
		case "vls.imm9":
			if bits(w, 11, 10) == 1 {
				setBase(ea)
			} else {
				setBase(ea - sext(uint64(bits(w, 20, 12)), 9))
			}
		default:
			v := uint64(int64(r.IntN(129) - 64))
			if rm != 31 {
				s.X[rm] = v
			} else {
				v = 0
			}
			var ext uint64
			switch bits(w, 15, 13) {
			case 2:
				ext = uint64(uint32(v))
			case 6:
				ext = sext(uint64(uint32(v)), 32)
			default:
				ext = v
			}
			if bits(w, 12, 12) == 1 {
				ext <<= scale
			}
			if rm != rn {
				setBase(ea - ext)
			}
		}
	case "vls.pair":
		scale := 2 + bits(w, 31, 30)
		ea := pickEA(r, 1<<scale)
		if bits(w, 24, 23) == 1 {
			setBase(ea)
		} else {
			setBase(ea - sext(uint64(bits(w, 21, 15)), 7)<<scale)
		}
	case "vls.multi":
		total := uint64(8) << bits(w, 30, 30) // per register
		switch bits(w, 15, 12) {
		case 0b0010, 0b0000:
			total *= 4
		case 0b0110, 0b0100:
			total *= 3
		case 0b1010, 0b1000:
			total *= 2
		}
		setBase(pickEA(r, total))
		if bits(w, 23, 23) == 1 && rm != 31 && rm != rn {
			s.X[rm] = uint64(int64(r.IntN(257) - 128))
		}
	case "vls.single":
		selem := uint64(bits(w, 13, 13)<<1|bits(w, 21, 21)) + 1
		scale := bits(w, 15, 14)
		if scale == 3 {
			scale = bits(w, 11, 10)
		} else if scale == 2 && bits(w, 10, 10) == 1 {
			scale = 3
		}
		setBase(pickEA(r, selem<<scale))
		if bits(w, 23, 23) == 1 && rm != 31 && rm != rn {
			s.X[rm] = uint64(int64(r.IntN(257) - 128))
		}
	case "simd.tbl":
		regs := int(bits(w, 14, 13)) + 1
		var v [2]uint64
		for h := 0; h < 2; h++ {
			for k := 0; k < 8; k++ {
				v[h] |= uint64(r.IntN(16*regs+12)) << (8 * k)
			}
		}
		if r.IntN(4) != 0 {
			s.V[rm] = v
		}
	case "ls.excl", "ls.atomic":
		size := uint64(1) << bits(w, 31, 30)
		pair := Classify(w) == "ls.excl" && bits(w, 23, 23) == 0 && bits(w, 21, 21) == 1
		total := size
		if pair {
			if bits(w, 31, 31) == 1 { // LDXP/STXP: sz<0> selects 32/64-bit registers
				size = 4 << bits(w, 30, 30)
			} else { // CASP
				size = 4 << bits(w, 30, 30)
			}
			total = 2 * size
		}
		ea := pickEA(r, total)
		setBase(ea)
		// CAS/CASP: make the comparison succeed half of the time.
		if rm != 31 && r.IntN(2) == 0 {
			s.X[rm] = memValue(s.Seed, ea, int(size))
			if pair && rm+1 < 31 {
				s.X[rm+1] = memValue(s.Seed, ea+size, int(size))
			}
		}
	}
	return s
}

// Case renders a state into a layout.Case.
func Case(id int, class string, w uint32, s State) L.Case {
	c := L.Case{ID: id, Class: class, Word: fmt.Sprintf("0x%08x", w), PC: fmt.Sprintf("%#x", L.TestPC),
		SP: fmt.Sprintf("%#x", s.SP), NZCV: s.NZCV, Seed: s.Seed, DCZID: DCZID}
	for i, v := range s.X {
		c.X[i] = fmt.Sprintf("%#x", v)
	}
	c.V = make([]string, 32)
	for i, v := range s.V {
		if v[1] == 0 {
			c.V[i] = fmt.Sprintf("%#x", v[0])
		} else {
			c.V[i] = fmt.Sprintf("0x%x%016x", v[1], v[0])
		}
	}
	c.TPIDR = fmt.Sprintf("%#x", s.TPIDR)
	if s.FPCR != 0 {
		c.FPCR = fmt.Sprintf("%#x", s.FPCR)
	}
	if s.FPSR != 0 {
		c.FPSR = fmt.Sprintf("%#x", s.FPSR)
	}
	return c
}

// vreg draws a vector register number (every value is a valid register).
func vreg(r *rand.Rand) uint32 { return uint32(r.IntN(32)) }

func reg(r *rand.Rand) uint32 {
	if r.IntN(10) == 0 {
		return 31
	}
	return uint32(r.IntN(31))
}

func u(r *rand.Rand, n int) uint32 { return uint32(r.Uint64() & (1<<n - 1)) }

// mostly returns def with probability 9/10 and a random n-bit value otherwise.
func mostly(r *rand.Rand, def uint32, n int) uint32 {
	if r.IntN(10) != 0 {
		return def
	}
	return u(r, n)
}

func smallOff(r *rand.Rand, n int, small int) uint32 {
	if r.IntN(10) < 7 {
		v := r.IntN(2*small+1) - small
		if v == 0 {
			v = 1
		}
		return uint32(v) & (1<<n - 1)
	}
	return u(r, n)
}

func pick(r *rand.Rand, xs ...uint32) uint32 { return xs[r.IntN(len(xs))] }

// Targeted generators per class: fixed opcode bits, random fields biased towards the
// allocated encodings (with a small share of unallocated variants).
var Targeted = map[string]func(r *rand.Rand) uint32{
	"dpi.pcrel": func(r *rand.Rand) uint32 {
		return 0x10000000 | u(r, 1)<<31 | u(r, 2)<<29 | u(r, 19)<<5 | reg(r)
	},
	"dpi.addsub": func(r *rand.Rand) uint32 {
		imm := u(r, 12)
		if r.IntN(4) == 0 {
			imm = pick(r, 0, 1, 0xfff, 0x800)
		}
		return 0x11000000 | u(r, 3)<<29 | u(r, 1)<<22 | imm<<10 | reg(r)<<5 | reg(r)
	},
	"dpi.logical": func(r *rand.Rand) uint32 {
		sf := u(r, 1)
		n := u(r, 1)
		if sf == 0 {
			n = mostly(r, 0, 1)
		}
		return 0x12000000 | sf<<31 | u(r, 2)<<29 | n<<22 | u(r, 6)<<16 | u(r, 6)<<10 | reg(r)<<5 | reg(r)
	},
	"dpi.movewide": func(r *rand.Rand) uint32 {
		sf := u(r, 1)
		opc := pick(r, 0, 2, 3, 0, 2, 3, 0, 2, 3, 1)
		hw := u(r, 2)
		if sf == 0 {
			hw = mostly(r, u(r, 1), 2)
		}
		imm := u(r, 16)
		if r.IntN(4) == 0 {
			imm = pick(r, 0, 1, 0xffff, 0x8000)
		}
		return 0x12800000 | sf<<31 | opc<<29 | hw<<21 | imm<<5 | reg(r)
	},
	"dpi.bitfield": func(r *rand.Rand) uint32 {
		sf := u(r, 1)
		opc := pick(r, 0, 1, 2, 0, 1, 2, 0, 1, 2, 3)
		n := mostly(r, sf, 1)
		w := 6
		if sf == 0 {
			w = 5
		}
		return 0x13000000 | sf<<31 | opc<<29 | n<<22 | mostly(r, u(r, w), 6)<<16 | mostly(r, u(r, w), 6)<<10 | reg(r)<<5 | reg(r)
	},
	"dpi.extract": func(r *rand.Rand) uint32 {
		sf := u(r, 1)
		w := 6
		if sf == 0 {
			w = 5
		}
		return 0x13800000 | sf<<31 | mostly(r, 0, 2)<<29 | mostly(r, sf, 1)<<22 | mostly(r, 0, 1)<<21 |
			reg(r)<<16 | mostly(r, u(r, w), 6)<<10 | reg(r)<<5 | reg(r)
	},
	"br.imm": func(r *rand.Rand) uint32 {
		return 0x14000000 | u(r, 1)<<31 | smallOff(r, 26, 400)
	},
	"br.cond": func(r *rand.Rand) uint32 {
		return 0x54000000 | smallOff(r, 19, 400)<<5 | mostly(r, 0, 1)<<4 | u(r, 4)
	},
	"br.cmp": func(r *rand.Rand) uint32 {
		return 0x34000000 | u(r, 1)<<31 | u(r, 1)<<24 | smallOff(r, 19, 400)<<5 | reg(r)
	},
	"br.test": func(r *rand.Rand) uint32 {
		return 0x36000000 | u(r, 1)<<31 | u(r, 1)<<24 | u(r, 5)<<19 | smallOff(r, 14, 400)<<5 | reg(r)
	},
	"br.reg": func(r *rand.Rand) uint32 {
		if r.IntN(20) == 0 {
			return 0xD6000000 | u(r, 25)
		}
		rn := reg(r)
		if r.IntN(3) == 0 {
			return 0xD65F0000 | rn<<5
		}
		return pick(r, 0xD61F0000, 0xD63F0000) | rn<<5
	},
	"sys.hint": func(r *rand.Rand) uint32 { return 0xD503201F | u(r, 7)<<5 },
	"sys.barrier": func(r *rand.Rand) uint32 {
		return 0xD503301F | u(r, 4)<<8 | u(r, 3)<<5
	},
	"dpr.logical": func(r *rand.Rand) uint32 {
		sf := u(r, 1)
		w := 6
		if sf == 0 {
			w = 5
		}
		return 0x0A000000 | sf<<31 | u(r, 2)<<29 | u(r, 2)<<22 | u(r, 1)<<21 | reg(r)<<16 | mostly(r, u(r, w), 6)<<10 | reg(r)<<5 | reg(r)
	},
	"dpr.addsub": func(r *rand.Rand) uint32 {
		sf := u(r, 1)
		w := 6
		if sf == 0 {
			w = 5
		}
		return 0x0B000000 | sf<<31 | u(r, 2)<<29 | mostly(r, u(r, 1)+u(r, 1), 2)<<22 | reg(r)<<16 | mostly(r, u(r, w), 6)<<10 | reg(r)<<5 | reg(r)
	},
	"dpr.addsubext": func(r *rand.Rand) uint32 {
		return 0x0B200000 | u(r, 3)<<29 | mostly(r, 0, 2)<<22 | reg(r)<<16 | u(r, 3)<<13 | mostly(r, uint32(r.IntN(5)), 3)<<10 | reg(r)<<5 | reg(r)
	},
	"dpr.adc": func(r *rand.Rand) uint32 {
		return 0x1A000000 | u(r, 3)<<29 | reg(r)<<16 | mostly(r, 0, 6)<<10 | reg(r)<<5 | reg(r)
	},
	"dpr.ccmp": func(r *rand.Rand) uint32 {
		return 0x1A400000 | u(r, 2)<<30 | mostly(r, 1, 1)<<29 | reg(r)<<16 | u(r, 4)<<12 | u(r, 1)<<11 |
			mostly(r, 0, 1)<<10 | reg(r)<<5 | mostly(r, 0, 1)<<4 | u(r, 4)
	},
	"dpr.csel": func(r *rand.Rand) uint32 {
		return 0x1A800000 | u(r, 2)<<30 | mostly(r, 0, 1)<<29 | reg(r)<<16 | u(r, 4)<<12 | mostly(r, u(r, 1), 2)<<10 | reg(r)<<5 | reg(r)
	},
	"dpr.dp1": func(r *rand.Rand) uint32 {
		return 0x5AC00000 | u(r, 1)<<31 | mostly(r, 0, 1)<<29 | mostly(r, 0, 5)<<16 | mostly(r, uint32(r.IntN(9)), 6)<<10 | reg(r)<<5 | reg(r)
	},
	"dpr.dp2": func(r *rand.Rand) uint32 {
		op := mostly(r, pick(r, 2, 3, 8, 9, 10, 11, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27), 6)
		return 0x1AC00000 | u(r, 1)<<31 | mostly(r, 0, 1)<<29 | reg(r)<<16 | op<<10 | reg(r)<<5 | reg(r)
	},
	"dpr.dp3": func(r *rand.Rand) uint32 {
		return 0x1B000000 | u(r, 1)<<31 | mostly(r, 0, 2)<<29 | mostly(r, pick(r, 0, 1, 2, 5, 6), 3)<<21 | reg(r)<<16 | u(r, 1)<<15 | reg(r)<<10 | reg(r)<<5 | reg(r)
	},
	"ls.uimm": func(r *rand.Rand) uint32 {
		imm := u(r, 12)
		if r.IntN(2) == 0 {
			imm = u(r, 6)
		}
		return 0x39000000 | u(r, 2)<<30 | u(r, 2)<<22 | imm<<10 | reg(r)<<5 | reg(r)
	},
	"ls.imm9": func(r *rand.Rand) uint32 {
		return 0x38000000 | u(r, 2)<<30 | u(r, 2)<<22 | u(r, 9)<<12 | u(r, 2)<<10 | reg(r)<<5 | reg(r)
	},
	"ls.regoff": func(r *rand.Rand) uint32 {
		return 0x38200800 | u(r, 2)<<30 | u(r, 2)<<22 | reg(r)<<16 | mostly(r, pick(r, 2, 3, 6, 7), 3)<<13 | u(r, 1)<<12 | reg(r)<<5 | reg(r)
	},
	"ls.pair": func(r *rand.Rand) uint32 {
		return 0x28000000 | mostly(r, pick(r, 0, 1, 2), 2)<<30 | u(r, 2)<<23 | u(r, 1)<<22 | smallOff(r, 7, 16)<<15 | reg(r)<<10 | reg(r)<<5 | reg(r)
	},
	"ls.literal": func(r *rand.Rand) uint32 {
		imm := uint32((L.DataBase+uint64(r.IntN(L.DataSize/4))*4-L.TestPC)/4) & 0x7ffff
		if r.IntN(10) == 0 {
			imm = u(r, 19)
		}
		return 0x18000000 | u(r, 2)<<30 | imm<<5 | reg(r)
	},
	"ls.excl": func(r *rand.Rand) uint32 {
		o2, l, o1 := u(r, 1), u(r, 1), u(r, 1)
		// Rs is a register operand of CAS/CASP and of the store-exclusives (status) and a
		// should-be-one field otherwise: mostly 31 there.
		rs := reg(r)
		if !(o1 == 1 || o2 == 0 && l == 0) {
			rs = mostly(r, 31, 5)
		}
		size := u(r, 2)
		if o2 == 0 && o1 == 1 && size < 2 && r.IntN(4) != 0 { // CASP: even registers
			rs &^= 1
			return 0x08000000 | size<<30 | l<<22 | 1<<21 | rs<<16 | u(r, 1)<<15 | mostly(r, 31, 5)<<10 | reg(r)<<5 | reg(r)&^1
		}
		return 0x08000000 | size<<30 | o2<<23 | l<<22 | o1<<21 | rs<<16 | mostly(r, 1, 1)<<15 | mostly(r, 31, 5)<<10 | reg(r)<<5 | reg(r)
	},
	"ls.atomic": func(r *rand.Rand) uint32 {
		o3opc := mostly(r, pick(r, 0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 8, 12), 4)
		ar := u(r, 2)
		rs := reg(r)
		if o3opc == 12 && r.IntN(4) != 0 { // LDAPR: A = 1, R = 0, Rs = 11111
			ar, rs = 2, 31
		}
		return 0x38200000 | u(r, 2)<<30 | ar<<22 | rs<<16 | o3opc<<12 | reg(r)<<5 | reg(r)
	},
	"sys.mrs": func(r *rand.Rand) uint32 {
		switch r.IntN(3) {
		case 0:
			return 0xD53B00E0 | reg(r) // MRS Xt, DCZID_EL0
		case 1:
			return 0xD53BD040 | reg(r) // MRS Xt, TPIDR_EL0
		}
		return 0xD5300000 | u(r, 20) // any system register read
	},
	// SIMD&FP loads and stores (V = 1).
	"vls.multi": func(r *rand.Rand) uint32 {
		op := mostly(r, pick(r, 0b0111, 0b1010, 0b0110, 0b0010), 4)
		w := 0x0C000000 | u(r, 1)<<30 | u(r, 1)<<22 | op<<12 | u(r, 2)<<10 | reg(r)<<5 | uint32(r.IntN(32))
		if r.IntN(2) == 0 {
			w |= 1<<23 | pick(r, 31, 31, reg(r))<<16
		}
		return w
	},
	"vls.single": func(r *rand.Rand) uint32 {
		w := 0x0D000000 | u(r, 1)<<30 | mostly(r, 1, 1)<<22 | u(r, 1)<<21 | u(r, 3)<<13 | u(r, 1)<<12 | u(r, 2)<<10 | reg(r)<<5 | uint32(r.IntN(32))
		if r.IntN(2) == 0 {
			w |= 1<<23 | pick(r, 31, 31, reg(r))<<16
		}
		return w
	},
	"simd.aes": func(r *rand.Rand) uint32 {
		if r.IntN(8) == 0 { // neighbours: other opcodes and sizes of the AES group
			return 0x4E280800 | u(r, 2)<<22 | u(r, 5)<<12 | vreg(r)<<5 | vreg(r)
		}
		return 0x4E284800 | u(r, 2)<<12 | vreg(r)<<5 | vreg(r)
	},
	"vls.uimm": func(r *rand.Rand) uint32 {
		imm := u(r, 12)
		if r.IntN(2) == 0 {
			imm = u(r, 6)
		}
		return 0x3D000000 | u(r, 2)<<30 | mostly(r, pick(r, 0, 1, 2, 3, 0, 1), 2)<<22 | imm<<10 | reg(r)<<5 | uint32(r.IntN(32))
	},
	"vls.imm9": func(r *rand.Rand) uint32 {
		return 0x3C000000 | u(r, 2)<<30 | u(r, 2)<<22 | u(r, 9)<<12 | u(r, 2)<<10 | reg(r)<<5 | uint32(r.IntN(32))
	},
	"vls.regoff": func(r *rand.Rand) uint32 {
		return 0x3C200800 | u(r, 2)<<30 | u(r, 2)<<22 | reg(r)<<16 | mostly(r, pick(r, 2, 3, 6, 7), 3)<<13 | u(r, 1)<<12 | reg(r)<<5 | uint32(r.IntN(32))
	},
	"vls.pair": func(r *rand.Rand) uint32 {
		return 0x2C000000 | mostly(r, pick(r, 0, 1, 2), 2)<<30 | mostly(r, pick(r, 1, 2, 3), 2)<<23 | u(r, 1)<<22 |
			smallOff(r, 7, 16)<<15 | uint32(r.IntN(32))<<10 | reg(r)<<5 | uint32(r.IntN(32))
	},
	"vls.literal": func(r *rand.Rand) uint32 {
		imm := uint32((L.DataBase+uint64(r.IntN(L.DataSize/4))*4-L.TestPC)/4) & 0x7ffff
		if r.IntN(10) == 0 {
			imm = u(r, 19)
		}
		return 0x1C000000 | mostly(r, pick(r, 0, 1, 2), 2)<<30 | imm<<5 | uint32(r.IntN(32))
	},
	// Advanced SIMD data processing (integer and move classes the model covers).
	"simd.3same": func(r *rand.Rand) uint32 {
		op := mostly(r, pick(r, 0b00011, 0b00011, 0b10000, 0b10001, 0b10001, 0b00110, 0b00111,
			0b01100, 0b01101, 0b10100, 0b10101, 0b10111, 0b10111), 5)
		return 0x0E200400 | u(r, 1)<<30 | u(r, 1)<<29 | u(r, 2)<<22 | vreg(r)<<16 | op<<11 | vreg(r)<<5 | vreg(r)
	},
	"simd.s3same": func(r *rand.Rand) uint32 {
		op := mostly(r, pick(r, 0b10000, 0b10001, 0b00110, 0b00111), 5)
		return 0x5E200400 | u(r, 1)<<29 | mostly(r, 3, 2)<<22 | vreg(r)<<16 | op<<11 | vreg(r)<<5 | vreg(r)
	},
	"simd.copy": func(r *rand.Rand) uint32 {
		op := uint32(0)
		if r.IntN(4) == 0 {
			op = 1
		}
		imm4 := mostly(r, pick(r, 0, 1, 3, 5, 7), 4)
		if op == 1 {
			imm4 = u(r, 4)
		}
		imm5 := u(r, 5)
		if imm5&0xf == 0 && r.IntN(4) != 0 {
			imm5 |= 1 << r.IntN(4)
		}
		rn := vreg(r)
		if op == 0 && (imm4 == 1 || imm4 == 3) {
			rn = reg(r)
		}
		rd := vreg(r)
		if op == 0 && (imm4 == 5 || imm4 == 7) {
			rd = reg(r)
		}
		return 0x0E000400 | u(r, 1)<<30 | op<<29 | imm5<<16 | imm4<<11 | rn<<5 | rd
	},
	"simd.across": func(r *rand.Rand) uint32 {
		op := mostly(r, pick(r, 0b00011, 0b01010, 0b11010, 0b11011), 5)
		return 0x0E300800 | u(r, 1)<<30 | u(r, 1)<<29 | u(r, 2)<<22 | op<<12 | vreg(r)<<5 | vreg(r)
	},
	"simd.2misc": func(r *rand.Rand) uint32 {
		op := mostly(r, pick(r, 0b00000, 0b00001, 0b00101, 0b01000, 0b01001, 0b01010, 0b01011, 0b10010), 5)
		return 0x0E200800 | u(r, 1)<<30 | u(r, 1)<<29 | u(r, 2)<<22 | op<<12 | vreg(r)<<5 | vreg(r)
	},
	"simd.shift": func(r *rand.Rand) uint32 {
		op := mostly(r, pick(r, 0b00000, 0b00010, 0b01010, 0b01000, 0b10000, 0b10100), 5)
		immh := u(r, 4)
		if immh == 0 {
			immh = 1 << r.IntN(4)
		}
		return 0x0F000400 | u(r, 1)<<30 | u(r, 1)<<29 | immh<<19 | u(r, 3)<<16 | op<<11 | vreg(r)<<5 | vreg(r)
	},
	"simd.modimm": func(r *rand.Rand) uint32 {
		return 0x0F000400 | u(r, 1)<<30 | u(r, 1)<<29 | u(r, 3)<<16 | u(r, 4)<<12 | mostly(r, 0, 1)<<11 | u(r, 5)<<5 | vreg(r)
	},
	"simd.ext": func(r *rand.Rand) uint32 {
		return 0x2E000000 | u(r, 1)<<30 | vreg(r)<<16 | u(r, 4)<<11 | vreg(r)<<5 | vreg(r)
	},
	"simd.tbl": func(r *rand.Rand) uint32 {
		return 0x0E000000 | u(r, 1)<<30 | vreg(r)<<16 | u(r, 2)<<13 | u(r, 1)<<12 | vreg(r)<<5 | vreg(r)
	},
	"simd.fmovgen": func(r *rand.Rand) uint32 {
		t := [][3]uint32{{0, 0, 0}, {1, 1, 0}, {1, 2, 1}}[r.IntN(3)]
		if r.IntN(8) == 0 {
			t = [3]uint32{u(r, 1), u(r, 2), u(r, 2)}
		}
		op := mostly(r, pick(r, 6, 7), 3)
		return 0x1E200000 | t[0]<<31 | t[1]<<22 | t[2]<<19 | op<<16 | reg(r)<<5 | reg(r)
	},
	"sys.sys": func(r *rand.Rand) uint32 {
		if r.IntN(2) == 0 {
			return 0xD50B7420 | reg(r) // DC ZVA, Xt
		}
		// SYS #op1, C7, Cm, #op2, Xt with op1 = 3 (EL0-accessible DC/IC ops) or 0
		return 0xD5087000 | pick(r, 3, 3, 3, 0)<<16 | u(r, 4)<<8 | u(r, 3)<<5 | reg(r)
	},
}

// Groups are fully random words inside one top-level encoding group (decoder strictness).
var Groups = map[string]func(r *rand.Rand) uint32{
	"dpi": func(r *rand.Rand) uint32 { return r.Uint32()&^0x1C000000 | 0x10000000 },
	"dpr": func(r *rand.Rand) uint32 { return r.Uint32()&^0x0E000000 | 0x0A000000 },
	"br":  func(r *rand.Rand) uint32 { return r.Uint32()&^0x1C000000 | 0x14000000 },
	"ls":  func(r *rand.Rand) uint32 { return r.Uint32()&^0x0E000000 | 0x08000000 },
	// SIMD&FP data processing (x111) and SIMD&FP loads and stores (x1x0 with V = 1).
	"simd": func(r *rand.Rand) uint32 { return r.Uint32()&^0x0E000000 | 0x0E000000 },
	"vls":  func(r *rand.Rand) uint32 { return r.Uint32()&^0x0E000000 | 0x0C000000 },
}
