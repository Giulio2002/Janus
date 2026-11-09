package gen

import (
	"fmt"
	"math/rand/v2"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
	"golang.org/x/arch/x86/x86asm"
)

// x87 (WP-J): targeted encodings of the escape opcodes D8-DF and FWAIT, random x87 states
// (register stack, TOP, tags, control word with every precision/rounding/mask setting, status
// word with sticky and pending flags) and double-extended edge values (zeros, denormals,
// pseudo-denormals, unnormals, pseudo-infinities/NaNs, infinities, quiet and signalling NaNs,
// rounding-boundary significands, values at the overflow and underflow thresholds), with
// memory operands planted in the buffer in the instruction's format. Plus the C-specific
// encodings of the same package: NOTRACK (3E) indirect branches and the padded TLS call.

// F80 is a double-extended encoding: the 64-bit significand and the sign/exponent word.
type F80 struct {
	Sig uint64
	SE  uint16
}

func (x F80) String() string {
	if x.SE == 0 {
		return fmt.Sprintf("%#x", x.Sig)
	}
	return fmt.Sprintf("0x%x%016x", x.SE, x.Sig)
}

func mk80(s int, e uint16, sig uint64) F80 { return F80{sig, uint16(s)<<15 | e&0x7FFF} }

// roundingSig returns a significand whose bits below the precision-p rounding position are a
// tie, just above or just below it (for p = 24, 53, 64 the last kept bit is random).
func roundingSig(r *rand.Rand, p int) uint64 {
	sig := r.Uint64() | 1<<63
	if p >= 64 {
		return sig
	}
	k := uint(64 - p) // bits below the rounding position
	sig &^= 1<<k - 1
	half := uint64(1) << (k - 1)
	switch r.IntN(4) {
	case 0:
		sig |= half // exact tie
	case 1:
		sig |= half + 1
	case 2:
		sig |= half - 1
	default:
		sig |= r.Uint64() & (1<<k - 1)
	}
	return sig
}

// Edge80 returns a double-extended edge value.
func Edge80(r *rand.Rand) F80 {
	s := r.IntN(2)
	switch r.IntN(26) {
	case 0:
		return mk80(s, 0, 0)
	case 1:
		v := r.Uint64() &^ (1 << 63)
		if r.IntN(2) == 0 {
			v >>= uint(r.IntN(63))
		}
		return mk80(s, 0, max(v, 1)) // denormal
	case 2:
		return mk80(s, 0, r.Uint64()|1<<63) // pseudo-denormal
	case 3, 4:
		return mk80(s, uint16(1+r.IntN(0x7FFE)), r.Uint64()|1<<63)
	case 5, 6:
		return mk80(s, uint16(0x3FF0+r.IntN(32)), r.Uint64()|1<<63)
	case 7:
		return mk80(s, uint16(1+r.IntN(70)), r.Uint64()|1<<63) // near the underflow threshold
	case 8:
		return mk80(s, uint16(0x7FFE-r.IntN(70)), r.Uint64()|1<<63) // near overflow
	case 9:
		return mk80(s, 0x7FFF, 1<<63) // infinity
	case 10:
		return mk80(s, 0x7FFF, 3<<62|r.Uint64()>>uint(2+r.IntN(62))) // QNaN
	case 11:
		return mk80(s, 0x7FFF, 1<<63|max(r.Uint64()>>uint(2+r.IntN(62)), 1)) // SNaN
	case 12:
		return mk80(s, uint16(1+r.IntN(0x7FFE)), r.Uint64()&^(1<<63)) // unnormal
	case 13:
		return mk80(s, 0x7FFF, r.Uint64()&^(1<<63)) // pseudo-infinity / pseudo-NaN
	case 14:
		// a small integer
		n := uint64(1 + r.IntN(1<<20))
		hb := 63
		for n>>hb == 0 {
			hb--
		}
		return mk80(s, uint16(16383+hb), n<<(63-hb))
	case 15, 16:
		return mk80(s, uint16(0x3FF0+r.IntN(32)), roundingSig(r, []int{24, 53, 64, 64}[r.IntN(4)]))
	case 17:
		// a binary64 / binary32 value
		sig := r.Uint64() | 1<<63
		if r.IntN(2) == 0 {
			sig &^= 1<<11 - 1
		} else {
			sig &^= 1<<40 - 1
		}
		return mk80(s, uint16(0x3F00+r.IntN(0x200)), sig)
	case 18:
		return mk80(s, 0x7FFE, ^uint64(0)) // max normal
	case 19:
		return mk80(s, 1, 1<<63) // min normal
	case 20:
		return mk80(s, uint16(16383+r.IntN(3)-1), 1<<63) // 0.5, 1, 2
	case 21:
		// a power of two near the binary64/binary32 subnormal ranges
		return mk80(s, uint16(16383-1022-r.IntN(60)), roundingSig(r, 53))
	case 22:
		return mk80(s, uint16(16383-126-r.IntN(30)), roundingSig(r, 24))
	case 23:
		// near the integer range limits (FIST)
		return mk80(s, uint16(16383+[]int{15, 16, 31, 32, 62, 63, 64}[r.IntN(7)]), roundingSig(r, 64)>>uint(r.IntN(2)) | 1<<63)
	case 24:
		// a half-integer (FIST rounding)
		n := uint64(r.IntN(1 << 10))
		v := n<<1 | 1 // n + 0.5 as (2n+1)/2
		hb := 63
		for v>>hb == 0 {
			hb--
		}
		return mk80(s, uint16(16383+hb-1), v<<(63-hb))
	default:
		return mk80(s, uint16(r.IntN(0x8000)), r.Uint64())
	}
}

// near returns a value close to x (same exponent, a few units apart), for cancellations.
func near(r *rand.Rand, x F80) F80 {
	d := uint64(r.IntN(9)) - 4
	return F80{x.Sig + d<<uint(r.IntN(41)), x.SE ^ uint16(r.IntN(2))<<15}
}

// RandX87 returns a random x87 state: TOP, the in-use registers (mostly ST(0)..ST(k-1)),
// the register values, the control word (masks, precision, rounding) and the status word.
func RandX87(r *rand.Rand) *L.X87State {
	top := r.IntN(8)
	var depth int
	switch r.IntN(12) {
	case 0:
		depth = 0
	case 1, 2:
		depth = 1
	case 3, 4, 5, 6:
		depth = 2
	case 7, 8:
		depth = 3
	case 9:
		depth = 8
	case 10:
		depth = 7
	default:
		depth = r.IntN(9)
	}
	ftw := 0
	for i := 0; i < depth; i++ {
		ftw |= 1 << ((top + i) & 7)
	}
	if r.IntN(10) == 0 {
		ftw = r.IntN(256)
	}
	var st [8]F80
	for i := range st {
		st[i] = Edge80(r)
	}
	if r.IntN(4) == 0 {
		st[1] = near(r, st[0])
	}
	if r.IntN(8) == 0 {
		st[1] = st[0] // equal operands
	}
	masks := 0x3F
	if r.IntN(8) == 0 {
		masks = r.IntN(64)
	}
	pc := []int{3, 3, 3, 2, 2, 0, 0, 1}[r.IntN(8)]
	if r.IntN(16) != 0 && pc == 1 {
		pc = 3
	}
	rc := r.IntN(4)
	if r.IntN(2) == 0 {
		rc = 0
	}
	cw := masks | 0x40 | pc<<8 | rc<<10 | r.IntN(2)<<12
	flags := r.IntN(128) & (masks | 0x40)
	if r.IntN(3) == 0 {
		flags = 0
	}
	fsw := flags | r.IntN(2)<<8 | r.IntN(2)<<9 | r.IntN(2)<<10 | r.IntN(2)<<14 | top<<11
	if r.IntN(40) == 0 && masks != 0x3F {
		// a pending unmasked exception: ES and B set
		fsw |= (0x3F &^ masks) & -(0x3F &^ masks) // the lowest unmasked flag
		fsw |= 0x80 | 0x8000
	}
	x := &L.X87State{FCW: fmt.Sprintf("%#x", cw), FSW: fmt.Sprintf("%#x", fsw), FTW: ftw}
	for i := range st {
		x.ST[i] = st[i].String()
	}
	return x
}

// x87Specs: every memory form (/0../7, random addressing) and every register form of D8-DF,
// FWAIT, and the prefixed variants.
type x87Spec struct {
	op  byte
	ext int  // memory forms: ModRM.reg; -1 = register form
	m   byte // register form: the ModRM byte
}

func x87SpecList() []x87Spec {
	var s []x87Spec
	for op := 0xD8; op <= 0xDF; op++ {
		for ext := 0; ext < 8; ext++ {
			s = append(s, x87Spec{op: byte(op), ext: ext})
		}
		for m := 0xC0; m <= 0xFF; m++ {
			s = append(s, x87Spec{op: byte(op), ext: -1, m: byte(m)})
		}
	}
	return s
}

func x87Bytes(r *rand.Rand, sp x87Spec) []byte {
	var out []byte
	switch k := r.IntN(40); {
	case k == 0:
		out = append(out, []byte{0x66, 0xF2, 0xF3, 0xF0, 0x67, 0x65}[r.IntN(6)])
	case k < 3:
		out = append(out, []byte{0x2E, 0x3E, 0x26, 0x36, 0x64}[r.IntN(5)])
	}
	if sp.ext >= 0 && r.IntN(4) == 0 {
		rex := byte(0x40 | r.IntN(8))
		if r.IntN(12) == 0 {
			rex |= 8
		}
		out = append(out, rex)
	} else if sp.ext < 0 && r.IntN(30) == 0 {
		out = append(out, byte(0x40|r.IntN(16)))
	}
	out = append(out, sp.op)
	if sp.ext < 0 {
		return append(out, sp.m)
	}
	md := r.IntN(3)
	rm := r.IntN(8)
	out = append(out, byte(md<<6|sp.ext<<3|rm))
	if rm == 4 {
		out = append(out, byte(r.IntN(256)))
	}
	switch {
	case md == 1:
		out = append(out, byte(r.IntN(256)))
	case md == 2 || (md == 0 && rm == 5):
		d := r.Uint32()
		if r.IntN(2) == 0 {
			d = uint32(int32(r.IntN(512) - 256))
		}
		out = append(out, byte(d), byte(d>>8), byte(d>>16), byte(d>>24))
	}
	if md == 0 && rm == 4 && out[len(out)-1]&7 == 5 {
		d := r.Uint32()
		out = append(out, byte(d), byte(d>>8), byte(d>>16), byte(d>>24))
	}
	return out
}

// ea is the effective address of m for state s (0, false if it cannot be computed).
func ea(s *State, inst x86asm.Inst, m x86asm.Mem) (uint64, bool) {
	if m.Base == x86asm.RIP {
		return L.TestPC + uint64(inst.Len) + uint64(m.Disp), true
	}
	var a uint64
	if n, _, ok := regNum(m.Base); ok {
		a += s.Regs[n]
	} else if m.Base != 0 {
		return 0, false
	}
	if n, _, ok := regNum(m.Index); ok {
		a += s.Regs[n] * uint64(m.Scale)
	} else if m.Index != 0 {
		return 0, false
	}
	a += uint64(m.Disp)
	for _, p := range inst.Prefix {
		if p&0xFF == x86asm.PrefixFS {
			a += s.FSBase
		}
	}
	return a, true
}

// plantX87Mem writes an edge value of the instruction's memory format at its operand.
func plantX87Mem(r *rand.Rand, s *State, b []byte) {
	inst, ok := Decode(b)
	if !ok {
		return
	}
	var mem *x86asm.Mem
	for _, a := range inst.Args {
		if m, ok := a.(x86asm.Mem); ok {
			mem = &m
		}
	}
	if mem == nil {
		return
	}
	a, ok := ea(s, inst, *mem)
	if !ok || a < L.DataBase || a+10 > L.DataBase+L.DataSize {
		return
	}
	i := prefixLen(b)
	if i+1 >= len(b) {
		return
	}
	op, ext := b[i], int(b[i+1]>>3&7)
	var bytes []byte
	put := func(v uint64, n int) {
		for k := 0; k < n; k++ {
			bytes = append(bytes, byte(v>>(8*k)))
		}
	}
	switch {
	case op == 0xD8 || (op == 0xD9 && ext == 0):
		put(FPEdge(r, 32), 4)
	case op == 0xDC || (op == 0xDD && ext == 0):
		put(FPEdge(r, 64), 8)
	case op == 0xDB && ext == 5:
		x := Edge80(r)
		put(x.Sig, 8)
		put(uint64(x.SE), 2)
	case op == 0xD9 && ext == 5:
		// FLDCW: a normalised control word, sometimes raw bits
		cw := uint64(0x37F)
		switch r.IntN(4) {
		case 0:
			cw = uint64(r.IntN(1 << 16))
		case 1, 2:
			cw = uint64(0x3F|0x40|[]int{0, 2, 3, 1}[r.IntN(4)]<<8|r.IntN(4)<<10) &^ uint64(r.IntN(2)*r.IntN(64))
		}
		put(cw, 2)
	case op == 0xDA || (op == 0xDB && ext == 0):
		put(intEdge(r), 4)
	case op == 0xDE || (op == 0xDF && ext == 0):
		put(intEdge(r), 2)
	case op == 0xDF && ext == 5:
		put(intEdge(r), 8)
	default:
		return
	}
	off := int(a - L.DataBase)
	for k, v := range bytes {
		s.Init = append(s.Init, [2]int{off + k, int(v)})
	}
}

func hexv64(x string) uint64 {
	var v uint64
	fmt.Sscanf(x, "0x%x", &v)
	return v
}

func intEdge(r *rand.Rand) uint64 {
	if r.IntN(3) == 0 {
		return uint64(int64(r.IntN(201) - 100))
	}
	return RandValue(r)
}

func prefixLen(b []byte) int {
	i := 0
	for i < len(b) {
		switch x := b[i]; {
		case x == 0x66 || x == 0x67 || x == 0xF2 || x == 0xF3 || x == 0xF0 || x == 0x2E || x == 0x3E ||
			x == 0x26 || x == 0x36 || x == 0x64 || x == 0x65 || x >= 0x40 && x <= 0x4F:
			i++
			continue
		}
		break
	}
	return i
}

// IsX87 reports whether b is an x87 instruction (D8-DF or FWAIT after its prefixes).
func IsX87(b []byte) bool {
	i := prefixLen(b)
	return i < len(b) && (b[i] >= 0xD8 && b[i] <= 0xDF || b[i] == 0x9B)
}

// SetupX87 is Setup plus a random x87 state and a planted memory operand.
func SetupX87(r *rand.Rand, b []byte) State {
	s := Setup(r, b)
	s.X87 = RandX87(r)
	// register forms: make ST(0)..ST(i) in use in most cases (and ST(7) free for pushes)
	if i := prefixLen(b); i+1 < len(b) && b[i] >= 0xD8 && b[i] <= 0xDF && r.IntN(8) != 0 {
		top := int(hexv64(s.X87.FSW)>>11) & 7
		k := 1
		if b[i+1] >= 0xC0 {
			k = int(b[i+1]&7) + 1
		}
		if k < 2 && r.IntN(2) == 0 {
			k = 2
		}
		for j := 0; j < k; j++ {
			s.X87.FTW |= 1 << ((top + j) & 7)
		}
		if r.IntN(3) != 0 {
			s.X87.FTW &^= 1 << ((top + 7) & 7)
			if k == 8 {
				s.X87.FTW |= 1 << ((top + 7) & 7)
			}
		}
	}
	plantX87Mem(r, &s, b)
	return s
}

// X87Cases returns n cases per x87 spec (register forms: n/4), the FWAIT and CET/TLS
// families, as (class, bytes, state).
func X87Cases(r *rand.Rand, n int) []EdgeCase {
	var out []EdgeCase
	for _, sp := range x87SpecList() {
		k := n
		if sp.ext < 0 {
			k = max(n/4, 1)
		}
		for i := 0; i < k; i++ {
			b := x87Bytes(r, sp)
			if !OK(b) {
				continue
			}
			out = append(out, EdgeCase{Class: "x87/" + Classify(b), Bytes: b, State: SetupX87(r, b)})
		}
	}
	for i := 0; i < n; i++ {
		b := []byte{0x9B}
		if r.IntN(4) == 0 {
			b = []byte{[]byte{0x66, 0x3E, 0x48}[r.IntN(3)], 0x9B}
		}
		out = append(out, EdgeCase{Class: "x87/fwait", Bytes: b, State: SetupX87(r, b)})
	}
	for i := 0; i < n; i++ {
		b := cetBytes(r)
		s := Setup(r, b)
		out = append(out, EdgeCase{Class: "cet/" + Classify(b), Bytes: b, State: s})
	}
	return out
}

// cetBytes: NOTRACK (3E) and other segment prefixes on FF /2, /4; the padded TLS call
// (66 66 48 E8) and its neighbours; the data16 LEA of the general-dynamic sequence.
func cetBytes(r *rand.Rand) []byte {
	rel := []byte{byte(r.IntN(256)), byte(r.IntN(3)) - 1, 0xFF, 0xFF}
	if r.IntN(2) == 0 {
		rel = []byte{byte(r.IntN(64)), 0, 0, 0}
	}
	switch r.IntN(6) {
	case 0, 1:
		var out []byte
		if r.IntN(6) == 0 {
			out = append(out, []byte{0x2E, 0x26, 0x36, 0x64, 0x66, 0xF2}[r.IntN(6)])
		}
		out = append(out, 0x3E)
		if r.IntN(3) == 0 {
			out = append(out, byte(0x40|r.IntN(16)))
		}
		md := r.IntN(4)
		ext := []int{2, 4}[r.IntN(2)]
		out = append(out, 0xFF, byte(md<<6|ext<<3|r.IntN(8)))
		for k := 0; k < 6; k++ {
			out = append(out, byte(r.IntN(256)))
		}
		return trim(out)
	case 2, 3:
		pre := [][]byte{{0x66, 0x66, 0x48}, {0x66, 0x66, 0x48}, {0x66, 0x48}, {0x66, 0x66}, {0x66, 0x66, 0x40}, {0x48}, {0x66, 0x66, 0x66, 0x48}}[r.IntN(7)]
		return append(append(pre, 0xE8), rel...)
	case 4:
		return append([]byte{0x66, 0x48, 0x8D, 0x3D}, rel...)
	default:
		return append([]byte{0x3E, 0xE8}, rel...)
	}
}
