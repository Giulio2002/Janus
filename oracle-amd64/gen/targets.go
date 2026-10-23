package gen

import (
	"math/rand/v2"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
)

// Spec is a targeted encoding family: an opcode (with mandatory prefix bytes), followed by
// random ModRM/SIB/displacement/immediate bytes; optional operand-size prefix and REX are
// chosen at random. The bytes are truncated to the length x86asm decodes (when it can).
type Spec struct {
	Name   string
	Pre    []byte // mandatory prefix (66/F2/F3), placed before REX
	Op     []byte
	NoREXW bool
	Reg    int // ModRM.reg forced to this value (-1 = random)
	Mod3   int // 1 = force register form, 2 = force memory form, 0 = random
}

func specs() []Spec {
	var s []Spec
	add := func(name string, pre []byte, op []byte, reg, mod int) {
		s = append(s, Spec{Name: name, Pre: pre, Op: op, Reg: reg, Mod3: mod})
	}
	b := func(x ...byte) []byte { return x }
	// ALU 00-3F: op r/m,r ; r,r/m ; AL/eAX,imm
	alu := []string{"add", "or", "adc", "sbb", "and", "sub", "xor", "cmp"}
	for i, n := range alu {
		o := byte(i * 8)
		for k := byte(0); k < 6; k++ {
			add("alu/"+n, nil, b(o+k), -1, 0)
		}
		for g := 0; g < 3; g++ {
			add("grp1/"+n, nil, b([]byte{0x80, 0x81, 0x83}[g]), i, 0)
		}
	}
	for _, o := range []byte{0x84, 0x85, 0xA8, 0xA9} {
		add("test", nil, b(o), -1, 0)
	}
	for r := 0; r < 8; r++ {
		add("grp3", nil, b(0xF6), r, 0)
		add("grp3", nil, b(0xF7), r, 0)
	}
	for _, o := range []byte{0x88, 0x89, 0x8A, 0x8B} {
		add("mov", nil, b(o), -1, 0)
	}
	add("lea", nil, b(0x8D), -1, 2)
	add("mov", nil, b(0xC6), 0, 0)
	add("mov", nil, b(0xC7), 0, 0)
	for o := byte(0xB0); o <= 0xBF; o++ {
		add("movimm", nil, b(o), -1, 0)
	}
	for _, o := range []byte{0xB6, 0xB7, 0xBE, 0xBF} {
		add("movx", nil, b(0x0F, o), -1, 0)
	}
	add("movsxd", nil, b(0x63), -1, 0)
	for r := 0; r < 2; r++ {
		add("incdec", nil, b(0xFE), r, 0)
		add("incdec", nil, b(0xFF), r, 0)
	}
	for _, r := range []int{2, 4, 6} {
		add("ffind", nil, b(0xFF), r, 0)
	}
	for r := 0; r < 8; r++ {
		for _, o := range []byte{0xC0, 0xC1, 0xD0, 0xD1, 0xD2, 0xD3} {
			add("shift", nil, b(o), r, 0)
		}
	}
	for _, o := range []byte{0xA4, 0xA5, 0xAC, 0xAD} {
		add("shxd", nil, b(0x0F, o), -1, 0)
	}
	for _, o := range []byte{0xA3, 0xAB, 0xB3, 0xBB} {
		add("bt", nil, b(0x0F, o), -1, 0)
	}
	for r := 4; r < 8; r++ {
		add("bt", nil, b(0x0F, 0xBA), r, 0)
	}
	add("bsf", nil, b(0x0F, 0xBC), -1, 0)
	add("bsr", nil, b(0x0F, 0xBD), -1, 0)
	add("tzcnt", b(0xF3), b(0x0F, 0xBC), -1, 0)
	add("lzcnt", b(0xF3), b(0x0F, 0xBD), -1, 0)
	add("popcnt", b(0xF3), b(0x0F, 0xB8), -1, 0)
	for o := byte(0xC8); o <= 0xCF; o++ {
		add("bswap", nil, b(0x0F, o), -1, 0)
	}
	for o := byte(0x90); o <= 0x9F; o++ {
		add("setcc", nil, b(0x0F, o), -1, 0)
	}
	for o := byte(0x40); o <= 0x4F; o++ {
		add("cmovcc", nil, b(0x0F, o), -1, 0)
	}
	for o := byte(0x70); o <= 0x7F; o++ {
		add("jcc", nil, b(o), -1, 0)
	}
	for o := byte(0x80); o <= 0x8F; o++ {
		add("jcc", nil, b(0x0F, o), -1, 0)
	}
	for _, o := range []byte{0xEB, 0xE9, 0xE8, 0xC3, 0xC2, 0xC9, 0x6A, 0x68, 0x98, 0x99, 0xF8, 0xF9, 0xF5, 0x90} {
		add("misc", nil, b(o), -1, 0)
	}
	for o := byte(0x50); o <= 0x5F; o++ {
		add("pushpop", nil, b(o), -1, 0)
	}
	add("pushpop", nil, b(0x8F), 0, 0)
	add("nop", nil, b(0x0F, 0x1F), 0, 0)
	add("nop", b(0x66), b(0x90), -1, 0)
	for _, o := range []byte{0x86, 0x87, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97} {
		add("xchg", nil, b(o), -1, 0)
	}
	// SSE moves and zeroing
	for _, o := range []byte{0x10, 0x11, 0x28, 0x29} {
		add("sse/mov", nil, b(0x0F, o), -1, 0)
		add("sse/mov", b(0x66), b(0x0F, o), -1, 0)
	}
	for _, o := range []byte{0x6F, 0x7F} {
		add("sse/mov", b(0xF3), b(0x0F, o), -1, 0)
		add("sse/mov", b(0x66), b(0x0F, o), -1, 0)
	}
	add("sse/xor", nil, b(0x0F, 0x57), -1, 0)
	add("sse/xor", b(0x66), b(0x0F, 0x57), -1, 0)
	add("sse/xor", b(0x66), b(0x0F, 0xEF), -1, 0)
	add("sse/movq", b(0x66), b(0x0F, 0x6E), -1, 0)
	add("sse/movq", b(0x66), b(0x0F, 0x7E), -1, 0)
	add("sse/movq", b(0xF3), b(0x0F, 0x7E), -1, 0)
	add("sse/movq", b(0x66), b(0x0F, 0xD6), -1, 0)
	add("ud", nil, b(0x0F, 0x0B), -1, 0)
	add("ud", nil, b(0xCC), -1, 0)
	return s
}

// Specs is the targeted encoding table.
var Specs = specs()

// Targeted produces one encoding of spec sp.
func Targeted(r *rand.Rand, sp Spec) []byte {
	var out []byte
	// optional legacy prefixes: operand size, segment/branch hints, rarely others
	switch r.IntN(10) {
	case 0:
		out = append(out, 0x66)
	case 1:
		out = append(out, []byte{0x2E, 0x3E, 0x26, 0x36, 0x67, 0xF0, 0xF2, 0xF3}[r.IntN(8)])
	}
	out = append(out, sp.Pre...)
	if r.IntN(3) != 0 {
		rex := byte(0x40 | r.IntN(16))
		if r.IntN(2) == 0 {
			rex |= 8
		}
		out = append(out, rex)
	}
	out = append(out, sp.Op...)
	modrm := byte(r.IntN(256))
	if sp.Reg >= 0 {
		modrm = modrm&^0x38 | byte(sp.Reg)<<3
	}
	switch sp.Mod3 {
	case 1:
		modrm |= 0xC0
	case 2:
		if modrm>>6 == 3 {
			modrm &^= 0xC0
		}
	default:
		// bias towards register forms and short displacements
		if r.IntN(3) == 0 {
			modrm |= 0xC0
		}
	}
	tail := make([]byte, 14)
	for i := range tail {
		tail[i] = byte(r.IntN(256))
	}
	// small displacements/immediates are more interesting
	if r.IntN(2) == 0 {
		for i := 1; i < len(tail); i++ {
			if r.IntN(3) != 0 {
				tail[i] = []byte{0, 0, 0xff, 1, 8, 0x10, 0x80, 0x7f}[r.IntN(8)]
			}
		}
	}
	tail[0] = modrm
	out = append(out, tail...)
	return trim(out)
}

// trim cuts b to the instruction x86asm decodes, or to 15 bytes.
func trim(b []byte) []byte {
	if len(b) > 15 {
		b = b[:15]
	}
	if inst, ok := Decode(b); ok && inst.Len <= len(b) {
		return b[:inst.Len]
	}
	return b
}

var prefixPool = []byte{0x66, 0x67, 0xF2, 0xF3, 0xF0, 0x2E, 0x3E, 0x26, 0x36, 0x64, 0x65}

// GroupRandom is a random prefix/opcode/tail string, to exercise the decoder's rejection.
func GroupRandom(r *rand.Rand) []byte {
	var out []byte
	for n := r.IntN(4); n > 0; n-- {
		out = append(out, prefixPool[r.IntN(len(prefixPool))])
	}
	if r.IntN(2) == 0 {
		out = append(out, byte(0x40|r.IntN(16)))
	}
	switch r.IntN(4) {
	case 0:
		out = append(out, 0x0F, byte(r.IntN(256)))
	case 1:
		out = append(out, 0x0F, []byte{0x38, 0x3A}[r.IntN(2)], byte(r.IntN(256)))
	default:
		out = append(out, byte(r.IntN(256)))
	}
	for len(out) < 15 {
		out = append(out, byte(r.IntN(256)))
	}
	return trim(out)
}

// OK reports whether b may be run (not forbidden).
func OK(b []byte) bool { return len(b) > 0 && !L.Forbidden(b) }
