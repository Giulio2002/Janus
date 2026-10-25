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
	// atomics: LOCK-prefixed read-modify-write forms (memory destination forced, and random
	// ModRM to hit the #UD register forms), XADD, CMPXCHG, CMPXCHG8B/16B, and fences
	lk := b(0xF0)
	for i, n := range alu {
		o := byte(i * 8)
		add("lock/"+n, lk, b(o), -1, 2)
		add("lock/"+n, lk, b(o+1), -1, 2)
		add("lock/"+n, lk, b(o+1), -1, 0)
		add("lock/"+n, lk, b(0x83), i, 2)
		add("lock/"+n, lk, b(0x81), i, 0)
		add("lock/"+n, lk, b(0x80), i, 2)
	}
	for r := 0; r < 2; r++ {
		add("lock/incdec", lk, b(0xFF), r, 2)
		add("lock/incdec", lk, b(0xFE), r, 0)
	}
	for r := 2; r < 4; r++ {
		add("lock/notneg", lk, b(0xF7), r, 2)
		add("lock/notneg", lk, b(0xF6), r, 0)
	}
	for r := 4; r < 8; r++ {
		add("lock/bt", lk, b(0x0F, 0xBA), r, 2)
	}
	add("lock/bt", lk, b(0x0F, 0xAB), -1, 2)
	add("lock/xchg", lk, b(0x87), -1, 0)
	add("lock/xchg", lk, b(0x86), -1, 2)
	add("lock/mov", lk, b(0x89), -1, 2)
	add("lock/test", lk, b(0x85), -1, 2)
	for _, o := range []byte{0xC0, 0xC1, 0xB0, 0xB1} {
		add("atomic", lk, b(0x0F, o), -1, 2)
		add("atomic", lk, b(0x0F, o), -1, 2)
		add("atomic", nil, b(0x0F, o), -1, 0)
	}
	add("atomic", lk, b(0x0F, 0xC7), 1, 2)
	add("atomic", nil, b(0x0F, 0xC7), 1, 0)
	add("atomic", lk, b(0x0F, 0xC7), -1, 0)
	for r := 5; r < 8; r++ {
		add("fence", nil, b(0x0F, 0xAE), r, 1)
	}
	add("fence", b(0xF3), b(0x90), -1, 0)
	// CET hint space F3 0F 1E: ENDBR64 (/7, rm = 2) and ENDBR32 (rm = 3) among the /7 register
	// forms, RDSSP (/1) and the reserved NOPs; without and with other prefixes (only the exact
	// bytes F3 0F 1E FA are modelled)
	add("cet/endbr", b(0xF3), b(0x0F, 0x1E), 7, 1)
	add("cet/endbr", b(0xF3), b(0x0F, 0x1E), 7, 1)
	add("cet/endbr", b(0xF3), b(0x0F, 0x1E), -1, 0)
	add("cet/endbr", nil, b(0x0F, 0x1E), 7, 1)
	// string instructions, with and without REP (the state is steered to small counts)
	for _, o := range []byte{0xA4, 0xA5, 0xAA, 0xAB} {
		add("string", b(0xF3), b(o), -1, 0)
		add("string", b(0xF3), b(o), -1, 0)
		add("string", nil, b(o), -1, 0)
	}
	for _, o := range []byte{0xA6, 0xA7, 0xAC, 0xAD, 0xAE, 0xAF} {
		add("string", b(0xF3), b(o), -1, 0)
		add("string", b(0xF2), b(o), -1, 0)
	}
	// SSE packed-integer compares and logic, PMOVMSKB, PSHUFD (66: SSE; no prefix: MMX, rejected)
	for _, o := range []byte{0x74, 0xDB, 0xEB, 0x60, 0xD7, 0x70} {
		add("sse/int", b(0x66), b(0x0F, o), -1, 0)
		add("sse/int", b(0x66), b(0x0F, o), -1, 1)
		add("sse/int", nil, b(0x0F, o), -1, 0)
	}
	add("sse/int", b(0xF2), b(0x0F, 0x70), -1, 0) // PSHUFLW
	add("sse/int", b(0xF3), b(0x0F, 0x70), -1, 0) // PSHUFHW (not modelled)
	// RCL/RCR by 1, imm8 and CL, register and memory forms
	for r := 2; r < 4; r++ {
		for _, o := range []byte{0xC0, 0xC1, 0xD0, 0xD1, 0xD2, 0xD3} {
			add("rcx", nil, b(o), r, 0)
		}
	}
	// scalar moves MOVSS (F3) / MOVSD (F2)
	for _, p := range []byte{0xF2, 0xF3} {
		for _, o := range []byte{0x10, 0x11} {
			add("sse/movs", b(p), b(0x0F, o), -1, 0)
			add("sse/movs", b(p), b(0x0F, o), -1, 1)
		}
	}
	// PREFETCHh (/0../3) and the reserved hint NOPs (/4../7, rejected); CLD, STD (rejected)
	for r := 0; r < 8; r++ {
		add("prefetch", nil, b(0x0F, 0x18), r, 0)
	}
	add("misc", nil, b(0xFC), -1, 0)
	add("misc", nil, b(0xFD), -1, 0)
	// FS-relative forms (memory operand forced), and FS on forms where it is rejected
	for _, o := range [][]byte{{0x8B}, {0x89}, {0x88}, {0x8A}, {0xC7}, {0xC6}, {0x03}, {0x3B}, {0x39}, {0x85}, {0x81}, {0x83}, {0x0F, 0xB6}, {0x0F, 0xB7}, {0x0F, 0xBE}, {0x63}} {
		add("fs", b(0x64), o, -1, 2)
	}
	for _, o := range [][]byte{{0x8B}, {0x89}, {0x8D}, {0xFF}, {0x0F, 0x10}, {0xA5}, {0xAB}, {0x0F, 0xB1}} {
		add("fs", b(0x64), o, -1, 0)
	}
	add("ud", nil, b(0x0F, 0x0B), -1, 0)
	add("ud", nil, b(0xCC), -1, 0)
	// WP-C: traps, environment reads, the RFLAGS image (exact forms; Targeted adds random
	// prefixes and REX, which the decoder rejects)
	add("sys/trap", nil, b(0xF4), -1, 0)
	add("sys/trap", nil, b(0xCD, 0x03), -1, 0)
	add("sys/env", nil, b(0x0F, 0xA2), -1, 0)
	add("sys/env", nil, b(0x0F, 0x31), -1, 0)
	add("sys/flags", nil, b(0x9C), -1, 0)
	add("sys/flags", nil, b(0x9D), -1, 0)
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

// VexSpec is a targeted VEX encoding family: opcode map (1 = 0F, 2 = 0F38), implied prefix
// pp (0 none, 1 66, 2 F3, 3 F2) and opcode, followed by random ModRM/SIB/displacement bytes.
type VexSpec struct {
	Name    string
	Map, PP byte
	Op      byte
	Mod3    int // 1 = register form, 2 = memory form, 0 = random
}

func vexSpecs() []VexSpec {
	var s []VexSpec
	add := func(name string, mp, pp, op byte, mod int) {
		s = append(s, VexSpec{name, mp, pp, op, mod})
	}
	for _, mod := range []int{0, 1, 2} {
		add("vex/mov", 1, 2, 0x6F, mod) // VMOVDQU
		add("vex/mov", 1, 2, 0x7F, mod)
		add("vex/mov", 1, 1, 0x6F, mod) // VMOVDQA
		add("vex/mov", 1, 1, 0x7F, mod)
		add("vex/mov", 1, 1, 0xE7, mod)                     // VMOVNTDQ
		for _, op := range []byte{0xEF, 0xDB, 0xEB, 0x74} { // VPXOR VPAND VPOR VPCMPEQB
			add("vex/int", 1, 1, op, mod)
		}
		add("vex/int", 1, 1, 0xD7, mod) // VPMOVMSKB
		add("vex/int", 2, 1, 0x17, mod) // VPTEST
		add("vex/int", 2, 1, 0x78, mod) // VPBROADCASTB
	}
	add("vex/zero", 1, 0, 0x77, 0) // VZEROUPPER / VZEROALL
	add("vex/zero", 1, 0, 0x77, 0)
	// neighbours that must be rejected (or are not modelled)
	add("vex/other", 1, 0, 0x6F, 0) // no VEX MMX form: #UD
	add("vex/other", 1, 3, 0x6F, 0) // VMOVDQU with F2: #UD
	add("vex/other", 2, 1, 0x79, 0) // VPBROADCASTW
	add("vex/other", 1, 1, 0xDF, 0) // VPANDN
	add("vex/other", 1, 1, 0x75, 0) // VPCMPEQW
	add("vex/other", 3, 1, 0x0F, 0) // VPALIGNR
	add("vex/other", 2, 2, 0xF6, 0) // MULX
	return s
}

// VexSpecs is the targeted VEX table.
var VexSpecs = vexSpecs()

// VexTargeted produces one VEX encoding of sp: mostly the valid shape (unused VEX.vvvv =
// 1111, the right map and pp), sometimes a reserved field set, a stray prefix before the VEX
// prefix, or the other form (2-byte / 3-byte).
func VexTargeted(r *rand.Rand, sp VexSpec) []byte {
	var out []byte
	if r.IntN(12) == 0 {
		out = append(out, []byte{0x66, 0xF2, 0xF3, 0xF0, 0x40, 0x48, 0x2E, 0x64, 0x67}[r.IntN(9)])
	}
	rr, xx, bb := byte(r.IntN(2)), byte(r.IntN(2)), byte(r.IntN(2))
	w := byte(r.IntN(2))
	vvvv := byte(0)
	if r.IntN(4) == 0 {
		vvvv = byte(r.IntN(16))
	}
	l := byte(r.IntN(2))
	if sp.Op == 0x77 && r.IntN(3) != 0 {
		l = 0
	}
	mp, pp := sp.Map, sp.PP
	if r.IntN(20) == 0 {
		mp = byte(r.IntN(4))
	}
	if r.IntN(20) == 0 {
		pp = byte(r.IntN(4))
	}
	if mp == 1 && xx == 0 && bb == 0 && w == 0 && r.IntN(3) != 0 {
		out = append(out, 0xC5, (1-rr)<<7|(^vvvv&15)<<3|l<<2|pp)
	} else {
		out = append(out, 0xC4, (1-rr)<<7|(1-xx)<<6|(1-bb)<<5|mp, w<<7|(^vvvv&15)<<3|l<<2|pp)
	}
	out = append(out, sp.Op)
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
			tail[i] = []byte{0, 0, 0xff, 1, 0x20, 0x10, 0x80, 0xe0}[r.IntN(8)]
		}
	}
	tail[0] = modrm
	out = append(out, tail...)
	return trim(out)
}
