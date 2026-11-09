package gen

import (
	"math/rand/v2"
	"strings"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
	"golang.org/x/arch/x86/x86asm"
)

// The x86 crypto extensions (WP-E): AES-NI, PCLMULQDQ, SHA-NI and ADX (legacy encodings),
// Janus/Amd64/{InstrCrypto,DecodeCrypto,ExecCrypto}.lean.

// CryptoClasses are the WP-E classes (x86asm mnemonics, lower case; "adcx"/"adox" are named by
// Classify, this x86asm version does not know them).
var CryptoClasses = strings.Fields(`aesenc aesenclast aesdec aesdeclast aesimc aeskeygenassist
	pclmulqdq sha1rnds4 sha1nexte sha1msg1 sha1msg2 sha256rnds2 sha256msg1 sha256msg2 adcx adox`)

func init() {
	for _, m := range CryptoClasses {
		Modeled[m] = true
	}
}

// CryptoRegexp matches every WP-E class (for `harvest -only`).
func CryptoRegexp() string { return "^(" + strings.Join(CryptoClasses, "|") + ")$" }

type adxForm struct {
	bytes []byte // the same instruction with 13 (ADC r, r/m) for 0F 38 F6 and no mandatory prefix
	extra int    // how many bytes longer the original is
	adox  bool
}

// adxOperandForm recognises ADCX (66 [REX] 0F 38 F6 /r) and ADOX (F3 [REX] 0F 38 F6 /r) with
// the prefix combinations the model accepts (66 alone, or the last of F2/F3 being F3 without
// 66), other legacy prefixes anywhere before REX.
func adxOperandForm(b []byte) (adxForm, bool) {
	var keep []byte
	has66, rep, removed := false, byte(0), 0
	i := 0
	for ; i < len(b); i++ {
		switch c := b[i]; c {
		case 0x66:
			has66 = true
			removed++
			continue
		case 0xF2, 0xF3:
			rep = c
			removed++
			continue
		case 0x26, 0x2E, 0x36, 0x3E, 0x64, 0x65, 0x67, 0xF0:
			keep = append(keep, c)
			continue
		}
		break
	}
	if i < len(b) && b[i]&0xF0 == 0x40 {
		keep = append(keep, b[i])
		i++
	}
	if i+3 > len(b) || b[i] != 0x0F || b[i+1] != 0x38 || b[i+2] != 0xF6 {
		return adxForm{}, false
	}
	var adox bool
	switch {
	case has66 && rep == 0:
	case !has66 && rep == 0xF3:
		adox = true
	default:
		return adxForm{}, false
	}
	out := append(append(keep, 0x13), b[i+3:]...)
	return adxForm{out, removed + 2, adox}, true
}

// adxClass is "adcx"/"adox" for an ADX instruction.
func adxClass(b []byte) (string, bool) {
	k, ok := adxOperandForm(b)
	if !ok {
		return "", false
	}
	if k.adox {
		return "adox", true
	}
	return "adcx", true
}

func cryptoSpecs() []Spec {
	var s []Spec
	add := func(name string, pre []byte, op []byte, mod int) {
		s = append(s, Spec{Name: name, Pre: pre, Op: op, Reg: -1, Mod3: mod})
	}
	b := func(x ...byte) []byte { return x }
	p66, pF3, pF2 := b(0x66), b(0xF3), b(0xF2)
	// AES-NI 66 0F 38 DB..DF and the neighbours without 66 / with F2/F3 / unallocated
	for _, o := range []byte{0xDB, 0xDC, 0xDD, 0xDE, 0xDF} {
		for _, mod := range []int{1, 1, 2, 2, 0} {
			add("crypto/aes", p66, b(0x0F, 0x38, o), mod)
		}
		add("crypto/aes-other", nil, b(0x0F, 0x38, o), 0)
		add("crypto/aes-other", pF3, b(0x0F, 0x38, o), 0)
		add("crypto/aes-other", pF2, b(0x0F, 0x38, o), 0)
		add("crypto/aes-other", b(0x66, 0xF3), b(0x0F, 0x38, o), 0)
	}
	add("crypto/aes-other", p66, b(0x0F, 0x38, 0xDA), 0)
	// AESKEYGENASSIST 66 0F 3A DF ib, PCLMULQDQ 66 0F 3A 44 ib
	for _, o := range []byte{0xDF, 0x44} {
		for _, mod := range []int{1, 1, 2, 2, 0} {
			add("crypto/3a", p66, b(0x0F, 0x3A, o), mod)
		}
		add("crypto/3a-other", nil, b(0x0F, 0x3A, o), 0)
		add("crypto/3a-other", pF3, b(0x0F, 0x3A, o), 0)
		add("crypto/3a-other", pF2, b(0x0F, 0x3A, o), 0)
	}
	add("crypto/3a-other", p66, b(0x0F, 0x3A, 0x45), 0)
	// SHA-NI NP 0F 38 C8..CD, NP 0F 3A CC ib, and their 66/F2/F3 neighbours
	for _, o := range []byte{0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD} {
		for _, mod := range []int{1, 1, 2, 2, 0} {
			add("crypto/sha", nil, b(0x0F, 0x38, o), mod)
		}
		add("crypto/sha-other", p66, b(0x0F, 0x38, o), 0)
		add("crypto/sha-other", pF3, b(0x0F, 0x38, o), 0)
		add("crypto/sha-other", pF2, b(0x0F, 0x38, o), 0)
	}
	for _, mod := range []int{1, 1, 2, 2, 0} {
		add("crypto/sha", nil, b(0x0F, 0x3A, 0xCC), mod)
	}
	add("crypto/sha-other", p66, b(0x0F, 0x3A, 0xCC), 0)
	add("crypto/sha-other", pF3, b(0x0F, 0x3A, 0xCC), 0)
	add("crypto/sha-other", nil, b(0x0F, 0x38, 0xCE), 0)
	add("crypto/sha-other", nil, b(0x0F, 0x38, 0xCF), 0)
	// ADX: 66 / F3 0F 38 F6 (and F2, 66+F3, none: rejected)
	for _, mod := range []int{1, 1, 1, 2, 2, 0} {
		add("crypto/adx", p66, b(0x0F, 0x38, 0xF6), mod)
		add("crypto/adx", pF3, b(0x0F, 0x38, 0xF6), mod)
	}
	add("crypto/adx-other", pF2, b(0x0F, 0x38, 0xF6), 0)
	add("crypto/adx-other", b(0x66, 0xF3), b(0x0F, 0x38, 0xF6), 0)
	add("crypto/adx-other", b(0xF3, 0x66), b(0x0F, 0x38, 0xF6), 0)
	add("crypto/adx-other", nil, b(0x0F, 0x38, 0xF6), 0)
	return s
}

// CryptoSpecs are the legacy-encoded WP-E targets (also part of Specs).
var CryptoSpecs = cryptoSpecs()

func init() { Specs = append(Specs, CryptoSpecs...) }

func isCrypto(cls string) bool {
	for _, c := range CryptoClasses {
		if c == cls {
			return true
		}
	}
	return false
}

// adxEdges are interesting addends: around the 32- and 64-bit carry boundaries.
var adxEdges = []uint64{0, 1, 2, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFE, 0xFFFFFFFF, 0x100000000,
	0x1FFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF,
	0xFFFFFFFF00000000}

// setupCrypto steers the WP-E classes: 16-byte memory operands mostly aligned (legacy SSE faults
// otherwise), state/key values with structure now and then (zero, all ones, equal operands), and
// for ADCX/ADOX addends around the carry boundaries in the register and memory operands.
func setupCrypto(r *rand.Rand, s *State, inst x86asm.Inst, cls string) {
	if !isCrypto(cls) {
		return
	}
	if cls == "adcx" || cls == "adox" {
		for _, a := range inst.Args {
			if a == nil {
				break
			}
			switch a := a.(type) {
			case x86asm.Reg:
				if n, _, ok := regNum(a); ok && n != 4 && r.IntN(2) == 0 {
					s.Regs[n] = adxEdges[r.IntN(len(adxEdges))]
				}
			case x86asm.Mem:
				if ea, ok := effAddr(s, inst, a); ok && r.IntN(2) == 0 {
					plantLE(s, ea, [2]uint64{adxEdges[r.IntN(len(adxEdges))], 0}, 8)
				}
			}
		}
		return
	}
	for i := range s.XMM {
		switch r.IntN(10) {
		case 0:
			s.XMM[i] = [2]uint64{}
		case 1:
			s.XMM[i] = [2]uint64{^uint64(0), ^uint64(0)}
		case 2:
			s.XMM[i] = laneXMM(r, 32)
		}
	}
	if len(inst.Args) > 1 {
		d, src := xmmArg(inst.Args[0]), xmmArg(inst.Args[1])
		if d >= 0 && src >= 0 && d != src && r.IntN(6) == 0 {
			s.XMM[src] = s.XMM[d]
		}
	}
	for _, a := range inst.Args {
		m, ok := a.(x86asm.Mem)
		if !ok {
			continue
		}
		if r.IntN(4) != 0 {
			if ea, ok := effAddr(s, inst, m); ok && ea >= L.DataBase && ea < L.DataBase+L.DataSize {
				if bn, _, bok := regNum(m.Base); bok && bn != 4 {
					s.Regs[bn] -= ea & 15
				}
			}
		}
		if ea, ok := effAddr(s, inst, m); ok && r.IntN(2) == 0 {
			plantLE(s, ea, [2]uint64{r.Uint64(), r.Uint64()}, 16)
		}
	}
}

// CryptoEdges are the systematic WP-E families, per round: AESKEYGENASSIST, PCLMULQDQ and
// SHA1RNDS4 with every imm8 (one per round, cycling, plus a random one); each AES round on
// zero/all-ones/random states; ADCX/ADOX at 32 and 64 bits, register and memory forms, under
// every combination of the six status flags with addends at the carry boundaries (the five
// flags the instruction must not touch are compared).
func CryptoEdges(r *rand.Rand, n int) []EdgeCase {
	var out []EdgeCase
	emit := func(class string, b []byte, s State) {
		if OK(b) {
			out = append(out, EdgeCase{"edge/" + class, b, s})
		}
	}
	p66 := []byte{0x66}
	for round := 0; round < n; round++ {
		for _, imm := range []byte{byte(round % 256), byte(r.IntN(256))} {
			for _, o := range []struct {
				pre []byte
				op  []byte
			}{{p66, []byte{0x0F, 0x3A, 0xDF}}, {p66, []byte{0x0F, 0x3A, 0x44}}, {nil, []byte{0x0F, 0x3A, 0xCC}}} {
				d, sr := r.IntN(16), r.IntN(16)
				b := legacyRR(o.pre, o.op, r.IntN(4) == 0, d, sr, imm)
				s := baseState(r)
				for i := range s.XMM {
					s.XMM[i] = [2]uint64{r.Uint64(), r.Uint64()}
				}
				emit("crypto-imm", b, s)
			}
		}
		for _, o := range []byte{0xDB, 0xDC, 0xDD, 0xDE, 0xDF} {
			d, sr := r.IntN(16), r.IntN(16)
			b := legacyRR(p66, []byte{0x0F, 0x38, o}, false, d, sr)
			s := baseState(r)
			for i := range s.XMM {
				s.XMM[i] = [][2]uint64{{}, {^uint64(0), ^uint64(0)}, {r.Uint64(), r.Uint64()}}[r.IntN(3)]
			}
			emit("aes", b, s)
		}
		for _, o := range []byte{0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD} {
			d, sr := r.IntN(16), r.IntN(16)
			b := legacyRR(nil, []byte{0x0F, 0x38, o}, false, d, sr)
			s := baseState(r)
			for i := range s.XMM {
				s.XMM[i] = laneXMM(r, 32)
			}
			emit("sha", b, s)
		}
		for _, pre := range [][]byte{{0x66}, {0xF3}} {
			for _, w := range []int{32, 64} {
				d, sr := r.IntN(16), r.IntN(16)
				if d == 4 {
					d = 0
				}
				if sr == 4 {
					sr = 3
				}
				var b []byte
				s := baseState(r)
				if r.IntN(3) == 0 {
					// memory form: [base] with base = R15/RBX..., the operand in the buffer
					base := []int{3, 6, 7, 13, 15}[r.IntN(5)]
					b = cat(pre, rexFor(w, d, 0, base, false), []byte{0x0F, 0x38, 0xF6, byte(d&7)<<3 | byte(base&7)})
					if base&7 == 5 {
						// [RBP/R13] needs a disp8
						b[len(b)-1] |= 0x40
						b = append(b, 0)
					}
					ea := L.DataBase + 64 + uint64(8*r.IntN(64))
					s.Regs[base] = ea
					plantLE(&s, ea, [2]uint64{adxEdges[r.IntN(len(adxEdges))], 0}, 8)
				} else {
					b = cat(pre, rexFor(w, d, 0, sr, false), []byte{0x0F, 0x38, 0xF6, modrmRR(d, sr)})
					s.Regs[sr] = adxEdges[r.IntN(len(adxEdges))]
				}
				s.Regs[d] = adxEdges[r.IntN(len(adxEdges))]
				s.RFlags = FlagCombo(r.IntN(64))
				emit("adx", b, s)
			}
		}
	}
	return out
}
