package gen

// Advanced SIMD (NEON) classes beyond the original SIMD subset: classification, targeted
// encodings over every field combination of each class (allocated and unallocated
// neighbours alike), and states that exercise lane-wise edge cases: IEEE edge values in every
// lane of the floating-point forms, saturation boundaries and small shift counts for the
// integer forms. The class only groups results and picks states; it never decides what an
// instruction does.

import "math/rand/v2"

// neonClasses are the extra class names, in report order (appended to Classes).
var neonClasses = []string{
	"simd.3diff", "simd.s3diff", "simd.s2misc", "simd.spair", "simd.sshift",
	"simd.elem", "simd.selem",
}

func init() {
	// insert the new SIMD classes after "simd.fmovgen"
	var out []string
	for _, c := range Classes {
		out = append(out, c)
		if c == "simd.fmovgen" {
			out = append(out, neonClasses...)
		}
	}
	Classes = out
}

// classifyNeon returns the class of a word of the x111 group in one of the NEON classes the
// original classifier does not name, or "" (the permute and scalar DUP classes are
// classifyCrypto's simd.permute / simd.dupscalar).
func classifyNeon(w uint32) string {
	switch {
	case w&0x9F200C00 == 0x0E200000:
		return "simd.3diff"
	case w&0xDF200C00 == 0x5E200000:
		return "simd.s3diff"
	case w&0xDF3E0C00 == 0x5E200800:
		return "simd.s2misc"
	case w&0xDF3E0C00 == 0x5E300800:
		return "simd.spair"
	case w&0xDF800400 == 0x5F000400:
		return "simd.sshift"
	case w&0x9F000400 == 0x0F000000:
		return "simd.elem"
	case w&0xDF000400 == 0x5F000000:
		return "simd.selem"
	}
	return ""
}

// neonFP reports whether w is an Advanced SIMD floating-point form (its operands are
// floating-point lanes, or integers converted to floating point), and returns the lane
// format of its source operands and whether those are integers (SCVTF/UCVTF).
func neonFP(w uint32) (is bool, t fmtF, intSrc bool) {
	sz := bits(w, 22, 22)
	t = f32
	if sz == 1 {
		t = f64
	}
	cls := Classify(w)
	switch cls {
	case "simd.3same", "simd.s3same":
		return bits(w, 15, 14) == 3, t, false
	case "simd.2misc", "simd.s2misc":
		op := bits(w, 16, 12)
		switch {
		case op == 0b10110: // FCVTN/FCVTXN: double sources
			return true, f64, false
		case op == 0b10111: // FCVTL: single sources
			return true, f32, false
		case op == 0b11101 && bits(w, 23, 23) == 0: // SCVTF/UCVTF
			return true, t, true
		case op == 0b11100 && bits(w, 23, 23) == 1: // URECPE/URSQRTE (integer lanes)
			return false, t, false
		case op >= 0b01100 && op <= 0b01111, op >= 0b11000:
			return true, t, false
		}
	case "simd.across", "simd.spair":
		op := bits(w, 16, 12)
		return op == 0b01100 || op == 0b01101 || op == 0b01111, t, false
	case "simd.elem", "simd.selem":
		op := bits(w, 15, 12)
		return op == 0b0001 || op == 0b0101 || op == 0b1001, t, false
	case "simd.shift", "simd.sshift":
		op := bits(w, 15, 11)
		immh := bits(w, 22, 19)
		t = f32
		if immh >= 8 {
			t = f64
		}
		if op == 0b11100 {
			return true, t, true
		}
		return op == 0b11111, t, false
	}
	return false, t, false
}

// setupNeonFP fills the vector registers with IEEE edge values in every lane of format t (or
// integer edge values for the integer-to-float conversions), with crafted operand relations
// between the lanes of Rn, Rm and Rd, and random FPCR/FPSR.
func setupNeonFP(r *rand.Rand, w uint32, s *State, t fmtF, intSrc bool) {
	lanes := 2
	ebits := uint(64)
	if t == f32 {
		lanes, ebits = 4, 32
	}
	lane := func() uint64 {
		if intSrc {
			v := intEdge(r)
			if ebits == 32 {
				if r.IntN(2) == 0 {
					v = uint64(uint32(v))
				} else {
					v = uint64(uint32(v >> 32))
				}
			}
			return v
		}
		return t.edge(r)
	}
	set := func(reg uint32, k int, v uint64) {
		h, sh := k*int(ebits)/64, uint(k*int(ebits))%64
		mask := uint64(1)<<ebits - 1
		if ebits == 64 {
			mask = ^uint64(0)
		}
		s.V[reg][h] = s.V[reg][h]&^(mask<<sh) | (v&mask)<<sh
	}
	for i := range s.V {
		for k := 0; k < lanes; k++ {
			set(uint32(i), k, lane())
		}
	}
	rn, rm, rd := bits(w, 9, 5), bits(w, 20, 16), bits(w, 4, 0)
	if Classify(w) == "simd.elem" || Classify(w) == "simd.selem" {
		rm = bits(w, 19, 16) | bits(w, 20, 20)<<4
	}
	if !intSrc && r.IntN(10) < 6 {
		for k := 0; k < lanes; k++ {
			a, b, c := t.craft(r)
			if r.IntN(2) == 0 {
				a, b = b, a
			}
			set(rn, k, a)
			set(rm, k, b)
			set(rd, k, c)
		}
	}
	if r.IntN(4) == 0 { // the upper half zero: 64-bit operands
		s.V[rn][1] = 0
	}
	s.FPCR, s.FPSR = RandFPCR(r), RandFPSR(r)
	if r.IntN(4) == 0 {
		s.FPCR = 0
	}
}

// satLane draws a lane value of esize bits near a saturation or shift boundary.
func satLane(r *rand.Rand, esize uint) uint64 {
	m := uint64(1)<<esize - 1
	if esize == 64 {
		m = ^uint64(0)
	}
	hi := uint64(1) << (esize - 1)
	switch r.IntN(8) {
	case 0:
		return hi - uint64(r.IntN(3)) // INT_MAX .. INT_MAX-2
	case 1:
		return hi + uint64(r.IntN(3)) // INT_MIN ..
	case 2:
		return m - uint64(r.IntN(3)) // UINT_MAX, -1 ..
	case 3:
		return uint64(r.IntN(3))
	case 4:
		return (hi >> uint(r.IntN(int(esize)))) & m
	case 5:
		return uint64(int64(r.IntN(2*int(esize)+9)-int(esize)-4)) & m // small signed: shift counts
	}
	return r.Uint64() & m
}

// setupNeonInt biases the integer operands: lanes at the saturation boundaries in Rn/Rm/Rd,
// and small signed shift counts in Rm for the register shifts (SSHL ... UQRSHL).
func setupNeonInt(r *rand.Rand, w uint32, s *State) {
	esize := uint(8) << bits(w, 23, 22)
	if Classify(w) == "simd.shift" || Classify(w) == "simd.sshift" {
		immh := bits(w, 22, 19)
		esize = 8
		for immh > 1 {
			immh >>= 1
			esize <<= 1
		}
		esize = 2 * esize // the narrowing forms read double-width lanes
		if esize > 64 {
			esize = 64
		}
	}
	lanes := int(128 / esize)
	set := func(reg uint32, k int, v uint64) {
		h, sh := k*int(esize)/64, uint(k*int(esize))%64
		mask := uint64(1)<<esize - 1
		if esize == 64 {
			mask = ^uint64(0)
		}
		s.V[reg][h] = s.V[reg][h]&^(mask<<sh) | (v&mask)<<sh
	}
	rn, rm, rd := bits(w, 9, 5), bits(w, 20, 16), bits(w, 4, 0)
	if r.IntN(3) == 0 {
		for _, reg := range []uint32{rn, rm, rd} {
			for k := 0; k < lanes; k++ {
				if r.IntN(2) == 0 {
					set(reg, k, satLane(r, esize))
				}
			}
		}
	}
	if Classify(w) == "simd.3same" || Classify(w) == "simd.s3same" {
		if op := bits(w, 15, 11); op>>2 == 0b010 && r.IntN(4) != 0 {
			for k := 0; k < lanes; k++ {
				set(rm, k, uint64(int64(r.IntN(2*int(esize)+9)-int(esize)-4)))
			}
		}
	}
	if r.IntN(5) == 0 {
		s.FPSR = RandFPSR(r)
	}
}

// setupNeon is called by Setup for the SIMD data-processing classes.
func setupNeon(r *rand.Rand, w uint32, s *State) {
	if is, t, intSrc := neonFP(w); is {
		setupNeonFP(r, w, s, t, intSrc)
		return
	}
	switch Classify(w) {
	case "simd.3same", "simd.s3same", "simd.3diff", "simd.s3diff", "simd.2misc", "simd.s2misc",
		"simd.across", "simd.spair", "simd.permute", "simd.shift", "simd.sshift", "simd.elem",
		"simd.selem":
		setupNeonInt(r, w, s)
	}
}

func init() {
	// Every opcode of each class, with random size/Q/U (allocated and unallocated alike).
	Targeted["neon.3same"] = func(r *rand.Rand) uint32 {
		return 0x0E200400 | u(r, 1)<<30 | u(r, 1)<<29 | u(r, 2)<<22 | vreg(r)<<16 | u(r, 5)<<11 | vreg(r)<<5 | vreg(r)
	}
	Targeted["neon.3samefp"] = func(r *rand.Rand) uint32 {
		return 0x0E20C400 | u(r, 1)<<30 | u(r, 1)<<29 | u(r, 2)<<22 | vreg(r)<<16 | u(r, 3)<<11 | vreg(r)<<5 | vreg(r)
	}
	Targeted["neon.s3same"] = func(r *rand.Rand) uint32 {
		return 0x5E200400 | u(r, 1)<<29 | u(r, 2)<<22 | vreg(r)<<16 | u(r, 5)<<11 | vreg(r)<<5 | vreg(r)
	}
	Targeted["neon.3diff"] = func(r *rand.Rand) uint32 {
		return 0x0E200000 | u(r, 1)<<30 | u(r, 1)<<29 | u(r, 2)<<22 | vreg(r)<<16 | u(r, 4)<<12 | vreg(r)<<5 | vreg(r)
	}
	Targeted["neon.s3diff"] = func(r *rand.Rand) uint32 {
		return 0x5E200000 | u(r, 1)<<29 | u(r, 2)<<22 | vreg(r)<<16 | mostly(r, pick(r, 9, 11, 13), 4)<<12 | vreg(r)<<5 | vreg(r)
	}
	Targeted["neon.2misc"] = func(r *rand.Rand) uint32 {
		return 0x0E200800 | u(r, 1)<<30 | u(r, 1)<<29 | u(r, 2)<<22 | u(r, 5)<<12 | vreg(r)<<5 | vreg(r)
	}
	Targeted["neon.s2misc"] = func(r *rand.Rand) uint32 {
		return 0x5E200800 | u(r, 1)<<29 | u(r, 2)<<22 | u(r, 5)<<12 | vreg(r)<<5 | vreg(r)
	}
	Targeted["neon.across"] = func(r *rand.Rand) uint32 {
		op := mostly(r, pick(r, 0b00011, 0b01010, 0b11010, 0b11011, 0b01100, 0b01111, 0b01100, 0b01111), 5)
		return 0x0E300800 | u(r, 1)<<30 | u(r, 1)<<29 | u(r, 2)<<22 | op<<12 | vreg(r)<<5 | vreg(r)
	}
	Targeted["neon.spair"] = func(r *rand.Rand) uint32 {
		op := mostly(r, pick(r, 0b11011, 0b01101, 0b01100, 0b01111), 5)
		return 0x5E300800 | u(r, 1)<<29 | u(r, 2)<<22 | op<<12 | vreg(r)<<5 | vreg(r)
	}
	Targeted["neon.shift"] = func(r *rand.Rand) uint32 {
		immh := u(r, 4)
		if immh == 0 {
			immh = 1 << r.IntN(4)
		}
		return 0x0F000400 | u(r, 1)<<30 | u(r, 1)<<29 | immh<<19 | u(r, 3)<<16 | u(r, 5)<<11 | vreg(r)<<5 | vreg(r)
	}
	Targeted["neon.sshift"] = func(r *rand.Rand) uint32 {
		immh := u(r, 4)
		if immh == 0 && r.IntN(8) != 0 {
			immh = 1 << r.IntN(4)
		}
		return 0x5F000400 | u(r, 1)<<29 | immh<<19 | u(r, 3)<<16 | u(r, 5)<<11 | vreg(r)<<5 | vreg(r)
	}
	Targeted["neon.elem"] = func(r *rand.Rand) uint32 {
		return 0x0F000000 | u(r, 1)<<30 | u(r, 1)<<29 | u(r, 2)<<22 | u(r, 1)<<21 | u(r, 1)<<20 | u(r, 4)<<16 |
			u(r, 4)<<12 | u(r, 1)<<11 | vreg(r)<<5 | vreg(r)
	}
	Targeted["neon.selem"] = func(r *rand.Rand) uint32 {
		return 0x5F000000 | u(r, 1)<<29 | u(r, 2)<<22 | u(r, 1)<<21 | u(r, 1)<<20 | u(r, 4)<<16 |
			u(r, 4)<<12 | u(r, 1)<<11 | vreg(r)<<5 | vreg(r)
	}
	// LD2-LD4/ST2-ST4 (multiple structures), with and without post-index.
	Targeted["vls.struct"] = func(r *rand.Rand) uint32 {
		op := mostly(r, pick(r, 0b0000, 0b0100, 0b1000), 4)
		w := 0x0C000000 | u(r, 1)<<30 | u(r, 1)<<22 | op<<12 | u(r, 2)<<10 | reg(r)<<5 | uint32(r.IntN(32))
		if r.IntN(2) == 0 {
			w |= 1<<23 | pick(r, 31, 31, reg(r))<<16
		}
		return w
	}
	// LDNP/STNP (SIMD&FP).
	Targeted["vls.np"] = func(r *rand.Rand) uint32 {
		return 0x2C000000 | mostly(r, pick(r, 0, 1, 2), 2)<<30 | u(r, 1)<<22 |
			smallOff(r, 7, 16)<<15 | uint32(r.IntN(32))<<10 | reg(r)<<5 | uint32(r.IntN(32))
	}
}
