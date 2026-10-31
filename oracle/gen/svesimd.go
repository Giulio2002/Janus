package gen

import "math/rand/v2"

// The SVE / SME / Advanced SIMD&FP / SIMD load-store slice of the corpus (`oracle svegen`, scripts/oracle.sh).
// The targeted classes and the random groups of gen.go cover the base ISA and the NEON classes the Janus model
// executes; the corpus has almost no words of the top-level groups below, so it says nothing about the
// decoders of those groups (e.g. the Sail model's __DecodeA64_SVE). Each generator draws a uniformly random
// word of one top-level encoding group (Arm ARM C4.1: the fixed bits of op0 = bits 28:25, and bit 31 for SME);
// words are "valid-ish": most are allocated encodings, some are unallocated (both sides must agree on those too).
// No verdict is claimed beyond the existing ones: a word the Janus model does not decode is a model-gap.

// SVESIMDGroups maps the corpus class suffix to the generator of one top-level group, in a fixed order.
var SVESIMDGroups = []struct {
	Name string
	Gen  func(r *rand.Rand) uint32
}{
	// SVE: op0 (28:25) = 0010, bits 31:29 and 24:0 free (data processing, predicate ops, contiguous/gather loads and stores)
	{"sve", func(r *rand.Rand) uint32 { return r.Uint32()&^0x1E000000 | 0x04000000 }},
	// SME: bit 31 = 1, op0 = 0000
	{"sme", func(r *rand.Rand) uint32 { return r.Uint32()&^0x1E000000 | 0x80000000 }},
	// Advanced SIMD and scalar FP data processing: op0 (28:25) in {0111, 1111}
	{"simdfp", func(r *rand.Rand) uint32 {
		return r.Uint32()&^0x1E000000 | [2]uint32{0x0E000000, 0x1E000000}[r.IntN(2)]
	}},
	// Advanced SIMD load/store (structures, pairs, registers, literal): op0 (28:25) in {x110} (V = 1, bit 25 = 0)
	{"simdls", func(r *rand.Rand) uint32 {
		return r.Uint32()&^0x1E000000 | [2]uint32{0x0C000000, 0x1C000000}[r.IntN(2)]
	}},
}

// SVESIMDWord returns the next word of group i (for the callers' unpredictability / testing filters).
func SVESIMDWord(r *rand.Rand, i int) uint32 { return SVESIMDGroups[i].Gen(r) }
