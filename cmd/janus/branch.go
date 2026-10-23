package main

// Untrusted reachability decoding of AArch64 direct branches, using golang.org/x/arch.
//
// The extractor uses this only to decide which functions to copy. It never decides what an
// instruction means: Lean decodes every word again. If a branch is missed here, the target
// is simply absent from the extracted program and the Lean model faults with `noCode`.

import (
	"encoding/binary"

	"golang.org/x/arch/arm64/arm64asm"
)

// branchTarget returns the target of a PC-relative direct branch at pc, if w is one of
// B, BL, B.cond, CBZ, CBNZ, TBZ or TBNZ.
func branchTarget(w uint32, pc uint64) (uint64, bool) {
	var buf [4]byte
	binary.LittleEndian.PutUint32(buf[:], w)
	inst, err := arm64asm.Decode(buf[:])
	if err != nil {
		return 0, false
	}
	switch inst.Op {
	case arm64asm.B, arm64asm.BL, arm64asm.CBZ, arm64asm.CBNZ, arm64asm.TBZ, arm64asm.TBNZ:
	default:
		return 0, false
	}
	for _, a := range inst.Args {
		if rel, ok := a.(arm64asm.PCRel); ok {
			return uint64(int64(pc) + int64(rel)), true
		}
	}
	return 0, false
}

// isCall reports whether w is BL.
func isCall(w uint32) bool {
	var buf [4]byte
	binary.LittleEndian.PutUint32(buf[:], w)
	inst, err := arm64asm.Decode(buf[:])
	return err == nil && inst.Op == arm64asm.BL
}
