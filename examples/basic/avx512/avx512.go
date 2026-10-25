//go:build amd64

// Package avx512 holds the WP-G examples: Go functions whose work is done by small Go assembly
// functions using AVX-512 (EVEX, ZMM and opmask registers), built into
// artifacts/examples-amd64-avx512, a binary of its own so that the other examples' binaries do not
// change.
package avx512

// search64 returns the index of the first of the 8·nq bytes at p equal to c, or 64 if there is
// none (0 ≤ nq ≤ 8): the qword mask (1 << nq) - 1 in K1 (KMOVB) selects the qwords a masked,
// zeroing VMOVDQU64 loads, so only those 8·nq bytes are read (fault suppression); c is broadcast to
// the 64 bytes of Z1 (VPBROADCASTB r32); VPCMPEQB under the byte mask K3 (BZHI of all ones to
// 8·nq bits, KMOVQ) writes the equality mask to K2; KMOVQ, TZCNT.
//
//go:noescape
func search64(p *byte, nq int, c byte) int

// Search64 returns the index of the first of the 8·nq bytes at p equal to c (nq in [0, 8]), or
// 64 if there is none.
//
//go:noinline
func Search64(p *byte, nq int, c byte) int { return search64(p, nq, c) }
