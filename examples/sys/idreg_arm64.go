package sys

// ISAR0 returns ID_AA64ISAR0_EL1 (instruction set attributes 0), as the kernel reports it to
// EL0. Assembly, ABI0.
func ISAR0() uint64

// ISAR1 returns ID_AA64ISAR1_EL1.
func ISAR1() uint64

// PFR0 returns ID_AA64PFR0_EL1 (processor feature register 0).
func PFR0() uint64

// ZFR0 returns ID_AA64ZFR0_EL1 (SVE feature register 0).
func ZFR0() uint64

// MMFR0 returns ID_AA64MMFR0_EL1 (memory model feature register 0).
func MMFR0() uint64

// AESField is the AES field (bits 7:4) of ID_AA64ISAR0_EL1: 0 no AES, 1 AES, 2 AES and PMULL.
// golang.org/x/sys/cpu sets ARM64.HasAES and HasPMULL from it.
//
//go:noinline
func AESField() uint64 { return ISAR0() >> 4 & 0xf }

// SVEField is the SVE field (bits 35:32) of ID_AA64PFR0_EL1 (x/sys/cpu: ARM64.HasSVE).
//
//go:noinline
func SVEField() uint64 { return PFR0() >> 32 & 0xf }
