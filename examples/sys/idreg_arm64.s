#include "textflag.h"

// The feature-ID register reads of golang.org/x/sys/cpu (cpu_arm64.s) and internal/cpu: Linux
// traps `MRS Xt, ID_AA64*_EL1` at EL0 and emulates it (HWCAP_CPUID) with a sanitised value.

// func ISAR0() uint64
TEXT ·ISAR0(SB), NOSPLIT, $0-8
	MRS	ID_AA64ISAR0_EL1, R0
	MOVD	R0, ret+0(FP)
	RET

// func ISAR1() uint64
TEXT ·ISAR1(SB), NOSPLIT, $0-8
	WORD	$0xd5380620	// MRS ID_AA64ISAR1_EL1, R0
	MOVD	R0, ret+0(FP)
	RET

// func PFR0() uint64
TEXT ·PFR0(SB), NOSPLIT, $0-8
	MRS	ID_AA64PFR0_EL1, R0
	MOVD	R0, ret+0(FP)
	RET

// func ZFR0() uint64
TEXT ·ZFR0(SB), NOSPLIT, $0-8
	WORD	$0xd5380480	// MRS ID_AA64ZFR0_EL1, R0
	MOVD	R0, ret+0(FP)
	RET

// func MMFR0() uint64
TEXT ·MMFR0(SB), NOSPLIT, $0-8
	WORD	$0xd5380700	// MRS ID_AA64MMFR0_EL1, R0
	MOVD	R0, ret+0(FP)
	RET
