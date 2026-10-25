// Package layout is the contract shared by the native runner (cmd/runner, executing on the
// x86-64 host), the case generator, the comparator and the Lean side (Oracle/Amd64Main.lean,
// the `janus-oracle-amd64` executable). Every address here is concrete and fixed, so a test
// case is a closed, deterministic description of one x86-64 instruction execution.
//
// Address map (all canonical user-space addresses, below 2^47):
//
//	CtxPage    RW   host register save area, input state, captured output state
//	CodePage   RWX  the instruction bytes at TestPC; every other byte is 0xCC (INT3)
//	DataBase   RW   the memory buffer (DataSize bytes); the Lean model's only Region
//
// Everything else near these pages is unmapped. Falling through the instruction executes the
// INT3 right after it (SIGTRAP, saved RIP = TestPC + len + 1); a branch into the code page
// lands on an INT3 (SIGTRAP, saved RIP = target + 1); a branch anywhere else is an
// instruction-fetch SIGSEGV whose si_addr is the target; an instruction that itself faults
// raises SIGSEGV/SIGBUS/SIGILL/SIGFPE with saved RIP = TestPC.
//
// The Lean model fetches from the same code page: the case bytes followed by 0xCC up to the
// end of CodePage, so both sides see identical instruction bytes even when an encoding is
// longer than the bytes the case supplies.
package layout

const (
	CodePage = 0x10_0000_0000
	// TestPC sits in the middle of CodePage so short forward and backward branches land on
	// INT3 bytes of the same page.
	TestPC = CodePage + 0x800

	CtxPage = CodePage - 0x10_0000

	DataBase = CodePage + 0x4_0000
	DataSize = 4096

	PageSize = 4096
)

// RFLAGS status bits. Only these are set from a case and compared.
const (
	FlagCF = 1 << 0
	FlagPF = 1 << 2
	FlagAF = 1 << 4
	FlagZF = 1 << 6
	FlagSF = 1 << 7
	FlagOF = 1 << 11
	FlagDF = 1 << 10

	StatusFlags = FlagCF | FlagPF | FlagAF | FlagZF | FlagSF | FlagOF
)

// Pattern is the initial content of byte i of the data buffer for a given seed. The Lean
// side implements the same function (`pattern`). Identical to the arm64 oracle's.
func Pattern(seed uint64, i uint64) byte {
	return byte((i*157 + seed*89 + (i/256)*41 + 7) % 256)
}

// Case is one test: execute the instruction Bytes at TestPC from the given state.
//
// Register order is the hardware encoding order: RAX RCX RDX RBX RSP RBP RSI RDI R8..R15.
type Case struct {
	ID     int        `json:"id"`
	Class  string     `json:"class"`
	Bytes  string     `json:"bytes"`  // hex, 1..15 bytes, no separators ("4801d8")
	Regs   [16]string `json:"regs"`   // hex 64-bit
	RFlags int        `json:"rflags"` // status flags, plus FlagDF (the direction flag)
	XMM    [16]string `json:"xmm"`    // hex 128-bit
	// YMMH are bits 255:128 of YMM0-15 (hex 128-bit); absent = all zero.
	YMMH []string `json:"ymmh,omitempty"`
	// FSBase is the FS segment base (hex, canonical, below 2^47); absent = 0.
	FSBase string `json:"fsbase,omitempty"`
	Seed   uint64 `json:"seed"`
	// Init overrides buffer bytes after the pattern is applied: (offset, value) pairs, in
	// order. Used to plant return addresses / popped values. Absent = pattern only.
	Init [][2]int `json:"init,omitempty"`
	// MXCSR is the SSE control/status register for the case (hex, bits 15:0 only: flags
	// IE DE ZE OE UE PE 5:0, DAZ 6, masks 12:7, RC 14:13, FTZ 15); absent = DefaultMXCSR.
	// The runner loads it with LDMXCSR right before entering TestPC; the Lean side uses it as
	// `State.mxcsr`.
	MXCSR string `json:"mxcsr,omitempty"`
	// Seq (audit/rt-model): a straight-line sequence of instructions (hex each) laid out
	// one after another at TestPC; Bytes is ignored when Seq is set. The runner single-steps
	// through all of them; the model threads its own state through them.
	Seq []string `json:"seq,omitempty"`
}

// DefaultMXCSR is the MXCSR value Linux gives a new process (all exceptions masked, round to
// nearest, no FTZ/DAZ, no flags), which Go code runs with.
const DefaultMXCSR = 0x1F80

// MXCSRMask is the set of MXCSR bits a case may set (LDMXCSR with any other bit is #GP).
const MXCSRMask = 0xFFFF

// HW is what the native runner observed.
type HW struct {
	ID     int      `json:"id"`
	Status string   `json:"status"` // ok | fault | selfloop | escaped | error
	Sig    int      `json:"sig,omitempty"`
	Code   int      `json:"code,omitempty"`
	Addr   string   `json:"addr,omitempty"`
	PC     string   `json:"pc,omitempty"` // for ok: the address control went to
	Regs   []string `json:"regs,omitempty"`
	RFlags int      `json:"rflags"` // status bits only
	// DF is RFLAGS.DF after the instruction (compared with the model's direction flag).
	DF  bool     `json:"df,omitempty"`
	XMM []string `json:"xmm,omitempty"`
	// YMMH are bits 255:128 of YMM0-15 from the signal frame's XSAVE area (zero when the
	// frame says the AVX state is in its initial configuration); absent if the frame has no
	// XSAVE area.
	YMMH []string `json:"ymmh,omitempty"`
	Mem  [][2]int `json:"mem,omitempty"` // (offset, new byte) for every changed byte
	Note string   `json:"note,omitempty"`
	// Iters is the number of times the runner re-entered a REP string instruction (one
	// single-step trap per iteration with RIP still at TestPC, see IsRepString): the
	// iteration count minus one; 0 for every other instruction.
	Iters int `json:"iters,omitempty"`
	// MXCSR after the instruction (from the signal frame's fxsave area), hex.
	MXCSR string `json:"mxcsr,omitempty"`
}

// Model is what `janus-oracle-amd64` (Janus.Amd64.step) produced.
type Model struct {
	ID     int      `json:"id"`
	Status string   `json:"status"` // ok | fault
	Fault  string   `json:"fault,omitempty"`
	Detail any      `json:"detail,omitempty"`
	Len    int      `json:"len,omitempty"` // decoded instruction length
	PC     string   `json:"pc,omitempty"`
	Regs   []string `json:"regs,omitempty"`
	RFlags int      `json:"rflags"`
	// Defined is the mask of status flags the model defines after the instruction; the
	// others are architecturally undefined (reading them faults in the model) and are not
	// compared.
	Defined int      `json:"defined"`
	DF      bool     `json:"df,omitempty"` // the direction flag after the instruction
	XMM     []string `json:"xmm,omitempty"`
	YMMH    []string `json:"ymmh,omitempty"`
	Mem     [][2]int `json:"mem,omitempty"`
	MXCSR   string   `json:"mxcsr,omitempty"` // State.mxcsr after the instruction (hex)
}

// Ctx offsets (bytes) inside CtxPage. Must match cmd/runner/trampoline_amd64.s.
const (
	CtxInflight = 0
	CtxSig      = 8
	CtxAddr     = 16   // si_addr
	CtxCode     = 24   // si_code
	CtxHost     = 32   // rbx, rbp, r12, r13, r14, r15, rsp (7 words)
	CtxInRegs   = 104  // rax..r15 in encoding order (16 words); the RSP slot is unused (see CtxFrame)
	CtxInXMM    = 232  // xmm0..xmm15, 16 bytes each, little-endian
	CtxOutGRegs = 512  // copy of uc_mcontext.gregs[23] (Linux order: r8..r15 rdi rsi rbp rbx rdx rax rcx rsp rip eflags ...)
	CtxOutXMM   = 704  // xmm0..xmm15 from the signal frame's fxsave area
	CtxOutHasFP = 960  // 1 if the signal frame had an fpstate
	CtxFrame    = 1024 // IRETQ frame: rip, cs, rflags, rsp, ss
	CtxInYMMH   = 1536 // bits 255:128 of ymm0..ymm15 (16 bytes each), loaded with VINSERTI128
	CtxOutYMMH  = 1792 // bits 255:128 of ymm0..ymm15 from the signal frame's XSAVE area
	CtxOutXBV   = 2048 // XSTATE_BV of the signal frame (bit 2: AVX state not initial); ^0 = no XSAVE area
	CtxHostFS   = 2056 // the runner's own FS base (RDFSBASE), restored on resume
	CtxInFS     = 2064 // the case's FS base (WRFSBASE before entry)
	CtxInMXCSR  = 2072 // the case's MXCSR (LDMXCSR right before IRETQ), 32 bits
	CtxOutMXCSR = 2080 // MXCSR from the signal frame's fxsave area (offset 24), 32 bits
)

// XsaveYMMHOffset is the offset of the YMM_Hi128 component in the standard (non-compacted)
// XSAVE layout that Linux uses for signal frames (CPUID.(EAX=0DH,ECX=2).EBX; checked by the
// runner at start-up).
const XsaveYMMHOffset = 576

// Single-step entry: the runner enters the instruction with IRETQ and RFLAGS.TF = 1, so the
// CPU raises a debug trap (SIGTRAP, si_code TRAP_TRACE) after exactly one instruction, with
// the saved RIP = the address of the next instruction: TestPC + len on fall-through, the
// target on a taken branch (even an unmapped one: the trap precedes the next fetch).
const (
	TrapTrace = 2    // si_code of a single-step SIGTRAP
	SIKernel  = 0x80 // si_code of an INT3 SIGTRAP
)

// prefixLen is the number of legacy and REX prefix bytes at the start of b.
func prefixLen(b []byte) int {
	i := 0
	for i < len(b) {
		switch x := b[i]; {
		case x == 0x66 || x == 0x67 || x == 0xF2 || x == 0xF3 || x == 0xF0 ||
			x == 0x2E || x == 0x3E || x == 0x26 || x == 0x36 || x == 0x64 || x == 0x65 ||
			x >= 0x40 && x <= 0x4F:
			i++
			continue
		}
		break
	}
	return i
}

// IsRepString reports whether b is a string instruction (MOVS, CMPS, STOS, LODS, SCAS, INS,
// OUTS) with an F2/F3 repeat prefix. Single-stepping traps after every iteration of such an
// instruction with RIP still at the instruction, so the runner re-enters it until RIP moves.
func IsRepString(b []byte) bool {
	i := prefixLen(b)
	if i >= len(b) {
		return false
	}
	rep := false
	for _, x := range b[:i] {
		if x == 0xF2 || x == 0xF3 {
			rep = true
		}
	}
	switch b[i] {
	case 0xA4, 0xA5, 0xA6, 0xA7, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE, 0xAF, 0x6C, 0x6D, 0x6E, 0x6F:
		return rep
	}
	return false
}

// Forbidden reports whether the instruction encoded by b is one the native runner refuses to
// execute: INT n, MOV to a segment register, POPF, IRET, and the 0F-map SYSCALL, SYSENTER,
// SYSRET, SYSEXIT, POP FS/GS, LSS/LFS/LGS, group 15 (FXRSTOR/LDMXCSR/XRSTOR/WRFSBASE; the
// unprefixed fences LFENCE/MFENCE/SFENCE are allowed),
// and the system groups 0F 00 / 0F 01, plus any instruction with a GS segment prefix. FS is
// allowed: the runner points the FS base at the case's FSBase (WRFSBASE) for the duration of
// the case, so FS-relative accesses hit the case's own memory, never the runtime's TLS. VEX
// (C4/C5) and EVEX (62) instructions are user-mode vector instructions and are allowed.
// Only the opcode after the legacy and REX prefixes
// matters: the runner single-steps exactly one instruction, so later bytes are operands.
func Forbidden(b []byte) bool {
	i := 0
	for i < len(b) {
		switch x := b[i]; {
		case x == 0x66 || x == 0x67 || x == 0xF2 || x == 0xF3 || x == 0xF0 ||
			x == 0x2E || x == 0x3E || x == 0x26 || x == 0x36 || x == 0x64 || x == 0x65 ||
			x >= 0x40 && x <= 0x4F:
			i++
			continue
		}
		break
	}
	for _, x := range b[:i] {
		if x == 0x65 {
			return true
		}
	}
	if i >= len(b) {
		return false
	}
	switch b[i] {
	case 0x9D:
		// POPFQ (WP-C) only unprefixed: the runner enters with TF set and the signal frame's
		// flags are sanitised on return, so a popped TF/AC/NT/ID cannot escape the case; a
		// prefixed POPF (16-bit, REX) stays refused
		return i != 0
	case 0xCD, 0x8E, 0xCF:
		return true
	case 0x0F:
		if i+1 >= len(b) {
			return false
		}
		// LFENCE, MFENCE, SFENCE without any prefix are harmless (group 15 with mod = 11);
		// every other group-15 form stays refused
		if i == 0 && b[1] == 0xAE && len(b) >= 3 && (b[2] == 0xE8 || b[2] == 0xF0 || b[2] == 0xF8) {
			return false
		}
		switch b[i+1] {
		case 0x05, 0x34, 0x07, 0x35, 0xA1, 0xA9, 0xB2, 0xB4, 0xB5, 0xAE, 0x01, 0x00:
			return true
		}
	}
	return false
}
