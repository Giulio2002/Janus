// Package layout is the contract shared by the native runner (qemu-aarch64), the case
// generator, the comparator and the Lean side (Oracle/Main.lean). Every address here is
// concrete and fixed, so a test case is a closed, deterministic description of one
// AArch64 instruction execution.
//
// Address map (all inside the guest address space of qemu-aarch64 user mode):
//
//	EntryPage  RWX  trampoline: entry sequence, signal handler, resume sequence
//	CtxPage    RW   host register save area, input state, captured output state
//	CodePage   RWX  the instruction under test at TestPC; every other word is 0 (UDF)
//	DataBase   RW   the memory buffer (DataSize bytes); the Lean model's only Region
//
// Everything else near these pages is unmapped, so a branch anywhere else is observed as
// an instruction-fetch SIGSEGV whose PC is the branch target, and a load/store outside the
// buffer (that misses the code page) is observed as a data SIGSEGV at TestPC.
package layout

const (
	CodePage = 0x10_0000_0000
	// TestPC sits in the middle of CodePage so short forward and backward branches land
	// on UDF words of the same page (observed as SIGILL at the target).
	TestPC = CodePage + 0x800

	// EntryPage is 127 MiB below the test instruction (still in range of `B`, which the
	// entry sequence uses to reach TestPC), far from where test branches usually land.
	EntryPage = CodePage - 0x7F0_0000
	CtxPage   = EntryPage + 0x1000

	DataBase = CodePage + 0x4_0000
	DataSize = 4096

	PageSize = 4096
)

// Ctx offsets (bytes). Must match the trampoline in cmd/runner.
const (
	CtxInflight = 0
	CtxSig      = 8
	CtxAddr     = 16
	CtxCode     = 24
	CtxHost     = 32  // x19..x30 (12 words)
	CtxHostSP   = 128 // host SP
	CtxInNZCV   = 136 // NZCV in bits 31..28 (MSR NZCV format)
	CtxInSP     = 144
	CtxInX      = 152 // x0..x30
	CtxOut      = 400 // copy of uc_mcontext: regs[31], sp, pc, pstate
)

// Pattern is the initial content of byte i of the data buffer for a given seed. The Lean
// side implements the same function (Oracle/Main.lean: `pattern`).
func Pattern(seed uint64, i uint64) byte {
	return byte((i*157 + seed*89 + (i/256)*41 + 7) % 256)
}

// Case is one test: execute Word at TestPC from the given state.
type Case struct {
	ID    int        `json:"id"`
	Class string     `json:"class"`
	Word  string     `json:"word"` // hex, 32-bit
	PC    string     `json:"pc"`   // always TestPC (the runner rejects anything else)
	X     [31]string `json:"x"`    // hex, x0..x30
	SP    string     `json:"sp"`
	NZCV  int        `json:"nzcv"` // N=8 Z=4 C=2 V=1
	Seed  uint64     `json:"seed"`
	// DCZID is the reference machine's DCZID_EL0 (bits 4:0: DZP, BS), an IMPLEMENTATION
	// DEFINED constant that MRS DCZID_EL0 and DC ZVA depend on. The Lean side uses it as
	// `State.dczid`; the native runner refuses a case whose value differs from its CPU's.
	DCZID int `json:"dczid"`
}

// HW is what the native runner observed.
type HW struct {
	ID     int      `json:"id"`
	Status string   `json:"status"` // ok | fault | selfloop | escaped | error
	Sig    int      `json:"sig,omitempty"`
	Code   int      `json:"code,omitempty"`
	Addr   string   `json:"addr,omitempty"`
	PC     string   `json:"pc,omitempty"`
	X      []string `json:"x,omitempty"`
	SP     string   `json:"sp,omitempty"`
	NZCV   int      `json:"nzcv"`
	Mem    [][2]int `json:"mem,omitempty"` // (offset, new byte) for every changed byte
	Note   string   `json:"note,omitempty"`
}

// Model is what `janus-oracle` (Janus.Arm64.step) produced.
type Model struct {
	ID     int      `json:"id"`
	Status string   `json:"status"` // ok | fault
	Fault  string   `json:"fault,omitempty"`
	Detail any      `json:"detail,omitempty"` // fault fields (address, size, pc, ...)
	PC     string   `json:"pc,omitempty"`
	X      []string `json:"x,omitempty"`
	SP     string   `json:"sp,omitempty"`
	NZCV   int      `json:"nzcv"`
	Mem    [][2]int `json:"mem,omitempty"`
}
