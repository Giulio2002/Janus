//go:build arm64

// Command runner executes single AArch64 instructions natively (under qemu-aarch64 user
// mode on an x86 host, or on real arm64 Linux) and reports the resulting architectural
// state. It reads layout.Case JSON lines on stdin and writes layout.HW JSON lines.
//
// Mechanism (no per-case subprocess, no landing pads):
//
//   - The instruction is written at layout.TestPC in a page whose every other word is 0,
//     which is the permanently undefined encoding UDF #0.
//   - A hand-assembled entry sequence (in layout.EntryPage) saves the host callee-saved
//     registers and SP, loads NZCV, SP and X0..X30 from the case and branches to TestPC.
//   - Whatever happens next raises a signal: falling through executes the UDF at TestPC+4
//     (SIGILL), a branch lands on a UDF in the code page (SIGILL) or on an unmapped or
//     non-executable page (SIGSEGV with si_addr == pc), a faulting instruction raises
//     SIGILL/SIGSEGV/SIGBUS/SIGTRAP with pc == TestPC, and a branch-to-self is interrupted
//     by a watchdog (SIGALRM).
//   - A raw signal handler (installed with rt_sigaction, bypassing the Go runtime, running
//     on the thread's sigaltstack) copies uc_mcontext (X0..X30, SP, PC, PSTATE) into the
//     context page and rewrites the saved PC to a resume sequence that restores the host
//     registers and returns to Go. The kernel's sigreturn does the rest.
//
// So the state captured is exactly the architectural state after the one instruction, and
// the PC tells us where it went.
package main

import (
	"bufio"
	"encoding/binary"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"runtime"
	"runtime/debug"
	"strconv"
	"strings"
	"sync/atomic"
	"syscall"
	"time"
	"unsafe"

	L "github.com/Giulio2002/Janus/oracle/layout"
)

func callPage(entry uintptr)

func readDCZID() uint64

// dczid is this CPU's DCZID_EL0; every case must carry the same value (layout.Case.DCZID).
var dczid = readDCZID() & 0x1f

const (
	sigILL  = 4
	sigTRAP = 5
	sigBUS  = 7
	sigFPE  = 8
	sigSEGV = 11
	sigALRM = 14

	mapFixedNoreplace = 0x100000

	ucRegs = 184 // offsetof(ucontext_t, uc_mcontext.regs) on arm64
	ucPC   = 440 // offsetof(ucontext_t, uc_mcontext.pc)
	// offsetof(ucontext_t, uc_mcontext.__reserved): the first record is fpsimd_context.
	ucReserved = 464
)

var (
	entryAddr, handlerAddr, restorerAddr uint64
	ctx, code, data                      []byte
)

func mmapFixed(addr uint64, size int, prot int) []byte {
	p, _, errno := syscall.Syscall6(syscall.SYS_MMAP, uintptr(addr), uintptr(size), uintptr(prot),
		uintptr(syscall.MAP_PRIVATE|syscall.MAP_ANONYMOUS|mapFixedNoreplace), ^uintptr(0), 0)
	if errno != 0 || uint64(p) != addr {
		fmt.Fprintf(os.Stderr, "runner: mmap %#x failed: %v (got %#x)\n", addr, errno, p)
		os.Exit(2)
	}
	return unsafe.Slice((*byte)(unsafe.Pointer(p)), size)
}

func buildTrampoline() []uint32 {
	a := &asm{base: L.EntryPage}
	// ---- entry (x0 is ignored; called with BLR from callPage) ----
	entryAddr = a.pc()
	a.adr(16, L.CtxPage)
	for r := 19; r <= 30; r++ {
		a.str(r, 16, L.CtxHost+8*(r-19))
	}
	a.addImm(17, 31, 0) // mov x17, sp
	a.str(17, 16, L.CtxHostSP)
	a.mrsTPIDR(17) // host TPIDR_EL0, restored by the resume sequence
	a.str(17, 16, L.CtxHostTPID)
	a.ldr(17, 16, L.CtxInTPIDR)
	a.msrTPIDR(17)
	// Host FPCR/FPSR (restored by the resume sequence), then the case's. FPCR is read back
	// so the runner can refuse a case whose control bits the CPU does not keep.
	a.mrsFPCR(17)
	a.str(17, 16, L.CtxHostFPCR)
	a.mrsFPSR(17)
	a.str(17, 16, L.CtxHostFPSR)
	a.ldr(17, 16, L.CtxInFPCR)
	a.msrFPCR(17)
	a.mrsFPCR(17)
	a.str(17, 16, L.CtxFPCRBack)
	a.ldr(17, 16, L.CtxInFPSR)
	a.msrFPSR(17)
	for r := 0; r < 32; r++ {
		a.ldrq(r, 16, L.CtxInV+16*r)
	}
	a.ldr(17, 16, L.CtxInNZCV)
	a.msrNZCV(17)
	a.ldr(17, 16, L.CtxInSP)
	a.addImm(31, 17, 0) // mov sp, x17
	for r := 0; r <= 30; r++ {
		if r != 16 {
			a.ldr(r, 16, L.CtxInX+8*r)
		}
	}
	a.ldr(16, 16, L.CtxInX+8*16)
	a.emit(0xD503305F) // clrex: every case starts with the exclusive monitor open
	a.b(L.TestPC)

	// ---- signal handler: x0 = signo, x1 = siginfo*, x2 = ucontext* ----
	for len(a.words)%16 != 0 {
		a.emit(0)
	}
	handlerAddr = a.pc()
	notours, loop, plainRet := &label{}, &label{}, &label{}
	resume := &label{}
	a.adr(3, L.CtxPage)
	a.ldr(5, 3, L.CtxInflight)
	a.cbz(5, notours)
	a.str(0, 3, L.CtxSig)
	a.ldr(5, 1, 16) // si_addr
	a.str(5, 3, L.CtxAddr)
	a.ldrw(5, 1, 8) // si_code
	a.str(5, 3, L.CtxCode)
	a.addImm(6, 2, ucRegs)
	a.addImm(7, 3, L.CtxOut)
	a.movz(8, 34) // regs[31], sp, pc, pstate
	a.bind(loop)
	a.ldrPost8(9, 6)
	a.strPost8(9, 7)
	a.subsImm(8, 8, 1)
	a.bcond(1 /* ne */, loop)
	// The fpsimd_context record (first in uc_mcontext.__reserved): magic, size, fpsr, fpcr,
	// vregs[32].
	loop2 := &label{}
	a.addImm(6, 2, ucReserved)
	a.addImm(7, 3, L.CtxOutFP)
	a.movz(8, 66)
	a.bind(loop2)
	a.ldrPost8(9, 6)
	a.strPost8(9, 7)
	a.subsImm(8, 8, 1)
	a.bcond(1 /* ne */, loop2)
	resumeAdrIdx := len(a.words)
	a.emit(0) // adr x9, resume (patched below)
	a.str(9, 2, ucPC)
	a.str(31, 3, L.CtxInflight) // str xzr
	a.ret()
	a.bind(notours)
	a.subsImm(31, 0, sigALRM) // cmp x0, #SIGALRM
	a.bcond(0 /* eq */, plainRet)
	a.movz(0, 97)
	a.movz(8, 94) // exit_group(97): a synchronous fault outside the test instruction
	a.svc0()
	a.bind(plainRet)
	a.ret()

	restorerAddr = a.pc()
	a.movz(8, 139) // rt_sigreturn
	a.svc0()

	a.bind(resume)
	a.adr(16, L.CtxPage)
	a.ldr(17, 16, L.CtxHostTPID)
	a.msrTPIDR(17)
	a.ldr(17, 16, L.CtxHostFPCR)
	a.msrFPCR(17)
	a.ldr(17, 16, L.CtxHostFPSR)
	a.msrFPSR(17)
	a.ldr(17, 16, L.CtxHostSP)
	a.addImm(31, 17, 0)
	for r := 19; r <= 30; r++ {
		a.ldr(r, 16, L.CtxHost+8*(r-19))
	}
	a.ret()
	w := a.finish()
	off := uint32(resume.addr - (L.EntryPage + uint64(resumeAdrIdx)*4))
	w[resumeAdrIdx] = 0x10000000 | (off&3)<<29 | ((off>>2)&0x7ffff)<<5 | 9
	return w
}

type sigactiont struct {
	handler  uint64
	flags    uint64
	restorer uint64
	mask     uint64
}

func installHandlers() {
	const saSiginfo, saOnstack, saRestorer = 0x4, 0x08000000, 0x04000000
	for _, s := range []int{sigILL, sigTRAP, sigBUS, sigFPE, sigSEGV, sigALRM} {
		act := sigactiont{handler: handlerAddr, flags: saSiginfo | saOnstack | saRestorer,
			restorer: restorerAddr, mask: ^uint64(0) &^ (1<<(sigILL-1) | 1<<(sigSEGV-1) | 1<<(sigBUS-1))}
		_, _, errno := syscall.RawSyscall6(syscall.SYS_RT_SIGACTION, uintptr(s),
			uintptr(unsafe.Pointer(&act)), 0, 8, 0, 0)
		if errno != 0 {
			fmt.Fprintf(os.Stderr, "runner: rt_sigaction(%d): %v\n", s, errno)
			os.Exit(2)
		}
	}
}

func put64(b []byte, off int, v uint64) { binary.LittleEndian.PutUint64(b[off:], v) }
func get64(b []byte, off int) uint64    { return binary.LittleEndian.Uint64(b[off:]) }

func parseHex(s string) (uint64, error) {
	if len(s) > 2 && s[0] == '0' && (s[1] == 'x' || s[1] == 'X') {
		return strconv.ParseUint(s[2:], 16, 64)
	}
	return strconv.ParseUint(s, 0, 64)
}

func hex(v uint64) string { return "0x" + strconv.FormatUint(v, 16) }

// hex128 renders hi:lo as one hex number without leading zeros.
func hex128(lo, hi uint64) string {
	if hi == 0 {
		return hex(lo)
	}
	return fmt.Sprintf("0x%x%016x", hi, lo)
}

// parseHex128 parses a hex number of up to 128 bits into (low, high) 64-bit halves.
func parseHex128(s string) (uint64, uint64, error) {
	t := strings.TrimPrefix(strings.TrimPrefix(s, "0x"), "0X")
	if t == "" || len(t) > 32 {
		return 0, 0, fmt.Errorf("bad 128-bit hex %q", s)
	}
	var hi uint64
	if len(t) > 16 {
		var err error
		if hi, err = strconv.ParseUint(t[:len(t)-16], 16, 64); err != nil {
			return 0, 0, err
		}
		t = t[len(t)-16:]
	}
	lo, err := strconv.ParseUint(t, 16, 64)
	return lo, hi, err
}

var (
	busy atomic.Int64 // case sequence number currently executing, 0 when idle
)

func watchdog(tid int, limit time.Duration) {
	pid := os.Getpid()
	var last int64
	var since time.Time
	for {
		time.Sleep(limit / 4)
		cur := busy.Load()
		if cur == 0 || cur != last {
			last, since = cur, time.Now()
			continue
		}
		if time.Since(since) >= limit {
			syscall.Tgkill(pid, tid, syscall.SIGALRM)
			since = time.Now()
		}
	}
}

func runCase(c *L.Case, seq int64) L.HW {
	r := L.HW{ID: c.ID}
	word, err := parseHex(c.Word)
	if err != nil || word > 0xffffffff {
		r.Status, r.Note = "error", "bad word"
		return r
	}
	if pc, err := parseHex(c.PC); c.PC != "" && (err != nil || pc != L.TestPC) {
		r.Status, r.Note = "error", "pc must be layout.TestPC"
		return r
	}
	if uint64(c.DCZID) != dczid {
		r.Status, r.Note = "error", fmt.Sprintf("case dczid %#x differs from this CPU's DCZID_EL0 %#x (regenerate with -dczid)", c.DCZID, dczid)
		return r
	}
	clear(code)
	binary.LittleEndian.PutUint32(code[L.TestPC-L.CodePage:], uint32(word))
	for i := range data {
		data[i] = L.Pattern(c.Seed, uint64(i))
	}
	for i := 0; i < 31; i++ {
		v, err := parseHex(c.X[i])
		if err != nil {
			r.Status, r.Note = "error", "bad x"
			return r
		}
		put64(ctx, L.CtxInX+8*i, v)
	}
	sp, err := parseHex(c.SP)
	if err != nil {
		r.Status, r.Note = "error", "bad sp"
		return r
	}
	put64(ctx, L.CtxInSP, sp)
	for i := 0; i < 32; i++ {
		lo, hi := uint64(0), uint64(0)
		if len(c.V) == 32 {
			var err error
			if lo, hi, err = parseHex128(c.V[i]); err != nil {
				r.Status, r.Note = "error", "bad v"
				return r
			}
		} else if len(c.V) != 0 {
			r.Status, r.Note = "error", "v must have 32 entries"
			return r
		}
		put64(ctx, L.CtxInV+16*i, lo)
		put64(ctx, L.CtxInV+16*i+8, hi)
	}
	tp := uint64(0)
	if c.TPIDR != "" {
		if tp, err = parseHex(c.TPIDR); err != nil {
			r.Status, r.Note = "error", "bad tpidr"
			return r
		}
	}
	put64(ctx, L.CtxInTPIDR, tp)
	var fpcr, fpsr uint64
	if c.FPCR != "" {
		if fpcr, err = parseHex(c.FPCR); err != nil || fpcr > 0xffffffff {
			r.Status, r.Note = "error", "bad fpcr"
			return r
		}
	}
	if c.FPSR != "" {
		if fpsr, err = parseHex(c.FPSR); err != nil || fpsr > 0xffffffff {
			r.Status, r.Note = "error", "bad fpsr"
			return r
		}
	}
	put64(ctx, L.CtxInFPCR, fpcr)
	put64(ctx, L.CtxInFPSR, fpsr)
	put64(ctx, L.CtxFPCRBack, ^uint64(0))
	for i := L.CtxOutFP; i < L.CtxOutFP+528; i++ {
		ctx[i] = 0
	}
	put64(ctx, L.CtxInNZCV, uint64(c.NZCV&15)<<28)
	put64(ctx, L.CtxSig, 0)
	put64(ctx, L.CtxInflight, 1)
	busy.Store(seq)
	callPage(uintptr(entryAddr))
	busy.Store(0)

	sig := int(get64(ctx, L.CtxSig))
	r.Sig = sig
	r.Code = int(int32(get64(ctx, L.CtxCode)))
	addr := get64(ctx, L.CtxAddr)
	r.Addr = hex(addr)
	pc := get64(ctx, L.CtxOut+8*32)
	r.PC = hex(pc)
	r.X = make([]string, 31)
	for i := 0; i < 31; i++ {
		r.X[i] = hex(get64(ctx, L.CtxOut+8*i))
	}
	r.SP = hex(get64(ctx, L.CtxOut+8*31))
	r.NZCV = int(get64(ctx, L.CtxOut+8*33)>>28) & 15
	if binary.LittleEndian.Uint32(ctx[L.CtxOutFP:]) != L.FPSIMDMagic {
		r.Status, r.Note = "error", "signal frame has no fpsimd_context first"
		return r
	}
	if back := get64(ctx, L.CtxFPCRBack); back != fpcr {
		r.Status, r.Note = "error", fmt.Sprintf("fpcr %#x does not read back (got %#x): this CPU does not implement those bits", fpcr, back)
		return r
	}
	r.FPSR = hex(uint64(binary.LittleEndian.Uint32(ctx[L.CtxOutFP+8:])))
	r.FPCR = hex(uint64(binary.LittleEndian.Uint32(ctx[L.CtxOutFP+12:])))
	r.V = make([]string, 32)
	for i := 0; i < 32; i++ {
		r.V[i] = hex128(get64(ctx, L.CtxOutFP+16+16*i), get64(ctx, L.CtxOutFP+16+16*i+8))
	}
	for i := range data {
		if data[i] != L.Pattern(c.Seed, uint64(i)) {
			r.Mem = append(r.Mem, [2]int{i, int(data[i])})
		}
	}
	switch {
	case sig == sigALRM:
		r.Status = "selfloop"
	case pc == L.TestPC:
		r.Status = "fault"
	case sig == sigSEGV && addr == pc,
		sig == sigILL && pc >= L.CodePage && pc < L.CodePage+L.PageSize,
		sig == sigBUS && pc%4 != 0:
		r.Status = "ok"
	default:
		r.Status = "escaped"
		r.Note = "control reached mapped executable memory outside the code page"
	}
	return r
}

func main() {
	dump := flag.Bool("dump-trampoline", false, "write the trampoline words (raw little-endian) to stdout and exit")
	limit := flag.Duration("timeout", time.Second, "watchdog limit for one case (branch-to-self)")
	printDCZID := flag.Bool("dczid", false, "print this CPU's DCZID_EL0 (decimal) and exit")
	flag.Parse()
	if *printDCZID {
		fmt.Println(dczid)
		return
	}

	words := buildTrampoline()
	if *dump {
		b := make([]byte, 4*len(words))
		for i, w := range words {
			binary.LittleEndian.PutUint32(b[4*i:], w)
		}
		os.Stdout.Write(b)
		return
	}

	if !strings.Contains(os.Getenv("GODEBUG"), "asyncpreemptoff=1") {
		// An asynchronous-preemption SIGURG landing while the test instruction runs would
		// enter the Go signal handler with a foreign g register.
		fmt.Fprintln(os.Stderr, "runner: GODEBUG=asyncpreemptoff=1 is required")
		os.Exit(2)
	}
	runtime.LockOSThread()
	debug.SetGCPercent(-1)
	runtime.GOMAXPROCS(2)

	const rwx = syscall.PROT_READ | syscall.PROT_WRITE | syscall.PROT_EXEC
	entry := mmapFixed(L.EntryPage, L.PageSize, rwx)
	for i, w := range words {
		binary.LittleEndian.PutUint32(entry[4*i:], w)
	}
	ctx = mmapFixed(L.CtxPage, L.PageSize, syscall.PROT_READ|syscall.PROT_WRITE)
	code = mmapFixed(L.CodePage, L.PageSize, rwx)
	data = mmapFixed(L.DataBase, L.DataSize, syscall.PROT_READ|syscall.PROT_WRITE)
	installHandlers()
	go watchdog(syscall.Gettid(), *limit)

	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<20)
	out := bufio.NewWriterSize(os.Stdout, 1<<16)
	enc := json.NewEncoder(out)
	var seq int64
	for in.Scan() {
		line := in.Bytes()
		if len(line) == 0 {
			continue
		}
		var c L.Case
		if err := json.Unmarshal(line, &c); err != nil {
			fmt.Fprintf(os.Stderr, "runner: bad case: %v\n", err)
			os.Exit(2)
		}
		seq++
		r := runCase(&c, seq)
		enc.Encode(&r)
		out.Flush() // per case, so a harness crash loses nothing but the case that caused it
	}
	out.Flush()
}
