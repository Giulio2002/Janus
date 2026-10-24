//go:build amd64

// Command runner executes single x86-64 instructions natively on the host and reports the
// resulting architectural state. It reads layout.Case JSON lines on stdin and writes
// layout.HW JSON lines.
//
// Mechanism (no per-case subprocess):
//
//   - The instruction bytes are written at layout.TestPC in an RWX page whose every other
//     byte is 0xCC (INT3).
//   - callPage (trampoline_amd64.s) saves the host callee state in the context page, loads
//     XMM0-15 and the 16 GPRs of the case and enters TestPC with IRETQ, whose frame sets
//     RSP and RFLAGS (the case's status flags, plus TF) atomically with RIP.
//   - With TF set, the CPU raises a single-step debug trap after exactly one instruction:
//     SIGTRAP with si_code TRAP_TRACE and saved RIP = the next instruction (TestPC + len on
//     fall-through, the branch target on a taken branch, mapped or not). An instruction that
//     itself faults raises SIGSEGV/SIGBUS/SIGILL/SIGFPE (or SIGTRAP for INT3/INT1) with the
//     saved RIP at (or, for INT3, just after) TestPC.
//   - A raw signal handler (rt_sigaction, bypassing the Go runtime, on the thread's
//     sigaltstack) copies uc_mcontext and the XMM registers into the context page, resets the
//     x87/SSE control state in the frame, clears TF/DF/AC and redirects the saved RIP to a
//     resume sequence that restores the host registers and returns into Go.
//
// Safety: case bytes containing system-call, segment-load, FP-environment-load or other
// system encodings are refused (layout.Forbidden), and a seccomp filter makes every system
// call from the code page, and every call outside a short allow list, fail with EPERM.
package main

import (
	"bufio"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"math/big"
	"os"
	"runtime"
	"runtime/debug"
	"strconv"
	"strings"
	"sync/atomic"
	"syscall"
	"time"
	"unsafe"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
)

func callPage()
func handler()
func restorer()
func resume()
func addrs() (handler, restorer uintptr)
func cpuid(eax, ecx uint32) (a, b, c, d uint32)

const (
	sigILL  = 4
	sigTRAP = 5
	sigBUS  = 7
	sigFPE  = 8
	sigSEGV = 11
	sigALRM = 14

	mapFixedNoreplace = 0x100000

	userCS = 0x33
	userSS = 0x2b
	tf     = 0x100
)

// Linux uc_mcontext.gregs indices.
const (
	gR8 = iota
	gR9
	gR10
	gR11
	gR12
	gR13
	gR14
	gR15
	gRDI
	gRSI
	gRBP
	gRBX
	gRDX
	gRAX
	gRCX
	gRSP
	gRIP
	gEFL
)

// encoding order RAX RCX RDX RBX RSP RBP RSI RDI R8..R15 -> gregs index
var gregOf = [16]int{gRAX, gRCX, gRDX, gRBX, gRSP, gRBP, gRSI, gRDI, gR8, gR9, gR10, gR11, gR12, gR13, gR14, gR15}

var ctx, code, data []byte

func mmapFixed(addr uint64, size int, prot int) []byte {
	p, _, errno := syscall.Syscall6(syscall.SYS_MMAP, uintptr(addr), uintptr(size), uintptr(prot),
		uintptr(syscall.MAP_PRIVATE|syscall.MAP_ANONYMOUS|mapFixedNoreplace), ^uintptr(0), 0)
	if errno != 0 || uint64(p) != addr {
		fmt.Fprintf(os.Stderr, "runner: mmap %#x failed: %v (got %#x)\n", addr, errno, p)
		os.Exit(2)
	}
	return unsafe.Slice((*byte)(unsafe.Pointer(p)), size)
}

type sigactiont struct {
	handler  uint64
	flags    uint64
	restorer uint64
	mask     uint64
}

func installHandlers() {
	h, r := addrs()
	const saSiginfo, saOnstack, saRestorer = 0x4, 0x08000000, 0x04000000
	for _, s := range []int{sigILL, sigTRAP, sigBUS, sigFPE, sigSEGV, sigALRM} {
		act := sigactiont{handler: uint64(h), flags: saSiginfo | saOnstack | saRestorer,
			restorer: uint64(r), mask: ^uint64(0) &^ (1<<(sigILL-1) | 1<<(sigSEGV-1) | 1<<(sigBUS-1) | 1<<(sigFPE-1) | 1<<(sigTRAP-1))}
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
	s = strings.TrimPrefix(strings.TrimPrefix(s, "0x"), "0X")
	return strconv.ParseUint(s, 16, 64)
}

// parseHex128 returns the little-endian 16 bytes of a hex 128-bit value.
func parseHex128(s string) ([16]byte, error) {
	var out [16]byte
	s = strings.TrimPrefix(strings.TrimPrefix(s, "0x"), "0X")
	v, ok := new(big.Int).SetString(s, 16)
	if !ok || v.Sign() < 0 || v.BitLen() > 128 {
		return out, fmt.Errorf("bad xmm %q", s)
	}
	b := v.FillBytes(make([]byte, 16)) // big-endian
	for i := 0; i < 16; i++ {
		out[i] = b[15-i]
	}
	return out, nil
}

func hex64(v uint64) string { return "0x" + strconv.FormatUint(v, 16) }

func hex128(b []byte) string {
	be := make([]byte, 16)
	for i := 0; i < 16; i++ {
		be[i] = b[15-i]
	}
	return "0x" + new(big.Int).SetBytes(be).Text(16)
}

var busy atomic.Int64

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

var allowForbidden bool

func runCase(c *L.Case, seq int64) L.HW {
	r := L.HW{ID: c.ID}
	var b []byte
	var err error
	if len(c.Seq) > 0 {
		// audit/rt-model sequence mode: every instruction is checked on its own
		for _, h := range c.Seq {
			x, err := hex.DecodeString(strings.TrimPrefix(h, "0x"))
			if err != nil || len(x) == 0 || len(x) > 15 {
				r.Status, r.Note = "error", "bad seq bytes"
				return r
			}
			if L.Forbidden(x) || L.IsRepString(x) {
				r.Status, r.Note = "error", "forbidden encoding in seq (refused)"
				return r
			}
			b = append(b, x...)
		}
		if len(b) > 0x600 {
			r.Status, r.Note = "error", "seq too long"
			return r
		}
	} else {
		b, err = hex.DecodeString(strings.TrimPrefix(c.Bytes, "0x"))
		if err != nil || len(b) == 0 || len(b) > 15 {
			r.Status, r.Note = "error", "bad bytes"
			return r
		}
		if L.Forbidden(b) && !allowForbidden {
			r.Status, r.Note = "error", "forbidden encoding (refused)"
			return r
		}
	}
	seqEnd := uint64(L.TestPC + len(b))
	for i := range code {
		code[i] = 0xCC
	}
	copy(code[L.TestPC-L.CodePage:], b)
	for i := range data {
		data[i] = L.Pattern(c.Seed, uint64(i))
	}
	for _, e := range c.Init {
		if e[0] < 0 || e[0] >= L.DataSize || e[1] < 0 || e[1] > 255 {
			r.Status, r.Note = "error", "bad init"
			return r
		}
		data[e[0]] = byte(e[1])
	}
	initial := make([]byte, len(data))
	copy(initial, data)
	var regs [16]uint64
	for i := 0; i < 16; i++ {
		v, err := parseHex(c.Regs[i])
		if err != nil {
			r.Status, r.Note = "error", "bad reg"
			return r
		}
		regs[i] = v
		put64(ctx, L.CtxInRegs+8*i, v)
	}
	for i := 0; i < 16; i++ {
		x, err := parseHex128(c.XMM[i])
		if err != nil {
			r.Status, r.Note = "error", err.Error()
			return r
		}
		copy(ctx[L.CtxInXMM+16*i:], x[:])
	}
	if len(c.YMMH) != 0 && len(c.YMMH) != 16 {
		r.Status, r.Note = "error", "ymmh must have 16 entries"
		return r
	}
	for i := 0; i < 16; i++ {
		var y [16]byte
		if len(c.YMMH) == 16 {
			y, err = parseHex128(c.YMMH[i])
			if err != nil {
				r.Status, r.Note = "error", err.Error()
				return r
			}
		}
		copy(ctx[L.CtxInYMMH+16*i:], y[:])
	}
	var fsBase uint64
	if c.FSBase != "" {
		fsBase, err = parseHex(c.FSBase)
		// WRFSBASE needs a canonical address; only user (lower-half) values are accepted
		if err != nil || fsBase >= 1<<47 {
			r.Status, r.Note = "error", "bad fsbase"
			return r
		}
	}
	put64(ctx, L.CtxInFS, fsBase)
	mxcsr := uint64(L.DefaultMXCSR)
	if c.MXCSR != "" {
		mxcsr, err = parseHex(c.MXCSR)
		// LDMXCSR with a reserved bit set is #GP (in the trampoline, not at TestPC)
		if err != nil || mxcsr&^L.MXCSRMask != 0 {
			r.Status, r.Note = "error", "bad mxcsr"
			return r
		}
	}
	put64(ctx, L.CtxInMXCSR, mxcsr)
	put64(ctx, L.CtxFrame, L.TestPC)
	put64(ctx, L.CtxFrame+8, userCS)
	put64(ctx, L.CtxFrame+16, uint64(c.RFlags&(L.StatusFlags|L.FlagDF))|0x202|tf)
	put64(ctx, L.CtxFrame+24, regs[4])
	put64(ctx, L.CtxFrame+32, userSS)
	put64(ctx, L.CtxSig, 0)
	put64(ctx, L.CtxInflight, 1)
	busy.Store(seq)
	callPage()
	g := func(i int) uint64 { return get64(ctx, L.CtxOutGRegs+8*i) }
	// A REP string instruction traps after every iteration with RIP still at TestPC (SDM
	// Vol. 3 §18.3.1.4): re-enter it from the captured state until RIP moves on or it faults.
	// Sequence mode re-enters from the captured state at the captured RIP while it stays inside
	// the sequence (straight-line code: at most one step per instruction, plus slack).
	if L.IsRepString(b) || len(c.Seq) > 0 {
		for int(get64(ctx, L.CtxSig)) == sigTRAP && int(int32(get64(ctx, L.CtxCode))) == L.TrapTrace &&
			((len(c.Seq) == 0 && g(gRIP) == L.TestPC && r.Iters < 1<<16) ||
				(len(c.Seq) > 0 && g(gRIP) >= L.TestPC && g(gRIP) < seqEnd && r.Iters < 4*len(c.Seq))) {
			reRIP := uint64(L.TestPC)
			if len(c.Seq) > 0 {
				reRIP = g(gRIP)
			}
			r.Iters++
			for i := 0; i < 16; i++ {
				put64(ctx, L.CtxInRegs+8*i, g(gregOf[i]))
			}
			if get64(ctx, L.CtxOutHasFP) == 1 {
				copy(ctx[L.CtxInXMM:L.CtxInXMM+256], ctx[L.CtxOutXMM:L.CtxOutXMM+256])
				if xbv := get64(ctx, L.CtxOutXBV); xbv != ^uint64(0) {
					if xbv&4 != 0 {
						copy(ctx[L.CtxInYMMH:L.CtxInYMMH+256], ctx[L.CtxOutYMMH:L.CtxOutYMMH+256])
					} else {
						clear(ctx[L.CtxInYMMH : L.CtxInYMMH+256])
					}
				}
			}
			if m := get64(ctx, L.CtxOutMXCSR); m != ^uint64(0) {
				put64(ctx, L.CtxInMXCSR, m&L.MXCSRMask)
			}
			efl := g(gEFL)
			put64(ctx, L.CtxFrame, reRIP)
			put64(ctx, L.CtxFrame+8, userCS)
			put64(ctx, L.CtxFrame+16, efl&(L.StatusFlags|L.FlagDF)|0x202|tf)
			put64(ctx, L.CtxFrame+24, g(gRSP))
			put64(ctx, L.CtxFrame+32, userSS)
			put64(ctx, L.CtxSig, 0)
			put64(ctx, L.CtxInflight, 1)
			callPage()
		}
	}
	busy.Store(0)

	sig := int(get64(ctx, L.CtxSig))
	r.Sig = sig
	r.Code = int(int32(get64(ctx, L.CtxCode)))
	addr := get64(ctx, L.CtxAddr)
	r.Addr = hex64(addr)
	pc := g(gRIP)
	r.PC = hex64(pc)
	r.Regs = make([]string, 16)
	for i := 0; i < 16; i++ {
		r.Regs[i] = hex64(g(gregOf[i]))
	}
	r.RFlags = int(g(gEFL)) & L.StatusFlags
	r.DF = g(gEFL)&L.FlagDF != 0
	if get64(ctx, L.CtxOutHasFP) == 1 {
		r.MXCSR = hex64(get64(ctx, L.CtxOutMXCSR) & 0xFFFFFFFF)
		r.XMM = make([]string, 16)
		for i := 0; i < 16; i++ {
			r.XMM[i] = hex128(ctx[L.CtxOutXMM+16*i : L.CtxOutXMM+16*i+16])
		}
		if xbv := get64(ctx, L.CtxOutXBV); xbv != ^uint64(0) {
			// XSTATE_BV bit 2 clear: the AVX state is in its initial configuration (all upper
			// halves zero) and the area's contents are not meaningful
			r.YMMH = make([]string, 16)
			for i := 0; i < 16; i++ {
				if xbv&4 != 0 {
					r.YMMH[i] = hex128(ctx[L.CtxOutYMMH+16*i : L.CtxOutYMMH+16*i+16])
				} else {
					r.YMMH[i] = "0x0"
				}
			}
		}
	}
	for i := range data {
		if data[i] != initial[i] {
			r.Mem = append(r.Mem, [2]int{i, int(data[i])})
		}
	}
	switch {
	case sig == sigALRM:
		r.Status = "selfloop"
	case sig == sigTRAP && r.Code == L.TrapTrace:
		r.Status = "ok"
	case len(c.Seq) > 0 && pc >= L.TestPC && pc < seqEnd:
		// a sequence instruction faulted (a hardware fault leaves RIP at the instruction)
		r.Status = "fault"
	case pc == L.TestPC:
		r.Status = "fault"
	case sig == sigTRAP && pc > L.TestPC && pc <= L.TestPC+16:
		// INT3 / INT1 (possibly prefixed): with TF set, only the instruction under test can
		// have executed, so this is that instruction trapping.
		r.Status, r.Note = "fault", "int3/int1 at TestPC"
	default:
		r.Status = "escaped"
		r.Note = fmt.Sprintf("unexpected signal %d code %d at %#x", sig, r.Code, pc)
	}
	return r
}

// checkCPU makes sure the trampoline's RDFSBASE/WRFSBASE (FSGSBASE, enabled by the kernel:
// AT_HWCAP2 bit 1) and VINSERTI128 (AVX2) are available, and that the signal frame's XSAVE
// layout has YMM_Hi128 where the handler reads it.
func checkCPU() {
	auxv, err := os.ReadFile("/proc/self/auxv")
	if err != nil {
		fmt.Fprintf(os.Stderr, "runner: %v\n", err)
		os.Exit(2)
	}
	ok := false
	for i := 0; i+16 <= len(auxv); i += 16 {
		if binary.LittleEndian.Uint64(auxv[i:]) == 26 { // AT_HWCAP2
			ok = binary.LittleEndian.Uint64(auxv[i+8:])&2 != 0 // HWCAP2_FSGSBASE
		}
	}
	if !ok {
		fmt.Fprintln(os.Stderr, "runner: the kernel does not enable FSGSBASE (needed to run FS-relative cases)")
		os.Exit(2)
	}
	_, ebx, _, _ := cpuid(0xD, 2)
	_, ebx7, _, _ := cpuid(7, 0)
	if ebx7&(1<<5) == 0 || ebx != L.XsaveYMMHOffset {
		fmt.Fprintf(os.Stderr, "runner: need AVX2 and YMM_Hi128 at XSAVE offset %d (CPUID: AVX2 %v, offset %d)\n",
			L.XsaveYMMHOffset, ebx7&(1<<5) != 0, ebx)
		os.Exit(2)
	}
}

func main() {
	limit := flag.Duration("timeout", time.Second, "watchdog limit for one case")
	flag.BoolVar(&allowForbidden, "unsafe-allow-forbidden", false, "test only: run forbidden encodings (to check the seccomp filter)")
	flag.Parse()

	if !strings.Contains(os.Getenv("GODEBUG"), "asyncpreemptoff=1") {
		fmt.Fprintln(os.Stderr, "runner: GODEBUG=asyncpreemptoff=1 is required")
		os.Exit(2)
	}
	checkCPU()
	runtime.LockOSThread()
	debug.SetGCPercent(-1)
	runtime.GOMAXPROCS(2)

	const rwx = syscall.PROT_READ | syscall.PROT_WRITE | syscall.PROT_EXEC
	ctx = mmapFixed(L.CtxPage, L.PageSize, syscall.PROT_READ|syscall.PROT_WRITE)
	code = mmapFixed(L.CodePage, L.PageSize, rwx)
	data = mmapFixed(L.DataBase, L.DataSize, syscall.PROT_READ|syscall.PROT_WRITE)
	installHandlers()
	go watchdog(syscall.Gettid(), *limit)
	time.Sleep(10 * time.Millisecond) // let the runtime start its threads and timers
	installSeccomp()

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
		out.Flush()
	}
	out.Flush()
}
