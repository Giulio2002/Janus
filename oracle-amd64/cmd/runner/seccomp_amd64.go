//go:build amd64

package main

import (
	"fmt"
	"os"
	"syscall"
	"unsafe"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
)

// Safety net for executing arbitrary instruction bytes natively on a shared host.
//
// The filter (installed on every thread with SECCOMP_FILTER_FLAG_TSYNC, after
// PR_SET_NO_NEW_PRIVS) returns EPERM for
//   - any system call made from the code page (the instruction under test), and
//   - any system call that is not on a short allow list of what the Go runtime and the runner
//     need, with tgkill restricted to this process and clone to new threads.
// It never kills: a refused call just fails, so a runtime path we did not anticipate shows up
// as an error, not a dead runner.

type sockFilter struct {
	code uint16
	jt   uint8
	jf   uint8
	k    uint32
}

type sockFprog struct {
	n      uint16
	_      [6]byte
	filter *sockFilter
}

const (
	bpfLD   = 0x00
	bpfW    = 0x00
	bpfABS  = 0x20
	bpfJMP  = 0x05
	bpfJEQ  = 0x10
	bpfJGE  = 0x30
	bpfJSET = 0x40
	bpfK    = 0x00
	bpfRET  = 0x06

	retAllow = 0x7fff0000
	retErrno = 0x00050000 // | errno
	epermVal = 1

	auditArchX8664 = 0xC000003E
)

func stmt(code uint16, k uint32) sockFilter { return sockFilter{code: code, k: k} }
func jump(code uint16, k uint32, jt, jf uint8) sockFilter {
	return sockFilter{code: code, jt: jt, jf: jf, k: k}
}

// allowed system calls (x86-64 numbers).
var allowed = []uint32{
	0,   // read
	1,   // write
	3,   // close
	7,   // poll
	9,   // mmap
	10,  // mprotect
	11,  // munmap
	12,  // brk
	13,  // rt_sigaction
	14,  // rt_sigprocmask
	15,  // rt_sigreturn
	24,  // sched_yield
	28,  // madvise
	35,  // nanosleep
	39,  // getpid
	60,  // exit
	72,  // fcntl
	96,  // gettimeofday
	131, // sigaltstack
	186, // gettid
	201, // time
	202, // futex
	204, // sched_getaffinity
	228, // clock_gettime
	230, // clock_nanosleep
	231, // exit_group
	232, // epoll_wait
	233, // epoll_ctl
	270, // pselect6
	281, // epoll_pwait
	290, // eventfd2
	291, // epoll_create1
	293, // pipe2
	318, // getrandom
	441, // epoll_pwait2
}

func installSeccomp() {
	pid := uint32(os.Getpid())
	codeHi := uint32(uint64(L.CodePage) >> 32)
	codeLo := uint32(uint64(L.CodePage) & 0xffffffff)
	var p []sockFilter
	errno := stmt(bpfRET|bpfK, retErrno|epermVal)
	allow := stmt(bpfRET|bpfK, retAllow)
	// [arch] must be x86-64.
	p = append(p, stmt(bpfLD|bpfW|bpfABS, 4), jump(bpfJMP|bpfJEQ|bpfK, auditArchX8664, 1, 0), errno)
	// instruction_pointer in the code page (or just past its end): refuse.
	p = append(p,
		stmt(bpfLD|bpfW|bpfABS, 12),
		jump(bpfJMP|bpfJEQ|bpfK, codeHi, 0, 3),
		stmt(bpfLD|bpfW|bpfABS, 8),
		jump(bpfJMP|bpfJGE|bpfK, codeLo+L.PageSize+16, 1, 0),
		errno,
	)
	// nr
	p = append(p, stmt(bpfLD|bpfW|bpfABS, 0))
	// tgkill(pid, ...) only for this process
	p = append(p, jump(bpfJMP|bpfJEQ|bpfK, 234, 0, 4),
		stmt(bpfLD|bpfW|bpfABS, 16), // args[0] low
		jump(bpfJMP|bpfJEQ|bpfK, pid, 0, 1),
		allow, errno)
	// clone only with CLONE_THREAD
	p = append(p, stmt(bpfLD|bpfW|bpfABS, 0), jump(bpfJMP|bpfJEQ|bpfK, 56, 0, 4),
		stmt(bpfLD|bpfW|bpfABS, 16),
		jump(bpfJMP|bpfJSET|bpfK, 0x10000, 0, 1),
		allow, errno)
	p = append(p, stmt(bpfLD|bpfW|bpfABS, 0))
	for _, nr := range allowed {
		p = append(p, jump(bpfJMP|bpfJEQ|bpfK, nr, 0, 1), allow)
	}
	p = append(p, errno)
	prog := sockFprog{n: uint16(len(p)), filter: &p[0]}
	if _, _, e := syscall.RawSyscall6(syscall.SYS_PRCTL, 38 /* PR_SET_NO_NEW_PRIVS */, 1, 0, 0, 0, 0); e != 0 {
		fmt.Fprintf(os.Stderr, "runner: PR_SET_NO_NEW_PRIVS: %v\n", e)
		os.Exit(2)
	}
	const sysSeccomp = 317
	if r, _, e := syscall.RawSyscall(sysSeccomp, 1 /* SET_MODE_FILTER */, 1 /* TSYNC */, uintptr(unsafe.Pointer(&prog))); e != 0 || r != 0 {
		fmt.Fprintf(os.Stderr, "runner: seccomp: %v (r=%d)\n", e, r)
		os.Exit(2)
	}
}
