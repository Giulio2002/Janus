// Package sys holds the kernel examples: Go functions whose behaviour depends on Linux. Their
// proofs model the kernel as an environment with an explicit I/O trace
// (Janus/Contracts/Syscall.lean, Janus/Contracts/SyscallAmd64.lean): every SVC #0 / SYSCALL
// instruction, every read of a time or ID register and the vDSO clock functions are `.syscall`
// stubs, whose effect is given by per-system-call contracts; the scheduler hooks of
// syscall.Syscall (runtime.entersyscall, runtime.exitsyscall) are runtime contracts.
package sys

import (
	"runtime"
	"syscall"
	"time"
)

// WriteOut writes p to standard output with a single write(2) (syscall.Write).
//
//go:noinline
func WriteOut(p []byte) (int, error) { return syscall.Write(1, p) }

// Pid returns the process ID (syscall.Getpid: a raw system call, no scheduler hooks).
//
//go:noinline
func Pid() int { return syscall.Getpid() }

// NowNano returns the wall-clock time in nanoseconds since the Unix epoch
// (time.Now().UnixNano(), read through the vDSO).
//
//go:noinline
func NowNano() int64 { return time.Now().UnixNano() }

// MustNonNeg returns x, or stops the program at a breakpoint trap (runtime.Breakpoint: BRK on
// arm64, INT3 on amd64) when x is negative.
//
//go:noinline
func MustNonNeg(x int64) int64 {
	if x < 0 {
		runtime.Breakpoint()
	}
	return x
}
