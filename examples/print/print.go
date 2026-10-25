// Package print holds the print/println examples (R8): Go functions whose only effect is the
// builtin print or println, i.e. bytes written to standard error (fd 2) with write(2). Their
// proofs (examples/proofs-print) run the runtime's print functions from the binary
// (runtime.printstring, printuint, printint, printbool, printsp, printnl, gwrite,
// recordForPanic, writeErr, writeErrData, write, write1 down to its SVC #0 / SYSCALL) under
// the kernel semantics of Janus/Contracts/Syscall.lean; runtime.printlock/printunlock and
// runtime.memmove are runtime contracts (Janus/Contracts/Print.lean).
package print

import "unsafe"

// PrintX prints "x = " and x in decimal, then a newline.
//
//go:noinline
func PrintX(x uint64) { println("x =", x) }

// PrintBool prints true or false and a newline.
//
//go:noinline
func PrintBool(b bool) { println(b) }

// PrintNeg prints -17 (no newline).
//
//go:noinline
func PrintNeg() { print(-17) }

// PrintStr prints s and a newline.
//
//go:noinline
func PrintStr(s string) { println(s) }

// PrintInt prints a signed integer and a newline.
//
//go:noinline
func PrintInt(v int64) { println(v) }

// PrintHex prints a pointer-sized value in hexadecimal (print of a pointer).
//
//go:noinline
func PrintPtr(p unsafe.Pointer) { println(p) }

// PrintUintptr prints a uintptr (in hexadecimal).
//
//go:noinline
func PrintUintptr(p uintptr) { println(p) }

// PrintSlice prints a slice header: [len/cap]0xptr.
//
//go:noinline
func PrintSlice(s []byte) { println(s) }

// PrintEface prints an empty interface: (0xtype,0xdata).
//
//go:noinline
func PrintEface(e any) { println(e) }

// Stringer is a non-empty interface for PrintIface.
type Stringer interface{ String() string }

// PrintIface prints a non-empty interface: (0xitab,0xdata).
//
//go:noinline
func PrintIface(i Stringer) { println(i) }

// PrintF64 prints a float64 (strconv 'g', shortest) and a newline.
//
//go:noinline
func PrintF64(v float64) { println(v) }

// PrintF32 prints a float32.
//
//go:noinline
func PrintF32(v float32) { println(v) }

// PrintC128 prints a complex128.
//
//go:noinline
func PrintC128(c complex128) { println(c) }

// PrintC64 prints a complex64.
//
//go:noinline
func PrintC64(c complex64) { println(c) }
