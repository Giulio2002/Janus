package main

// Kernel and trap stubs (WP-C, Janus/Contracts/Syscall.lean, Janus/Contracts/SyscallAmd64.lean).
//
// Two kinds of stub stand for the program's interaction with Linux:
//
//   - stubSyscall ("syscall"): a point where the result comes from the kernel or the
//     environment. At instruction level: every SVC #0 / SYSCALL instruction and every read of
//     an environment register (arm64 MRS CNTVCT_EL0, CNTFRQ_EL0, MIDR_EL1, DIT and MSR DIT;
//     amd64 CPUID, XGETBV, RDTSC, RDTSCP) inside an extracted function, at its own address.
//     At function level: the vDSO clock functions (runtimeKernelStubs), classified and pinned
//     like every runtime stub (classifyStub, stubpin.go).
//   - stubTrap ("trap"): a trap instruction inside an extracted function (BRK, UDF; INT3,
//     INT 3, UD2, HLT).
//
// The instruction-level stubs are found by scanning the copied code (insnStubs). Their
// placement is not trusted: the Lean side reads the word (bytes) at a stub's address and
// accepts it only if it is the instruction the stub stands for (Kernel.siteOf, Kernel.trapAt).
// A missed instruction is not unsound either: the model faults on it (Fault.kernel /
// Fault.trap), so no theorem gets past it.

import (
	"bytes"
	"fmt"
	"sort"
)

const (
	// stubSyscall: Janus.StubKind.syscall.
	stubSyscall StubKind = "syscall"
	// stubTrap: Janus.StubKind.trap.
	stubTrap StubKind = "trap"
)

// runtimeKernelStubs are the vDSO clock functions per architecture, by linked name: Go 1.26's
// runtime/sys_linux_arm64.s (walltime, nanotime1, both ABI0) and, on amd64,
// runtime/sys_linux_amd64.s (nanotime1, ABI0) and runtime/time_linux_amd64.s (time.now,
// ABIInternal; on arm64 time.now is the Go function runtime.time_now, which is extracted).
// Their effect is the contract of the Lean site (Kernel.Site.walltime/.nanotime,
// Amd64.Kernel.Site.timeNow/.nanotime).
var runtimeKernelStubs = map[string]map[string]bool{
	"arm64": {"runtime.walltime.abi0": true, "runtime.nanotime1.abi0": true},
	"amd64": {"runtime.nanotime1.abi0": true, "time.now": true},
}

// kernelStubAnyArch reports whether name is a vDSO clock stub on some architecture.
func kernelStubAnyArch(name string) bool {
	for _, m := range runtimeKernelStubs {
		if m[name] {
			return true
		}
	}
	return false
}

// stubKindFor classifies a linked symbol name of a GOARCH binary (name only; classifyStub adds
// the checks that make the name trustworthy).
func stubKindFor(goarch, name string) (StubKind, bool) {
	if runtimeKernelStubs[goarch][name] {
		return stubSyscall, true
	}
	if kernelStubAnyArch(name) {
		return "", false // a vDSO stub of the other architecture (arm64 time.now is Go code)
	}
	return stubKind(name)
}

// stubPkgDirOK reports whether the pclntab package pkg of stub name may live in the GOROOT/src
// directory dir: the same, except time.now, which package time declares and runtime defines
// (runtime/time_linux_amd64.s, `TEXT time·now`).
func stubPkgDirOK(name, pkg, dir string) bool {
	return pkg == dir || (name == "time.now" && pkg == "time" && dir == "runtime")
}

// insnStub is one instruction-level stub of a copied function.
type insnStub struct {
	Name string
	Addr uint64
	Kind StubKind
}

// insnStubs lists the kernel, environment and trap instructions of a copied function.
func insnStubs(goarch string, s Segment) []insnStub {
	if goarch == "amd64" {
		return insnStubsAmd64(s)
	}
	return insnStubsArm64(s)
}

// arm64SysName names an arm64 kernel/environment/trap word ("" if it is none of them). Mirrors
// Janus.Arm64.decodeSys / decodeReserved.
func arm64SysName(w uint32) (string, StubKind) {
	switch {
	case w == 0xD4000001:
		return "syscall", stubSyscall
	case w&0xFFE0001F == 0xD4200000:
		return "trap:BRK", stubTrap
	case w&0xFFFFFFE0 == 0xD53BE040:
		return "env:CNTVCT_EL0", stubSyscall
	case w&0xFFFFFFE0 == 0xD53BE000:
		return "env:CNTFRQ_EL0", stubSyscall
	case w&0xFFFFFFE0 == 0xD5380000:
		return "env:MIDR_EL1", stubSyscall
	case w&0xFFFFFFE0 == 0xD53B42A0:
		return "env:DIT", stubSyscall
	case w&0xFFFFFFE0 == 0xD51B42A0, w == 0xD503405F, w == 0xD503415F:
		return "env:MSR_DIT", stubSyscall
	case w < 0x10000:
		return "trap:UDF", stubTrap
	}
	return "", ""
}

func insnStubsArm64(s Segment) []insnStub {
	// The run of zero words at the end of a function is alignment padding (UDF #0 that no
	// path reaches), and the targets of LDR (literal) are data: neither gets a stub.
	end := len(s.Words)
	for end > 0 && s.Words[end-1] == 0 {
		end--
	}
	lit := map[uint64]bool{}
	for _, r := range dataRefs(s.Words, s.Base) {
		if r.Kind == "ldr-literal" {
			lit[r.Target] = true
			lit[r.Target+4] = true
		}
	}
	var out []insnStub
	for i, w := range s.Words[:end] {
		pc := s.Base + 4*uint64(i)
		if lit[pc] {
			continue
		}
		if n, k := arm64SysName(w); n != "" {
			out = append(out, insnStub{Name: n, Addr: pc, Kind: k})
		}
	}
	return out
}

// amd64SysForms are the exact byte forms of Janus.Amd64.decodeSys that get a stub.
var amd64SysForms = []struct {
	bytes []byte
	name  string
	kind  StubKind
}{
	{[]byte{0x0F, 0x05}, "syscall", stubSyscall},
	{[]byte{0x0F, 0xA2}, "env:CPUID", stubSyscall},
	{[]byte{0x0F, 0x01, 0xD0}, "env:XGETBV", stubSyscall},
	{[]byte{0x0F, 0x31}, "env:RDTSC", stubSyscall},
	{[]byte{0x0F, 0x01, 0xF9}, "env:RDTSCP", stubSyscall},
	{[]byte{0xCC}, "trap:INT3", stubTrap},
	{[]byte{0xCD, 0x03}, "trap:INT3", stubTrap},
	{[]byte{0x0F, 0x0B}, "trap:UD2", stubTrap},
	{[]byte{0xF4}, "trap:HLT", stubTrap},
}

func insnStubsAmd64(s Segment) []insnStub {
	// The run of INT3 bytes at the end of a function is the linker's padding.
	end := len(s.Bytes)
	for end > 0 && s.Bytes[end-1] == 0xCC {
		end--
	}
	var out []insnStub
	for _, in := range sweepAmd64(s.Bytes[:end], s.Base) {
		off := int(in.PC - s.Base)
		for _, f := range amd64SysForms {
			if in.Inst.Len == len(f.bytes) && off+len(f.bytes) <= end && bytes.Equal(s.Bytes[off:off+len(f.bytes)], f.bytes) {
				out = append(out, insnStub{Name: f.name, Addr: in.PC, Kind: f.kind})
				break
			}
		}
	}
	return out
}

// addInsnStubs records the instruction-level stubs of a copied segment (once per address).
func (r *reacher) addInsnStubs(seg Segment) {
	for _, st := range insnStubs(r.b.GOARCH, seg) {
		if !r.stubSeen[st.Addr] {
			r.stubSeen[st.Addr] = true
			r.x.Stubs = append(r.x.Stubs, Stub{Name: st.Name, Addr: st.Addr, Kind: st.Kind})
		}
	}
}

// kernelSummary describes the kernel interface of an extraction for reports: the
// instruction-level syscall/environment/trap stubs and the vDSO stubs, as "name @ 0x...".
func kernelSummary(stubs []Stub) (kernel, traps []string) {
	for _, st := range stubs {
		switch st.Kind {
		case stubSyscall:
			kernel = append(kernel, fmt.Sprintf("%s @ 0x%x", st.Name, st.Addr))
		case stubTrap:
			traps = append(traps, fmt.Sprintf("%s @ 0x%x", st.Name, st.Addr))
		}
	}
	sort.Strings(kernel)
	sort.Strings(traps)
	return kernel, traps
}
