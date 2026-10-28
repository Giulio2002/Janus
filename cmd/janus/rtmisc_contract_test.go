package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// The rtmisc contract stubs (rtmiscContractStubs: the -d=checkptr checks, the cgo pointer
// checks and the size-specialised allocator) are linked by scripts/stubpins (so gen-stubpins measures them) and
// described by their contract library.
func TestRtmiscContractStubNames(t *testing.T) {
	src, err := os.ReadFile(filepath.Join(repoRoot, "scripts", "stubpins", "main.go"))
	if err != nil {
		t.Fatal(err)
	}
	read := func(f string) string {
		b, err := os.ReadFile(filepath.Join(repoRoot, "Janus", "Contracts", f))
		if err != nil {
			t.Fatal(err)
		}
		return string(b)
	}
	checkptr, sc, soft := read("InstrumentCalls.lean"), read("MallocSC.lean"), read("SoftFloat.lean")
	if len(rtmiscContractStubs) != 75 {
		t.Errorf("%d rtmisc contract stubs, want 75", len(rtmiscContractStubs))
	}
	for name := range rtmiscContractStubs {
		if !strings.Contains(string(src), "//go:linkname s_"+strings.TrimPrefix(name, "runtime.")+" "+name+"\n") {
			t.Errorf("scripts/stubpins does not link %s", name)
		}
		short := strings.TrimPrefix(name, "runtime.")
		switch {
		case short == "KeepAlive" || short == "fadd64" || short == "fsub64" || short == "fmul64" || short == "fdiv64":
			if !strings.Contains(soft, "`runtime."+short+"(") {
				t.Errorf("SoftFloat.lean does not describe %s", name)
			}
		case strings.HasPrefix(short, "checkptr"):
			if !strings.Contains(checkptr, "`"+short+"(") {
				t.Errorf("InstrumentCalls.lean does not describe %s", name)
			}
		case strings.HasPrefix(short, "cgoCheck"):
			if !strings.Contains(checkptr, "`runtime."+short+"(") {
				t.Errorf("InstrumentCalls.lean does not describe %s", name)
			}
		default:
			fam := strings.TrimRight(short, "0123456789")
			if !strings.Contains(sc, "`"+fam+"<") {
				t.Errorf("MallocSC.lean does not describe %s", name)
			}
		}
		if !runtimeContractStubs[name] {
			t.Errorf("%s is not in runtimeContractStubs", name)
		}
	}
}

// The soft-float contracts (Janus/Contracts/SoftFloat.lean) are IEEE 754 where the exact result is
// not tiny: examples/rtmisc/softcheck tests the runtime's own fadd64, fsub64, fmul64 and fdiv64
// against the hardware (scripts/softfloat-check.sh), and that Go's addition is not IEEE for tiny
// results (so the precondition is needed).
func TestSoftFloatRuntimeAgreesWithIEEE(t *testing.T) {
	if testing.Short() {
		t.Skip("runs the runtime's soft float on random operands")
	}
	cmd := exec.Command(filepath.Join(repoRoot, "scripts", "softfloat-check.sh"))
	cmd.Env = append(os.Environ(), "SOFTCHECK_N=100000")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("%v\n%s", err, out)
	}
}
