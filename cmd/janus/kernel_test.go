package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// WP-C: the instruction-level kernel and trap stubs (kernel.go).

func TestInsnStubsArm64(t *testing.T) {
	seg := Segment{Base: 0x1000, Words: []uint32{
		0xd2801588, // movz x8, #172
		0xd4000001, // svc #0
		0xd53be040, // mrs x0, cntvct_el0
		0xd4200000, // brk #0
		0x0000beef, // udf #0xbeef (in-function)
		0xd503415f, // msr dit, #1
		0xd65f03c0, // ret
		0x00000000, // padding: no stub
		0x00000000,
	}}
	got := insnStubsArm64(seg)
	want := []insnStub{
		{"syscall", 0x1004, stubSyscall}, {"env:CNTVCT_EL0", 0x1008, stubSyscall},
		{"trap:BRK", 0x100c, stubTrap}, {"trap:UDF", 0x1010, stubTrap}, {"env:MSR_DIT", 0x1014, stubSyscall},
	}
	if len(got) != len(want) {
		t.Fatalf("got %v, want %v", got, want)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Errorf("stub %d: got %v, want %v", i, got[i], want[i])
		}
	}
	// svc #1 and hlt are not kernel stubs (the decoder rejects them)
	if s := insnStubsArm64(Segment{Base: 0, Words: []uint32{0xd4000021, 0xd4400000, 0xd65f03c0}}); len(s) != 0 {
		t.Errorf("svc #1 / hlt got stubs %v", s)
	}
}

func TestInsnStubsAmd64(t *testing.T) {
	seg := Segment{Base: 0x2000, Bytes: []byte{
		0x48, 0xc7, 0xc0, 0x27, 0x00, 0x00, 0x00, // mov rax, 39
		0x0f, 0x05, // syscall
		0x0f, 0xa2, // cpuid
		0xcc,       // int3 (followed by code: not padding)
		0x0f, 0x0b, // ud2
		0xc3,             // ret
		0xcc, 0xcc, 0xcc, // padding: no stubs
	}}
	got := insnStubsAmd64(seg)
	want := []insnStub{
		{"syscall", 0x2007, stubSyscall}, {"env:CPUID", 0x2009, stubSyscall},
		{"trap:INT3", 0x200b, stubTrap}, {"trap:UD2", 0x200c, stubTrap},
	}
	if len(got) != len(want) {
		t.Fatalf("got %v, want %v", got, want)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Errorf("stub %d: got %v, want %v", i, got[i], want[i])
		}
	}
}

func TestKernelStubsPerArch(t *testing.T) {
	if k, ok := stubKindFor("amd64", "time.now"); !ok || k != stubSyscall {
		t.Errorf("amd64 time.now: %v %v", k, ok)
	}
	if _, ok := stubKindFor("arm64", "time.now"); ok {
		t.Errorf("arm64 time.now is Go code, not a stub")
	}
	for _, n := range []string{"runtime.walltime.abi0", "runtime.nanotime1.abi0"} {
		if k, ok := stubKindFor("arm64", n); !ok || k != stubSyscall {
			t.Errorf("arm64 %s: %v %v", n, k, ok)
		}
	}
	if !isTerminalStub("runtime.nanotime1.abi0") || !isTerminalStub("time.now") {
		t.Errorf("vDSO stubs must be terminal")
	}
}

// TestSysExtraction builds examples/sys for both ISAs and checks the stubs of the kernel examples.
func TestSysExtraction(t *testing.T) {
	dir := t.TempDir()
	for _, arch := range []string{"arm64", "amd64"} {
		bin := filepath.Join(dir, "sys-"+arch)
		cmd := exec.Command("go", "build", "-trimpath", "-buildvcs=false", "-o", bin, "./cmd")
		cmd.Dir = filepath.Join(repoRoot, "examples", "sys")
		cmd.Env = append(os.Environ(), "GOOS=linux", "GOARCH="+arch, "GOAMD64=v1", "CGO_ENABLED=0")
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("build %s: %v\n%s", arch, err, out)
		}
		cases := map[string][]string{
			"example.com/sys.Pid":        {"syscall"},
			"example.com/sys.MustNonNeg": {"trap:"},
			"example.com/sys.NowNano":    {map[string]string{"arm64": "runtime.walltime.abi0", "amd64": "time.now"}[arch]},
			"example.com/sys.WriteOut":   {"syscall"},
		}
		for sym, wants := range cases {
			out := filepath.Join(dir, arch+strings.ReplaceAll(sym, "/", "_"))
			args := []string{"extract", bin, sym, out}
			if strings.HasSuffix(sym, "WriteOut") {
				args = append(args, "--contract", "runtime.entersyscall", "--contract", "runtime.exitsyscall", "--contract", "runtime.convT64")
			}
			if code, _, stderr := runJanus(t, args...); code != 0 {
				t.Fatalf("%s %s: %s", arch, sym, stderr)
			}
			id := readIdentity(t, out)
			for _, w := range wants {
				found := false
				for _, s := range id.Stubs {
					if strings.HasPrefix(s.Name, w) && (s.Kind == string(stubSyscall) || s.Kind == string(stubTrap)) {
						found = true
					}
				}
				if !found {
					t.Errorf("%s %s: no %q stub in %v", arch, sym, w, id.Stubs)
				}
			}
			lean, _ := os.ReadFile(filepath.Join(out, "Extracted.lean"))
			if !strings.Contains(string(lean), "kind := .syscall") && !strings.Contains(string(lean), "kind := .trap") {
				t.Errorf("%s %s: Extracted.lean has no kernel/trap stub", arch, sym)
			}
		}
	}
}
