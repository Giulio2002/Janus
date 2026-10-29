package main

// RT 7 and 8: build inputs the verifier identity must cover, and builds from different sources that
// must not claim the same identity. Real builds of copies of the tree.

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// A Go assembly file is compiled with CGO_ENABLED=0 and is a build input that is not a .go file: editing
// its body (the Go declaration unchanged) must change the identity or force the executable fallback.
func TestRT07AssemblyFileIsPartOfTheIdentity(t *testing.T) {
	if testing.Short() {
		t.Skip("builds the command several times")
	}
	if runtimeGOARCH() != "amd64" {
		t.Skip("the assembly body below is amd64")
	}
	scratch, err := os.MkdirTemp(os.Getenv("JANUS_TEST_SCRATCH"), "verifierid-rt-")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(scratch)
	a := filepath.Join(scratch, "wt")
	os.MkdirAll(a, 0o755)
	copyTreeForBuild(t, a)
	decl := "package main\n\nfunc rtAsmValue() int\n\nvar _ = rtAsmValue\n"
	body := func(v string) string {
		return "#include \"textflag.h\"\n\nTEXT ·rtAsmValue(SB), NOSPLIT, $0-8\n\tMOVQ $" + v + ", AX\n\tMOVQ AX, ret+0(FP)\n\tRET\n"
	}
	os.WriteFile(filepath.Join(a, "cmd/janus/rtasm.go"), []byte(decl), 0o644)
	os.WriteFile(filepath.Join(a, "cmd/janus/rtasm_amd64.s"), []byte(body("1")), 0o644)
	nocgo := []string{"CGO_ENABLED=0"}
	id1 := buildCopy(t, a, filepath.Join(scratch, "j1"), nocgo)
	os.WriteFile(filepath.Join(a, "cmd/janus/rtasm_amd64.s"), []byte(body("2")), 0o644)
	id2 := buildCopy(t, a, filepath.Join(scratch, "j2"), nocgo)
	if id1 == id2 {
		t.Fatalf("two binaries with different assembly bodies share the identity %s", id1)
	}
}

// -overlay replaces file contents at build time: the embedded copy of a replaced source must be what is hashed
// (or the build must fall back), never the on-disk original.
func TestRT08OverlayBuildDoesNotClaimTheOriginalIdentity(t *testing.T) {
	if testing.Short() {
		t.Skip("builds the command several times")
	}
	scratch, err := os.MkdirTemp(os.Getenv("JANUS_TEST_SCRATCH"), "verifierid-rt-")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(scratch)
	a := filepath.Join(scratch, "wt")
	os.MkdirAll(a, 0o755)
	copyTreeForBuild(t, a)
	nocgo := []string{"CGO_ENABLED=0"}
	idA := buildCopy(t, a, filepath.Join(scratch, "ja"), nocgo)
	mainGo := filepath.Join(a, "cmd/janus/main.go")
	src, _ := os.ReadFile(mainGo)
	repl := filepath.Join(scratch, "main_overlay.go")
	os.WriteFile(repl, append(src, "\n// overlaid\nfunc init() { _ = 1 }\n"...), 0o644)
	ov := filepath.Join(scratch, "overlay.json")
	os.WriteFile(ov, []byte(`{"Replace":{`+jsonStr(mainGo)+`:`+jsonStr(repl)+`}}`), 0o644)
	id := buildCopy(t, a, filepath.Join(scratch, "jo"), nocgo, "-overlay", ov)
	if id == idA {
		t.Fatalf("an overlaid source claims the identity %s of the original", idA)
	}
	if !strings.HasPrefix(id, "src:") && !strings.HasPrefix(id, "exe:") {
		t.Fatal(id)
	}
}

func jsonStr(s string) string { return `"` + strings.ReplaceAll(s, `"`, `\"`) + `"` }
