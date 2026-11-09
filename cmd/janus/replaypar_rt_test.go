package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Expensive: needs forged fixtures (RT_BASE = a copy of the framework library, RT_FX = the forged
// oleans, RT_TMP = scratch on disk). With RT_BASE and RT_FX set they are used as given; otherwise, in the nightly gates
// (JANUS_NIGHTLY=1), rtFixtures builds them from the repository's framework library with the real `lean` (the forged modules are
// the kernel-skipping `forged` theorem of test/redteam/attacks/R1_forged_lemma.lean under other names); elsewhere the tests skip,
// and the gate's SKIPPED-COVERAGE line says so.
func rtFixtures(t *testing.T) (base, fx, tmp string) {
	t.Helper()
	base, fx, tmp = os.Getenv("RT_BASE"), os.Getenv("RT_FX"), os.Getenv("RT_TMP")
	if base != "" && fx != "" {
		if tmp == "" {
			tmp = t.TempDir()
		}
		return
	}
	if os.Getenv("JANUS_NIGHTLY") != "1" {
		t.Skip("RT fixtures: set RT_BASE/RT_FX, or run with JANUS_NIGHTLY=1 (the nightly gates build them)")
	}
	// (not realParFixture: it takes heavyReplayMu for the rest of the test, and the caller takes it too)
	lib0 := filepath.Join(repoRoot, ".lake", "build", "lib", "lean")
	if _, err := os.Stat(filepath.Join(lib0, "Janus.olean")); err != nil {
		t.Fatalf("JANUS_NIGHTLY=1 but the repository's Janus build is not present: %v", err)
	}
	lake, err := findLake()
	if err != nil {
		t.Fatalf("JANUS_NIGHTLY=1 but %v", err)
	}
	fx = t.TempDir()
	forged := func(name string) string { // a module whose kernel check is skipped
		return "import Lean\nopen Lean in\nset_option debug.skipKernelTC true in\nrun_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {\n" +
			"  name := `" + name + ".forged, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })\n"
	}
	mods := []struct{ out, mod, src string }{
		{"zz", "Janus.Zz", forged("Janus.Zz")},
		{"zzy", "Janus.Zz.Y", forged("Janus.Zz.Y")},
		{"x86", "JanusX86Zz", forged("JanusX86Zz")},
		{"rr", "JanusReplayRoot.Foo", forged("JanusReplayRoot.Foo")},
		{"rr0", "JanusReplayRoot", forged("JanusReplayRoot")},
		{"pr", "Janus.Pr", "import Lean\ninitialize IO.println \"replaying Janus.Zz\"\ndef Janus.Pr.x := 1\n"},
		{"ok", "Janus.Okay", "import Lean\ndef Janus.Okay.x := 1\n"},
	}
	for _, m := range mods {
		rel := strings.ReplaceAll(m.mod, ".", "/")
		src := t.TempDir()
		writeBytes(t, filepath.Join(src, rel+".lean"), []byte(m.src))
		dst := filepath.Join(fx, "out", m.out, rel+".olean")
		if err := os.MkdirAll(filepath.Dir(dst), 0o755); err != nil {
			t.Fatal(err)
		}
		cmd := exec.Command(lake, "env", "lean", "--root="+src, "-o", dst, filepath.Join(src, rel+".lean"))
		cmd.Dir = repoRoot
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("building the %s fixture: %v\n%s", m.mod, err, out)
		}
	}
	if tmp == "" {
		var err error
		if base, err = janusRunBase(); err != nil {
			t.Fatal(err)
		}
		tmp, err = os.MkdirTemp(base, "rt-")
		if err != nil {
			t.Fatal(err)
		}
		t.Cleanup(func() { os.RemoveAll(tmp) })
	}
	return lib0, fx, tmp
}

// rtLibCopy is `cp -al base lib` (hard links) where the file systems allow it, else a copy.
func rtLibCopy(t *testing.T, base, lib string) {
	t.Helper()
	if out, err := exec.Command("cp", "-al", base, lib).CombinedOutput(); err != nil {
		os.RemoveAll(lib)
		if err2 := copyTree(base, lib); err2 != nil {
			t.Fatalf("%v %s; copy: %v", err, out, err2)
		}
	}
}

// RT matrix: attacks on the parallel framework replay with the real leanchecker.
type rtMatrixCase struct {
	name     string
	add      map[string]string // lib-relative dest -> fixture src
	wantFail bool
}

var rtMatrixCases = []rtMatrixCase{
	{"honest", nil, false},
	{"extra Janus.Zz forged", map[string]string{"Janus/Zz.olean": "out/zz/Janus/Zz.olean"}, true},
	{"extra Janus.Zz.Y forged, no Janus.Zz", map[string]string{"Janus/Zz/Y.olean": "out/zzy/Janus/Zz/Y.olean"}, true},
	{"JanusX86Zz forged (not a Janus.* module)", map[string]string{"JanusX86Zz.olean": "out/x86/JanusX86Zz.olean"}, false},
	{"JanusReplayRoot.Foo forged", map[string]string{"JanusReplayRoot/Foo.olean": "out/rr/JanusReplayRoot/Foo.olean"}, true},
	{"Janus.Pr with initialize printing replaying lines", map[string]string{"Janus/Pr.olean": "out/pr/Janus/Pr.olean"}, false},
	{"Janus.Okay honest extra", map[string]string{"Janus/Okay.olean": "out/ok/Janus/Okay.olean"}, false},
	{"Janus/Foo.bar.olean forged (odd component)", map[string]string{"Janus/Foo.bar.olean": "out/zz/Janus/Zz.olean"}, true},
	{"Janus/Foo bar.olean forged (space)", map[string]string{"Janus/Foo bar.olean": "out/zz/Janus/Zz.olean"}, true},
	{"Janus/.hidden.olean forged", map[string]string{"Janus/.hid.olean": "out/zz/Janus/Zz.olean"}, true},
}

// TestRTMatrix is split into one top-level test per case (TestRTMatrix_0 .. _9: each case is a full real-leanchecker replay, ~4 min,
// ten of them in one test were 40 min on the gate's critical path); this stub only checks that the ten tests cover the table.
func TestRTMatrix(t *testing.T) {
	if len(rtMatrixCases) != 10 {
		t.Fatalf("the RT matrix has %d cases; add or remove its TestRTMatrix_N test", len(rtMatrixCases))
	}
}

func TestRTMatrix_0(t *testing.T) { rtMatrixRun(t, 0) }
func TestRTMatrix_1(t *testing.T) { rtMatrixRun(t, 1) }
func TestRTMatrix_2(t *testing.T) { rtMatrixRun(t, 2) }
func TestRTMatrix_3(t *testing.T) { rtMatrixRun(t, 3) }
func TestRTMatrix_4(t *testing.T) { rtMatrixRun(t, 4) }
func TestRTMatrix_5(t *testing.T) { rtMatrixRun(t, 5) }
func TestRTMatrix_6(t *testing.T) { rtMatrixRun(t, 6) }
func TestRTMatrix_7(t *testing.T) { rtMatrixRun(t, 7) }
func TestRTMatrix_8(t *testing.T) { rtMatrixRun(t, 8) }
func TestRTMatrix_9(t *testing.T) { rtMatrixRun(t, 9) }

func rtMatrixRun(t *testing.T, i int) {
	c := rtMatrixCases[i]
	t.Log("case:", c.name)
	base, fx, rtTmp := rtFixtures(t)
	_, tc, _, runIn := realParFixture(t)
	lib := filepath.Join(rtTmp, "lib-"+filepath.Base(t.TempDir()))
	rtLibCopy(t, base, lib)
	defer os.RemoveAll(lib)
	for dst, src := range c.add {
		p := filepath.Join(lib, dst)
		os.MkdirAll(filepath.Dir(p), 0o755)
		b, err := os.ReadFile(filepath.Join(fx, src))
		if err != nil {
			t.Fatal(err)
		}
		os.WriteFile(p, b, 0o644)
	}
	out, err, calls := realPar(t, tc, lib, runIn, 4)
	t.Logf("calls=%d err=%v out=%.300q", len(calls), err, out)
	if (err != nil) != c.wantFail {
		t.Errorf("UNEXPECTED: wantFail=%v err=%v", c.wantFail, err)
	}
}

func TestRTShadowedAlias(t *testing.T) {
	lib := os.Getenv("RT_LIB")
	if lib == "" {
		base, fx, tmp := rtFixtures(t)
		lib = filepath.Join(tmp, "lib-shadow")
		rtLibCopy(t, base, lib)
		b, err := os.ReadFile(filepath.Join(fx, "out", "rr0", "JanusReplayRoot.olean"))
		if err != nil {
			t.Fatal(err)
		}
		writeBytes(t, filepath.Join(lib, "JanusReplayRoot.olean"), b) // a forged module named like the replay's root alias
	}
	_, tc, _, runIn := realParFixture(t)
	out, err, calls := realPar(t, tc, lib, runIn, 4)
	t.Logf("calls=%d err=%v out=%q", len(calls), err, out)
	if err == nil {
		t.Errorf("BLOCKER: forged root passed parallel replay")
	}
}
