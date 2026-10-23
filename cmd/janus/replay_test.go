package main

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Tests for the framework olean pins, the closure check, the replay cache keys, the read-only
// framework overlay and the R1 attacks of docs/AUDIT.md (audit/attacks/R1_*).

func writeBytes(t *testing.T, p string, b []byte) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(p, b, 0o644); err != nil {
		t.Fatal(err)
	}
}

func TestPins(t *testing.T) {
	lib := t.TempDir()
	writeBytes(t, filepath.Join(lib, "Janus.olean"), []byte("root"))
	writeBytes(t, filepath.Join(lib, "Janus", "GoABI.olean"), []byte("goabi"))
	writeBytes(t, filepath.Join(lib, "Janus", "GoABI.ilean"), []byte("not module data"))
	writeBytes(t, filepath.Join(lib, "Janus", "GoABI.trace"), []byte("{}"))
	writeBytes(t, filepath.Join(lib, "Janus", "Stray.olean"), []byte("no source"))
	files := map[string][]byte{"Janus.lean": nil, "Janus/GoABI.lean": nil}
	p, err := frameworkPins(lib, files)
	if err != nil {
		t.Fatal(err)
	}
	if len(p.want) != 2 || p.want["Janus/GoABI.olean"] != sha256Hex([]byte("goabi")) {
		t.Fatalf("pins %v", p.want)
	}
	if _, ok := p.want["Janus/Stray.olean"]; ok {
		t.Fatal("a Janus.* olean without a framework source was pinned as framework")
	}
	ps := pinSet{p}
	if err := ps.check("nothing"); err != nil {
		t.Fatal(err)
	}
	// Lake bookkeeping may change; module data may not.
	writeBytes(t, filepath.Join(lib, "Janus", "GoABI.trace"), []byte(`{"changed":1}`))
	if err := ps.check("a trace rewrite"); err != nil {
		t.Fatalf("trace rewrite rejected: %v", err)
	}
	for _, c := range []struct {
		name   string
		mutate func()
		undo   func()
		want   string
	}{
		{"modified", func() { writeBytes(t, filepath.Join(lib, "Janus", "GoABI.olean"), []byte("Ensures := True")) },
			func() { writeBytes(t, filepath.Join(lib, "Janus", "GoABI.olean"), []byte("goabi")) }, "modified Janus/GoABI.olean"},
		{"missing", func() { os.Remove(filepath.Join(lib, "Janus.olean")) },
			func() { writeBytes(t, filepath.Join(lib, "Janus.olean"), []byte("root")) }, "missing Janus.olean"},
		{"server part", func() { writeBytes(t, filepath.Join(lib, "Janus", "GoABI.olean.server"), []byte("x")) },
			func() { os.Remove(filepath.Join(lib, "Janus", "GoABI.olean.server")) }, ""},
	} {
		c.mutate()
		err := ps.check("the step")
		c.undo()
		if c.want == "" {
			// GoABI has a source, so a new part of it is a change to a pinned module.
			if err == nil || !strings.Contains(err.Error(), "unexpected Janus/GoABI.olean.server") {
				t.Errorf("%s: %v", c.name, err)
			}
			continue
		}
		if err == nil || !strings.Contains(err.Error(), c.want) || err.(*diag).Stage != "framework integrity" {
			t.Errorf("%s: %v", c.name, err)
		}
	}
	// All module data of a directory (the trusted Extracted dir, the proof build).
	all, err := newPinnedLib("the build", lib, nil)
	if err != nil {
		t.Fatal(err)
	}
	writeBytes(t, filepath.Join(lib, "Janus", "Backdoor.olean"), []byte("injected"))
	if err := (pinSet{all}).check("the build"); err == nil || !strings.Contains(err.Error(), "unexpected Janus/Backdoor.olean") {
		t.Errorf("injected module: %v", err)
	}
}

func TestClosureCheck(t *testing.T) {
	tcLib, fwLib, trusted, work := t.TempDir(), t.TempDir(), t.TempDir(), t.TempDir()
	writeBytes(t, filepath.Join(tcLib, "Init.olean"), []byte("init"))
	writeBytes(t, filepath.Join(fwLib, "Janus.olean"), []byte("janus"))
	writeBytes(t, filepath.Join(fwLib, "Janus", "GoABI.olean"), []byte("goabi"))
	writeBytes(t, filepath.Join(trusted, "Extracted.olean"), []byte("ex"))
	writeBytes(t, filepath.Join(work, "Proof.olean"), []byte("proof"))
	fw, _ := frameworkPins(fwLib, map[string][]byte{"Janus.lean": nil, "Janus/GoABI.lean": nil})
	dirs := []string{trusted, fwLib, work, tcLib}
	homes := map[string]string{"Extracted": trusted, "Proof": work}
	mods := []string{"Init", "Janus", "Janus.GoABI", "Extracted", "Proof"}
	got, err := closureCheck(mods, dirs, tcLib, fw, homes)
	if err != nil {
		t.Fatal(err)
	}
	if len(got) != 4 || got["Proof"] != filepath.Join(work, "Proof.olean") {
		t.Fatalf("resolved %v", got)
	}
	if _, ok := got["Init"]; ok {
		t.Fatal("a core module is in the replay set")
	}
	for _, c := range []struct {
		name  string
		setup func()
		mods  []string
		want  string
	}{
		{"injected framework module", func() { writeBytes(t, filepath.Join(fwLib, "Janus", "Backdoor.olean"), []byte("b")) },
			[]string{"Janus.Backdoor"}, "not a module of the Janus framework"},
		{"framework module from elsewhere", func() { writeBytes(t, filepath.Join(work, "Janus", "Extra.olean"), []byte("x")) },
			[]string{"Janus.Extra"}, "not by the trusted framework build"},
		{"shadowed core", func() { writeBytes(t, filepath.Join(work, "Init", "Prelude.olean"), []byte("x")) },
			[]string{"Init.Prelude"}, "is shadowed"},
		{"Extracted elsewhere", func() {
			os.Remove(filepath.Join(trusted, "Extracted.olean"))
			writeBytes(t, filepath.Join(fwLib, "Extracted.olean"), []byte("x"))
		},
			[]string{"Extracted"}, "not by its trusted home"},
		{"missing", func() {}, []string{"Nowhere"}, "not on the search path"},
	} {
		c.setup()
		if _, err := closureCheck(c.mods, dirs, tcLib, fw, homes); err == nil || !strings.Contains(err.Error(), c.want) {
			t.Errorf("%s: %v", c.name, err)
		}
	}
}

func TestReplayPlanKeys(t *testing.T) {
	t.Setenv("JANUS_CACHE_DIR", t.TempDir())
	lib := t.TempDir()
	writeBytes(t, filepath.Join(lib, "A.olean"), []byte("a"))
	writeBytes(t, filepath.Join(lib, "B.olean"), []byte("b"))
	writeBytes(t, filepath.Join(lib, "C.olean"), []byte("c"))
	resolved := map[string]string{"A": filepath.Join(lib, "A.olean"), "B": filepath.Join(lib, "B.olean"), "C": filepath.Join(lib, "C.olean")}
	graph := map[string][]string{"A": {"Init"}, "B": {"A", "Init.Core"}, "C": {}}
	p1, err := planReplay(resolved, graph, "v1", true)
	if err != nil {
		t.Fatal(err)
	}
	if len(p1.todo) != 3 || len(p1.cached) != 0 {
		t.Fatalf("todo %v cached %v", p1.todo, p1.cached)
	}
	p1.record([]string{"A", "B", "C"})
	p2, _ := planReplay(resolved, graph, "v1", true)
	if len(p2.cached) != 3 || len(p2.todo) != 0 {
		t.Fatalf("after recording: todo %v cached %v", p2.todo, p2.cached)
	}
	// Changing A changes A's key and B's (which imports A), not C's.
	writeBytes(t, filepath.Join(lib, "A.olean"), []byte("a2"))
	p3, _ := planReplay(resolved, graph, "v1", true)
	if strings.Join(p3.todo, ",") != "A,B" || strings.Join(p3.cached, ",") != "C" {
		t.Fatalf("after changing A: todo %v cached %v", p3.todo, p3.cached)
	}
	// A server part is part of the key.
	writeBytes(t, filepath.Join(lib, "A.olean"), []byte("a"))
	writeBytes(t, filepath.Join(lib, "A.olean.server"), []byte("s"))
	if p4, _ := planReplay(resolved, graph, "v1", true); strings.Join(p4.todo, ",") != "A,B" {
		t.Fatalf("server part ignored: todo %v", p4.todo)
	}
	os.Remove(filepath.Join(lib, "A.olean.server"))
	// Another toolchain, or the cache off, replays everything.
	if p5, _ := planReplay(resolved, graph, "v2", true); len(p5.todo) != 3 {
		t.Fatalf("other toolchain reused %v", p5.cached)
	}
	if p6, _ := planReplay(resolved, graph, "v1", false); len(p6.todo) != 3 {
		t.Fatalf("cache off reused %v", p6.cached)
	}
	// A module without an import record cannot be planned.
	if _, err := planReplay(resolved, map[string][]string{"A": {}, "B": {"A"}}, "v1", true); err == nil {
		t.Fatal("missing import record accepted")
	}
	// Chunked replay through a fake leanchecker: failures are not recorded.
	calls := 0
	ok := func(argv ...string) (string, error) { calls++; return "", nil }
	t.Setenv("JANUS_CACHE_DIR", t.TempDir())
	p7, _ := planReplay(resolved, graph, "v1", true)
	if _, err := p7.replay("leanchecker", func(argv ...string) (string, error) { return "bad", fmt.Errorf("exit 1") }, p7.modules); err == nil {
		t.Fatal("failing replay passed")
	}
	if p8, _ := planReplay(resolved, graph, "v1", true); len(p8.cached) != 0 {
		t.Fatal("a failing replay was cached")
	}
	if _, err := p7.replay("leanchecker", ok, p7.modules); err != nil || calls != 1 {
		t.Fatalf("replay: %v, %d calls", err, calls)
	}
	if p9, _ := planReplay(resolved, graph, "v1", true); len(p9.cached) != 3 {
		t.Fatal("a passing replay was not cached")
	}
}

// TestProtectedOverlay: inside the sandbox a protected tree below a writable directory is
// read-only, and cannot be renamed or removed.
func TestProtectedOverlay(t *testing.T) {
	useTestCache(t)
	var sbs []*sandbox
	if p, err := exec.LookPath("bwrap"); err == nil {
		sbs = append(sbs, &sandbox{mode: "bwrap", bwrap: p})
	}
	if _, err := exec.LookPath("unshare"); err == nil {
		sbs = append(sbs, &sandbox{mode: "unshare"})
	}
	tested := 0
	for _, sb := range sbs {
		if sb.selfTest() != nil {
			continue
		}
		tested++
		t.Logf("checking the %s sandbox", sb.mode)
		base, _ := janusRunBase()
		ws, err := os.MkdirTemp(base, "overlay-")
		if err != nil {
			t.Fatal(err)
		}
		defer os.RemoveAll(ws)
		prot := filepath.Join(ws, "janus")
		writeBytes(t, filepath.Join(prot, "lib", "Janus", "GoABI.olean"), []byte("genuine"))
		script := "echo evil > janus/lib/Janus/GoABI.olean 2>/dev/null && echo WROTE; " +
			"mv janus janus.old 2>/dev/null && echo RENAMED; rm -rf janus 2>/dev/null; " +
			"echo ok > own.txt && echo OWN"
		cmd := sb.commandOverlay(ws, nil, nil, []string{prot}, []string{"/bin/sh", "-c", script}, os.Environ())
		out, _ := cmd.CombinedOutput()
		if strings.Contains(string(out), "WROTE") || strings.Contains(string(out), "RENAMED") || !strings.Contains(string(out), "OWN") {
			t.Errorf("sandbox %s: %s", sb.mode, out)
		}
		if b, _ := os.ReadFile(filepath.Join(prot, "lib", "Janus", "GoABI.olean")); string(b) != "genuine" {
			t.Errorf("sandbox %s: protected file is now %q", sb.mode, b)
		}
	}
	if tested == 0 {
		t.Skip("no sandbox")
	}
}

// r1Package copies audit/attacks/R1_pkg (and with dep, R1_dep) into a new directory, requiring
// janus from the repository checkout, and writes its manifest.
func r1Package(t *testing.T, dep bool) string {
	t.Helper()
	d := filepath.Join(t.TempDir(), "r1")
	copyAttack := func(src, dst string) {
		if err := copyTree(filepath.Join(repoRoot, "audit", "attacks", src), dst); err != nil {
			t.Fatal(err)
		}
	}
	copyAttack("R1_pkg", d)
	req, extra := "", ""
	if dep {
		copyAttack("R1_dep", d+"-dep")
		req = "require r1dep from " + leanString(d+"-dep")
		extra = fmt.Sprintf(`,{"type":"path","scope":"","name":"r1dep","manifestFile":"lake-manifest.json","inherited":false,"dir":%q,"configFile":"lakefile.lean"}`, d+"-dep")
	}
	lf := filepath.Join(d, "lakefile.lean")
	b, _ := os.ReadFile(lf)
	s := strings.Replace(string(b), `"@JANUS@"`, leanString(repoRoot), 1)
	s = strings.Replace(s, "-- @EXTRA_REQUIRE@", req, 1)
	writeFile(t, lf, s)
	writeFile(t, filepath.Join(d, "lake-manifest.json"), fmt.Sprintf(`{"version":"1.2.0","packagesDir":".lake/packages","name":"r1","lakeDir":".lake","fixedToolchain":false,`+
		`"packages":[{"type":"path","scope":"","name":"janus","manifestFile":"lake-manifest.json","inherited":false,"dir":%q,"configFile":"lakefile.toml"}%s]}`, repoRoot, extra))
	return d
}

// TestR1FrameworkTamper: consumer lakefiles and dependency build steps that replace, corrupt
// or add compiled framework modules (audit/attacks/R1_*) are rejected: under the sandbox the
// framework build is read-only (the write fails, so the false theorem does not even compile),
// and without one the framework pins catch the change.
func TestR1FrameworkTamper(t *testing.T) {
	needLean(t)
	useTestCache(t)
	if _, err := exec.LookPath("bwrap"); err != nil {
		t.Skip("bubblewrap not installed")
	}
	add := mustExtract(t, "example.com/basic.Add")
	cases := []struct {
		name, mode, proof, thm string
		dep                    bool
		flags                  []string
		stage, want            string
	}{
		{"ensures", "ensures", "R1/Ensures.lean", "R1.Ensures.claim", false, nil, "proof checking", "Type mismatch"},
		{"ensures unsandboxed", "ensures", "R1/Ensures.lean", "R1.Ensures.claim", false, []string{"--unsafe-no-sandbox"},
			"framework integrity", "modified Janus/GoABI.olean"},
		{"corrupt unsandboxed", "corrupt", "R1/Ensures.lean", "R1.Ensures.claim", false, []string{"--unsafe-no-sandbox"},
			"framework integrity", "modified Janus/GoABI.olean"},
		{"inject unsandboxed", "inject", "R1/Inject.lean", "R1.Inject.claim", false, []string{"--unsafe-no-sandbox"},
			"framework integrity", "unexpected Janus/Backdoor.olean"},
		{"inject via dependency", "", "R1/Plain.lean", "R1.Plain.claim", true, []string{"--allow-path-deps"},
			"module identity", "the dependency r1dep defines the module Janus.Backdoor"},
		{"inject via dependency unsandboxed", "", "R1/Plain.lean", "R1.Plain.claim", true, []string{"--allow-path-deps", "--unsafe-no-sandbox"},
			"framework integrity", "unexpected Janus/Backdoor.olean"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			pkg := r1Package(t, c.dep)
			t.Setenv("JANUS_R1_MODE", c.mode)
			args := append([]string{"verify", add, "--proof", filepath.Join(pkg, c.proof), "--proof-root", pkg, "--theorem", c.thm}, c.flags...)
			code, out, stderr := runJanus(t, args...)
			if code != 1 || out != "" || !strings.HasPrefix(stderr, "Invalid:") || !strings.Contains(stderr, "Stage: "+c.stage) || !strings.Contains(stderr, c.want) {
				t.Fatalf("got %d\n%s\n%s", code, out, stderr)
			}
		})
	}
	// The next verification of an honest proof in a tampered workspace starts from the trusted
	// framework build again (the workspace copy is re-seeded when it differs from the pins).
	pkg := r1Package(t, false)
	t.Setenv("JANUS_R1_MODE", "ensures")
	runJanus(t, "verify", add, "--proof", filepath.Join(pkg, "R1/Plain.lean"), "--proof-root", pkg, "--theorem", "R1.Plain.claim", "--unsafe-no-sandbox")
	t.Setenv("JANUS_R1_MODE", "")
	if code, out, stderr := runJanus(t, "verify", add, "--proof", filepath.Join(pkg, "R1/Plain.lean"), "--proof-root", pkg, "--theorem", "R1.Plain.claim"); code != 0 {
		t.Fatalf("honest proof after a tampered run: %d\n%s\n%s", code, out, stderr)
	}
}

// TestR1ForgedFrameworkLemma: a framework olean (in a --janus-root copy, whose pins are taken
// from that build) carrying a lemma the kernel never checked is caught by the kernel replay of
// the framework module.
func TestR1ForgedFrameworkLemma(t *testing.T) {
	needLean(t)
	useTestCache(t)
	root := filepath.Join(t.TempDir(), "janus")
	for _, f := range []string{"lakefile.toml", "lake-manifest.json", "lean-toolchain", "Janus.lean"} {
		b, err := os.ReadFile(filepath.Join(repoRoot, f))
		if err != nil {
			t.Fatal(err)
		}
		writeBytes(t, filepath.Join(root, f), b)
	}
	if err := copyTree(filepath.Join(repoRoot, "Janus"), filepath.Join(root, "Janus")); err != nil {
		t.Fatal(err)
	}
	if err := copyTree(filepath.Join(repoRoot, ".lake", "build"), filepath.Join(root, ".lake", "build")); err != nil {
		t.Skip("the repository's Janus build is not present (run lake build Janus Janus.Tools.Audit)")
	}
	src, _ := os.ReadFile(filepath.Join(repoRoot, "Janus", "GoABI.lean"))
	forge, _ := os.ReadFile(filepath.Join(repoRoot, "audit", "attacks", "R1_forged_lemma.lean"))
	fdir := filepath.Join(t.TempDir(), "forge")
	writeBytes(t, filepath.Join(fdir, "Janus", "GoABI.lean"), append(append([]byte("import Lean\n"), src...), forge...))
	lake, _ := findLake()
	cmd := exec.Command(lake, "env", "lean", "--root="+fdir, "-o", filepath.Join(root, ".lake", "build", "lib", "lean", "Janus", "GoABI.olean"),
		filepath.Join(fdir, "Janus", "GoABI.lean"))
	cmd.Dir = root
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("forging: %v\n%s", err, out)
	}
	add := mustExtract(t, "example.com/basic.Add")
	code, out, stderr := runJanus(t, "verify", add, "--proof", filepath.Join(repoRoot, "audit", "attacks", "R1_forged_proof.lean"), "--janus-root", root)
	if code != 1 || out != "" || !strings.Contains(stderr, "Stage: kernel replay") || !strings.Contains(stderr, "Janus.GoABI.forged") {
		t.Fatalf("got %d\n%s\n%s", code, out, stderr)
	}
}

func TestReplayTargets(t *testing.T) {
	targets, covers := replayTargets([]string{"Janus.GoABI", "Proof", "Janus", "Janus.Arm64.State", "JanusTrusted", "Extracted", "Proof.Lemmas"})
	if strings.Join(targets, ",") != "Extracted,Janus,JanusTrusted,Proof" {
		t.Fatalf("targets %v", targets)
	}
	if strings.Join(covers["Janus"], ",") != "Janus,Janus.Arm64.State,Janus.GoABI" || strings.Join(covers["Proof"], ",") != "Proof,Proof.Lemmas" {
		t.Fatalf("covers %v", covers)
	}
}
