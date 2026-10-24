package main

import (
	"encoding/json"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// Tests for janus verify --asl (asl.go, docs/ASL.md). The unit tests run always. Those that build
// and use the JanusASL package (the ArmASL model, about an hour on the first run, then cached in
// the test cache) run only with JANUS_TEST_ASL=1; JANUS_TEST_ASL_SEED may name a built JanusASL
// package directory (with its .lake) whose build seeds the test cache (Lake reuses it by content).

func needASL(t *testing.T) {
	t.Helper()
	needLean(t)
	if os.Getenv("JANUS_TEST_ASL") == "" {
		t.Skip("set JANUS_TEST_ASL=1 to build and test the JanusASL package (about an hour on the first run)")
	}
	useTestCache(t)
	if _, err := detectSandbox(false); err != nil {
		t.Skipf("no sandbox available: %v", err)
	}
	seed := os.Getenv("JANUS_TEST_ASL_SEED")
	if seed == "" {
		return
	}
	fw, err := loadFramework(repoRoot)
	if err != nil {
		t.Fatal(err)
	}
	pkg, err := loadASL(fw)
	if err != nil {
		t.Fatal(err)
	}
	// The directory framework (--janus-root repoRoot) and the embedded one (its cached base).
	for _, janusDir := range []string{repoRoot, filepath.Join(cacheRoot(), "v1", "framework", fw.Sha256[:24])} {
		dir := aslCacheDir(fw, pkg, janusDir)
		if _, err := os.Stat(filepath.Join(dir, ".lake")); err == nil {
			continue
		}
		if err := os.MkdirAll(dir, 0o755); err != nil {
			t.Fatal(err)
		}
		if err := copyTree(filepath.Join(seed, ".lake"), filepath.Join(dir, ".lake")); err != nil {
			t.Fatal(err)
		}
		_ = os.Remove(filepath.Join(dir, ".lake", "package-overrides.json"))
	}
}

func TestASLPackage(t *testing.T) {
	fw, err := loadFramework("")
	if err != nil {
		t.Fatal(err)
	}
	pkg, err := loadASL(fw)
	if err != nil {
		t.Fatal(err)
	}
	for _, p := range []string{"JanusASL/Verify.lean", "JanusASL/Classify.lean", "JanusASL/Proofs/Run.lean", "JanusASL/Proofs/Examples.lean"} {
		if _, ok := pkg.Files[p]; !ok {
			t.Errorf("embedded JanusASL lacks %s", p)
		}
	}
	// The embedded copy is the checkout's.
	dirFw, err := loadFramework(repoRoot)
	if err != nil {
		t.Fatal(err)
	}
	dirPkg, err := loadASL(dirFw)
	if err != nil {
		t.Fatal(err)
	}
	if dirPkg.Sha256 != pkg.Sha256 {
		t.Errorf("embedded JanusASL differs from the checkout's (%s vs %s): rebuild janus", pkg.Sha256, dirPkg.Sha256)
	}
	model, err := unpackModel(pkg.Files["vendor/ArmASL.tar.gz"])
	if err != nil || len(model) < 20 {
		t.Fatalf("unpack: %d files, %v", len(model), err)
	}
	// The recorded version pins are the ones the generator and the lakefile use.
	asl, _ := os.ReadFile(filepath.Join(repoRoot, "scripts", "asl.sh"))
	if m := regexp.MustCompile(`SAIL_ARM_REV=([0-9a-f]{40})`).FindSubmatch(asl); m == nil || string(m[1]) != pkg.Version["sail-arm"] {
		t.Errorf("vendor/ArmASL.version sail-arm %q does not match scripts/asl.sh", pkg.Version["sail-arm"])
	}
	if !strings.Contains(string(pkg.Files["lakefile.toml"]), `rev = "`+pkg.Version["lean-sail"]+`"`) {
		t.Errorf("vendor/ArmASL.version lean-sail %q does not match JanusASL/lakefile.toml", pkg.Version["lean-sail"])
	}
	if _, err := unpackModel([]byte("not a tarball")); err == nil {
		t.Error("unpackModel accepted garbage")
	}
}

func TestASLParseCoverage(t *testing.T) {
	m := "janus-asl-x: "
	out := "noise\n" + m + "class addSubShifted 1\n" + m + "class ret 1\n" + m + "uncovered word 0xf9400000 at 0x10 (f): ldrImm, loads and stores\n" + m + "summary 3 1\n"
	c := parseCoverage(out, m)
	if c == nil || c.Words != 3 || len(c.Uncovered) != 1 || c.Classes["ret"] != 1 || c.Classes["addSubShifted"] != 1 {
		t.Fatalf("parseCoverage = %+v", c)
	}
	if parseCoverage("other: summary 3 0\n", m) != nil {
		t.Error("coverage without the marker accepted")
	}
}

func TestASLAssumptions(t *testing.T) {
	a := aslAssumptions("… (h : JanusASL.Proofs.Rel js s) (hc : JanusASL.Proofs.LinuxEL0Config s) …")
	joined := strings.Join(a, "\n")
	for _, want := range []string{"Rel js s:", "LinuxEL0Config s:", "program's own fetch"} {
		if !strings.Contains(joined, want) {
			t.Errorf("assumptions lack %q", want)
		}
	}
	if strings.Contains(joined, "UserMapped m s:") {
		t.Error("UserMapped listed for a statement that does not name it")
	}
}

// aslVerify runs janus verify --asl on a fresh extraction of sym with proof (single file).
func aslVerify(t *testing.T, sym, proof string, extra ...string) (int, string, string, *verifiedReport, string) {
	t.Helper()
	dir := mustExtract(t, sym)
	code, stdout, stderr := runJanus(t, append([]string{"verify", dir, "--proof", proof, "--janus-root", repoRoot, "--asl"}, extra...)...)
	var r *verifiedReport
	if b, err := os.ReadFile(filepath.Join(dir, "verified.json")); err == nil {
		r = &verifiedReport{}
		if err := json.Unmarshal(b, r); err != nil {
			t.Fatal(err)
		}
	}
	return code, stdout, stderr, r, dir
}

// TestASLExamples: --asl derives the ASL corollaries of the shipped Add, Max, Mul64 and Add128
// proofs directly from their artifacts (these replaced the hand-copied programs that were in
// JanusASL/JanusASL/Proofs/Examples.lean).
func TestASLExamples(t *testing.T) {
	needASL(t)
	for name, post := range map[string]string{
		"Add":    "BitVec.toNat (js'.regs 0) = (x.toNat + y.toNat) % 2 ^ 64",
		"Max":    "js'.regs 0 = if y.toNat < x.toNat then x else y",
		"Mul64":  "BitVec.toNat (js'.regs 0) * 2 ^ 64 + BitVec.toNat (js'.regs 1) = x.toNat * y.toNat",
		"Add128": "% 2 ^ 128",
	} {
		t.Run(name, func(t *testing.T) {
			code, stdout, stderr, r, dir := aslVerify(t, "example.com/basic."+name, filepath.Join(repoRoot, "examples", "proofs", name+".lean"))
			if code != 0 || r == nil || r.ASL == nil || r.ASL.Status != "verified" {
				t.Fatalf("verify --asl %s: %d\n%s\n%s", name, code, stdout, stderr)
			}
			a := r.ASL
			if a.Theorem != aslCorollaryName || a.Of != "Proof.correctness" {
				t.Errorf("corollary %q of %q", a.Theorem, a.Of)
			}
			for _, want := range []string{"JanusASL.Proofs.aslRun (Extracted.program.withExit ret) fuel s = JanusASL.Proofs.AslOutcome.returned s'",
				"JanusASL.Proofs.Rel js s", "JanusASL.Proofs.LinuxEL0Config s", "Janus.GoABI.CallSetup (Extracted.program.withExit ret) Extracted.entry", post} {
				if !strings.Contains(a.Statement, want) {
					t.Errorf("statement lacks %q:\n%s", want, a.Statement)
				}
			}
			for _, ax := range a.Axioms {
				if !containsStr(allowedAxioms, ax) {
					t.Errorf("axiom %s", ax)
				}
			}
			if a.KernelReplay == nil || a.KernelReplay.Status != "passed" || !containsStr(a.KernelReplay.Modules, "ArmASL.Part01") ||
				!containsStr(a.KernelReplay.Modules, "JanusASL.Verify") || !containsStr(a.KernelReplay.Modules, aslCorollaryModule) ||
				!containsStr(a.KernelReplay.Modules, aslWordsModule) {
				t.Errorf("kernel replay %+v", a.KernelReplay)
			}
			if a.Coverage == nil || len(a.Coverage.Uncovered) != 0 || a.Coverage.Words == 0 || a.Model.ArmASLSha256 == "" || len(a.Assumptions) < 3 {
				t.Errorf("record %+v", a)
			}
			if r.Theorem != "Proof.correctness" {
				t.Errorf("main theorem %q", r.Theorem)
			}
			code, out, errOut := runJanus(t, "explain", dir)
			if code != 0 || !strings.Contains(out, "ASL corollary") || !strings.Contains(out, "LinuxEL0Config s:") || !strings.Contains(out, post) {
				t.Errorf("explain: %d\n%s%s", code, out, errOut)
			}
		})
	}
}

// TestASLUncovered: a program with words outside the proved subset (Get's load) keeps its main
// verification and fails the ASL stage with the list of words.
func TestASLUncovered(t *testing.T) {
	needASL(t)
	code, stdout, stderr, r, _ := aslVerify(t, "example.com/basic.Get", filepath.Join(repoRoot, "examples", "proofs", "Get.lean"))
	if code != 1 || r == nil || r.Theorem != "Proof.correctness" || r.ASL == nil || r.ASL.Status != "invalid" {
		t.Fatalf("Get --asl: %d %v\n%s\n%s", code, r, stdout, stderr)
	}
	if !strings.Contains(stdout, "Verified: Proof.correctness") || !strings.Contains(stderr, "Invalid: ASL corollary") ||
		!strings.Contains(stderr, "Stage: ASL coverage") || !strings.Contains(stderr, "loads and stores") {
		t.Errorf("Get --asl output:\n%s\n%s", stdout, stderr)
	}
	if r.ASL.Coverage == nil || len(r.ASL.Coverage.Uncovered) == 0 {
		t.Errorf("coverage %+v", r.ASL.Coverage)
	}
}

// TestASLForgeryRejected (audit/asl): proofs that try to forge the ASL corollary. Each main
// theorem verifies; the ASL stage must reject the forgery.
func TestASLForgeryRejected(t *testing.T) {
	needASL(t)
	for _, c := range []struct{ file, theorem, want string }{
		{"X1_shadow_toASL", "", "Stage: ASL corollary"},
		{"X2_own_toASL", "Proof.correctness_asl", "is not `Janus.GoABI.Ensures"},
		{"X3_plant_words", "", "Stage: ASL corollary"},
		{"X4_plant_corollary", "", "Stage: ASL corollary"},
		{"X5_elab_override", "", "ASL corollary"},
		{"X6_other_program", "", "not about Extracted.program itself"},
		{"X7_reserved_name", "", "reserved for JanusASL"},
	} {
		t.Run(c.file, func(t *testing.T) {
			extra := []string{}
			if c.theorem != "" {
				extra = append(extra, "--theorem", c.theorem)
			}
			code, stdout, stderr, r, _ := aslVerify(t, "example.com/basic.Add", filepath.Join(repoRoot, "audit", "asl", "attacks", c.file+".lean"), extra...)
			if code != 1 || r == nil || r.ASL == nil || r.ASL.Status != "invalid" || strings.Contains(stdout, "ASL corollary: Verified") {
				t.Fatalf("%s not rejected: %d\n%s\n%s", c.file, code, stdout, stderr)
			}
			if !strings.Contains(stderr, c.want) {
				t.Errorf("%s: expected %q in\n%s", c.file, c.want, stderr)
			}
		})
	}
}

// TestASLConsumer: --asl for a consumer package module, and a consumer module under a reserved
// JanusASL root is refused.
func TestASLConsumer(t *testing.T) {
	needASL(t)
	pkg := consumerCopy(t, "toml")
	dir := mustExtract(t, "example.com/basic.Add")
	code, stdout, stderr := runJanus(t, "verify", dir, "--proof", filepath.Join(pkg, "ConsumerExample", "Add.lean"),
		"--proof-root", pkg, "--theorem", "ConsumerExample.Add.correctness", "--asl")
	if code != 0 || !strings.Contains(stdout, "ASL corollary: Verified") {
		t.Fatalf("consumer --asl: %d\n%s\n%s", code, stdout, stderr)
	}
	// verify-batch --asl: a consumer request and a single-file one.
	maxDir := mustExtract(t, "example.com/basic.Max")
	man := filepath.Join(t.TempDir(), "requests.json")
	b, _ := json.Marshal(map[string]any{"schema": 1, "requests": []map[string]any{
		{"outdir": dir, "proof": filepath.Join(pkg, "ConsumerExample", "Add.lean"), "theorem": "ConsumerExample.Add.correctness", "proofRoot": pkg},
		{"outdir": maxDir, "proof": filepath.Join(repoRoot, "examples", "proofs", "Max.lean")},
	}})
	writeFile(t, man, string(b))
	code, stdout, stderr = runJanus(t, "verify-batch", man, "--asl", "--json")
	var res batchResults
	if err := json.Unmarshal([]byte(stdout), &res); err != nil || code != 0 || res.Passed != 2 || res.ASLFailed != 0 {
		t.Fatalf("verify-batch --asl: %d %v\n%s\n%s", code, err, stdout, stderr)
	}
	for _, r := range res.Results {
		if r.ASL != "verified" {
			t.Errorf("batch result %d: asl %q", r.Index, r.ASL)
		}
	}
	if rep := readReport(t, maxDir); rep.ASL == nil || rep.ASL.Status != "verified" {
		t.Errorf("Max report: %+v", rep.ASL)
	}
	// A module JanusASL.Fake in the consumer's build.
	writeFile(t, filepath.Join(pkg, "JanusASL", "Fake.lean"), "theorem fakeASL : True := trivial\n")
	lf, _ := os.ReadFile(filepath.Join(pkg, "lakefile.toml"))
	writeFile(t, filepath.Join(pkg, "lakefile.toml"), string(lf)+"\n[[lean_lib]]\nname = \"JanusASL\"\nglobs = [\"JanusASL.*\"]\n")
	writeFile(t, filepath.Join(pkg, "ConsumerExample", "Add.lean"), "import JanusASL.Fake\n"+mustRead(t, filepath.Join(pkg, "ConsumerExample", "Add.lean")))
	code, stdout, stderr = runJanus(t, "verify", dir, "--proof", filepath.Join(pkg, "ConsumerExample", "Add.lean"),
		"--proof-root", pkg, "--theorem", "ConsumerExample.Add.correctness", "--asl")
	if code != 1 || !strings.Contains(stderr, "Stage: ASL module identity") {
		t.Fatalf("consumer JanusASL module not refused: %d\n%s\n%s", code, stdout, stderr)
	}
}

func mustRead(t *testing.T, p string) string {
	t.Helper()
	b, err := os.ReadFile(p)
	if err != nil {
		t.Fatal(err)
	}
	return string(b)
}

// A new JanusASL build directory is seeded from the most recently used built sibling.
func TestASLSibling(t *testing.T) {
	parent := t.TempDir()
	mk := func(name string, built bool) string {
		d := filepath.Join(parent, name)
		if built {
			writeFile(t, filepath.Join(d, ".lake", "build", "lib", "lean", "ArmASL.olean"), "x")
		} else if err := os.MkdirAll(d, 0o755); err != nil {
			t.Fatal(err)
		}
		return d
	}
	old, self := mk("old", true), mk("self", false)
	_ = mk("unbuilt", false)
	if got := newestASLSibling(self); got != old {
		t.Errorf("newestASLSibling = %q, want %q", got, old)
	}
	if got := newestASLSibling(old); got != "" {
		t.Errorf("newestASLSibling(old) = %q, want none", got)
	}
}
