package main

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
	"time"
)

// Tests for janus verify --asl (asl.go, docs/design/ASL.md). The unit tests run always. Those that build
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
	// A seed is an acceleration, never an authority: it is used only when its manifest (written by writeASLSeedManifest)
	// names exactly this framework, JanusASL package and toolchain and every file of its .lake hashes as recorded; anything
	// else (no manifest, another key, a changed, missing or extra file) is a MISS and the build starts cold.
	if err := verifyASLSeed(seed, fw, pkg); err != nil {
		t.Logf("JANUS_TEST_ASL_SEED %s rejected (a cold build follows): %v", seed, err)
		return
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

const aslSeedManifest = "janus-seed.json"

type aslSeedDoc struct {
	Key   string            `json:"key"`
	Files map[string]string `json:"files"` // path relative to .lake -> sha256
}

func aslSeedKey(fw *framework, pkg *aslPackage) string {
	h := sha256.Sum256([]byte("janus-asl-seed-v1\n" + fw.Sha256 + "\n" + pkg.Sha256 + "\n" + fw.Toolchain + "\n"))
	return hex.EncodeToString(h[:])
}

func aslSeedFiles(seed string) (map[string]string, error) {
	files := map[string]string{}
	root := filepath.Join(seed, ".lake")
	err := filepath.WalkDir(root, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, _ := filepath.Rel(root, p)
		if rel == aslSeedManifest || rel == "package-overrides.json" {
			return nil
		}
		if d.Type()&fs.ModeSymlink != 0 {
			return fmt.Errorf("symlink %s in the seed", rel)
		}
		if d.IsDir() {
			return nil
		}
		b, err := os.ReadFile(p)
		if err != nil {
			return err
		}
		files[rel] = sha256Hex(b)
		return nil
	})
	return files, err
}

// writeASLSeedManifest records the key and the file hashes of a built JanusASL .lake so that verifyASLSeed can accept it.
func writeASLSeedManifest(seed string, fw *framework, pkg *aslPackage) error {
	files, err := aslSeedFiles(seed)
	if err != nil {
		return err
	}
	b, _ := json.Marshal(aslSeedDoc{Key: aslSeedKey(fw, pkg), Files: files})
	return os.WriteFile(filepath.Join(seed, ".lake", aslSeedManifest), b, 0o644)
}

func verifyASLSeed(seed string, fw *framework, pkg *aslPackage) error {
	b, err := os.ReadFile(filepath.Join(seed, ".lake", aslSeedManifest))
	if err != nil {
		return fmt.Errorf("no seed manifest: %v", err)
	}
	var doc aslSeedDoc
	if err := json.Unmarshal(b, &doc); err != nil {
		return fmt.Errorf("seed manifest unreadable: %v", err)
	}
	if doc.Key != aslSeedKey(fw, pkg) {
		return fmt.Errorf("seed was built for another framework, JanusASL package or toolchain")
	}
	got, err := aslSeedFiles(seed)
	if err != nil {
		return err
	}
	if len(got) != len(doc.Files) {
		return fmt.Errorf("seed has %d files, its manifest lists %d", len(got), len(doc.Files))
	}
	for f, h := range doc.Files {
		if got[f] != h {
			return fmt.Errorf("seed file %s is missing or changed", f)
		}
	}
	return nil
}

// A tampered, mismatched or unattested seed is rejected (never copied into the cache).
func TestASLSeedRejectsTamperedOrMismatched(t *testing.T) {
	fw, err := loadFramework(repoRoot)
	if err != nil {
		t.Fatal(err)
	}
	pkg, err := loadASL(fw)
	if err != nil {
		t.Fatal(err)
	}
	mk := func() string {
		d := t.TempDir()
		writeBytes(t, filepath.Join(d, ".lake", "build", "lib", "ArmASL.olean"), []byte("olean-bytes"))
		writeBytes(t, filepath.Join(d, ".lake", "build", "lib", "ArmASL.hash"), []byte("h"))
		return d
	}
	seed := mk()
	if err := verifyASLSeed(seed, fw, pkg); err == nil {
		t.Fatal("a seed without a manifest was accepted")
	}
	if err := writeASLSeedManifest(seed, fw, pkg); err != nil {
		t.Fatal(err)
	}
	if err := verifyASLSeed(seed, fw, pkg); err != nil {
		t.Fatalf("an honest attested seed was rejected: %v", err)
	}
	f := filepath.Join(seed, ".lake", "build", "lib", "ArmASL.olean")
	writeBytes(t, f, []byte("forged"))
	if verifyASLSeed(seed, fw, pkg) == nil {
		t.Error("a seed with a changed file was accepted")
	}
	writeBytes(t, f, []byte("olean-bytes"))
	writeBytes(t, filepath.Join(seed, ".lake", "build", "lib", "Extra.olean"), []byte("x"))
	if verifyASLSeed(seed, fw, pkg) == nil {
		t.Error("a seed with an extra file was accepted")
	}
	os.Remove(filepath.Join(seed, ".lake", "build", "lib", "Extra.olean"))
	os.Remove(filepath.Join(seed, ".lake", "build", "lib", "ArmASL.hash"))
	if verifyASLSeed(seed, fw, pkg) == nil {
		t.Error("a seed with a missing file was accepted")
	}
	writeBytes(t, filepath.Join(seed, ".lake", "build", "lib", "ArmASL.hash"), []byte("h"))
	if err := verifyASLSeed(seed, fw, pkg); err != nil {
		t.Fatalf("restored seed rejected: %v", err)
	}
	other := *fw
	other.Sha256 = strings.Repeat("0", 64)
	if verifyASLSeed(seed, &other, pkg) == nil {
		t.Error("a seed attested for another framework was accepted")
	}
	otherPkg := *pkg
	otherPkg.Sha256 = strings.Repeat("1", 64)
	if verifyASLSeed(seed, fw, &otherPkg) == nil {
		t.Error("a seed attested for another JanusASL package was accepted")
	}
	if err := os.Symlink("/etc/passwd", filepath.Join(seed, ".lake", "link")); err == nil && verifyASLSeed(seed, fw, pkg) == nil {
		t.Error("a seed holding a symlink was accepted")
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
	for _, p := range []string{"models/asl/JanusASL/Verify.lean", "models/asl/JanusASL/Classify.lean", "models/asl/JanusASL/Proofs/Run.lean", "models/asl/JanusASL/Proofs/Examples.lean"} {
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
	asl, _ := os.ReadFile(filepath.Join(repoRoot, "scripts", "build", "asl.sh"))
	if m := regexp.MustCompile(`SAIL_ARM_REV=([0-9a-f]{40})`).FindSubmatch(asl); m == nil || string(m[1]) != pkg.Version["sail-arm"] {
		t.Errorf("vendor/ArmASL.version sail-arm %q does not match scripts/build/asl.sh", pkg.Version["sail-arm"])
	}
	if !strings.Contains(string(pkg.Files["lakefile.toml"]), `rev = "`+pkg.Version["lean-sail"]+`"`) {
		t.Errorf("vendor/ArmASL.version lean-sail %q does not match models/asl/lakefile.toml", pkg.Version["lean-sail"])
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
// models/asl/JanusASL/Proofs/Examples.lean).
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

// TestASLForgeryRejected (test/redteam/asl): proofs that try to forge the ASL corollary. Each main
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
			code, stdout, stderr, r, _ := aslVerify(t, "example.com/basic.Add", filepath.Join(repoRoot, "test", "redteam", "asl", "attacks", c.file+".lean"), extra...)
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

// A symlinked <cacheDir>/.lake (scripts/build/asl.sh verify once seeded with `cp -a` of a gate tree's models/asl/.lake, itself
// a link into the main checkout) is replaced by a private directory; the link's target and the package override
// written afterwards never touch it.
func TestASLSymlinkedLakeDirIsReplaced(t *testing.T) {
	root := t.TempDir()
	victim := filepath.Join(root, "main-checkout", "models", "asl", ".lake")
	if err := os.MkdirAll(filepath.Join(victim, "build", "lib", "lean"), 0o755); err != nil {
		t.Fatal(err)
	}
	orig := []byte(`{"packages":[],"schemaVersion":"1.2.0","note":"the source tree's override"}`)
	ovr := filepath.Join(victim, "package-overrides.json")
	if err := os.WriteFile(ovr, orig, 0o644); err != nil {
		t.Fatal(err)
	}
	olean := filepath.Join(victim, "build", "lib", "lean", "ArmASL.olean")
	if err := os.WriteFile(olean, []byte("model"), 0o644); err != nil {
		t.Fatal(err)
	}
	dir := filepath.Join(root, "cache", "asl", "abc")
	if err := os.MkdirAll(dir, 0o755); err != nil {
		t.Fatal(err)
	}
	lake := filepath.Join(dir, ".lake")
	if err := os.Symlink(victim, lake); err != nil {
		t.Fatal(err)
	}
	if err := ensurePrivateDir(lake); err != nil {
		t.Fatal(err)
	}
	if fi, err := os.Lstat(lake); err != nil || !fi.IsDir() || fi.Mode()&os.ModeSymlink != 0 {
		t.Fatalf(".lake is not a private directory after ensurePrivateDir: %v %v", fi, err)
	}
	if err := writeFileNoFollow(filepath.Join(lake, "package-overrides.json"), []byte(`{"mine":true}`), 0o644); err != nil {
		t.Fatal(err)
	}
	if got, _ := os.ReadFile(ovr); string(got) != string(orig) {
		t.Fatalf("the symlink target's package-overrides.json changed: %s", got)
	}
	if got, _ := os.ReadFile(olean); string(got) != "model" {
		t.Fatalf("the symlink target's build changed: %s", got)
	}
	if _, err := os.Stat(filepath.Join(lake, "build")); err == nil {
		t.Fatal("the private .lake kept the target's build")
	}
	// a real directory is left alone, with its contents
	if err := ensurePrivateDir(lake); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Join(lake, "package-overrides.json")); err != nil {
		t.Fatal("ensurePrivateDir emptied a real directory")
	}
	// a regular file is an error, not silently replaced
	f := filepath.Join(root, "afile")
	_ = os.WriteFile(f, []byte("x"), 0o644)
	if err := ensurePrivateDir(f); err == nil {
		t.Fatal("ensurePrivateDir accepted a regular file")
	}
}

// writeFileNoFollow replaces a symlink at the destination (a link planted at package-overrides.json would otherwise
// have the override written into its target).
func TestASLWriteFileNoFollow(t *testing.T) {
	root := t.TempDir()
	target := filepath.Join(root, "target")
	if err := os.WriteFile(target, []byte("precious"), 0o644); err != nil {
		t.Fatal(err)
	}
	p := filepath.Join(root, "package-overrides.json")
	if err := os.Symlink(target, p); err != nil {
		t.Fatal(err)
	}
	if err := writeFileNoFollow(p, []byte("override"), 0o644); err != nil {
		t.Fatal(err)
	}
	if got, _ := os.ReadFile(target); string(got) != "precious" {
		t.Fatalf("the link's target was written: %s", got)
	}
	if fi, _ := os.Lstat(p); fi.Mode()&os.ModeSymlink != 0 {
		t.Fatal("the destination is still a symlink")
	}
	if got, _ := os.ReadFile(p); string(got) != "override" {
		t.Fatalf("destination content %q", got)
	}
	// overwriting a regular file works
	if err := writeFileNoFollow(p, []byte("again"), 0o644); err != nil {
		t.Fatal(err)
	}
	if got, _ := os.ReadFile(p); string(got) != "again" {
		t.Fatalf("second write %q", got)
	}
}

// A sibling build whose .lake is a symlink is not a seed.
func TestASLSiblingWithSymlinkedLakeIsNotASeed(t *testing.T) {
	parent := t.TempDir()
	real := filepath.Join(parent, "real")
	linked := filepath.Join(parent, "linked")
	self := filepath.Join(parent, "self")
	for _, d := range []string{real, linked, self} {
		if err := os.MkdirAll(d, 0o755); err != nil {
			t.Fatal(err)
		}
	}
	mk := func(lake string) {
		if err := os.MkdirAll(filepath.Join(lake, "build", "lib", "lean"), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(lake, "build", "lib", "lean", "ArmASL.olean"), []byte("m"), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	mk(filepath.Join(real, ".lake"))
	elsewhere := filepath.Join(t.TempDir(), ".lake")
	mk(elsewhere)
	if err := os.Symlink(elsewhere, filepath.Join(linked, ".lake")); err != nil {
		t.Fatal(err)
	}
	// make "linked" the most recently used: it must still lose
	now := time.Now()
	_ = os.Chtimes(real, now.Add(-time.Hour), now.Add(-time.Hour))
	_ = os.Chtimes(linked, now, now)
	if got := newestASLSibling(self); got != real {
		t.Fatalf("newestASLSibling = %q, want the real build %q", got, real)
	}
}

// A seed from a long-lived build holds modules of an older, longer model split (ArmASL.Part37 and up): they are pruned,
// the current model's modules (and their C objects) and everything outside build/*/ArmASL stay.
func TestASLPruneStaleArmASLModules(t *testing.T) {
	lake := filepath.Join(t.TempDir(), ".lake")
	put := func(rel string) {
		p := filepath.Join(lake, filepath.FromSlash(rel))
		if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(p, []byte(rel), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	keep := []string{"build/lib/lean/ArmASL/Part20.olean", "build/lib/lean/ArmASL/Part20.ilean", "build/ir/ArmASL/Part20.c", "build/ir/ArmASL/Part20.c.o",
		"build/lib/lean/ArmASL/Defs.olean", "build/lib/lean/ArmASL.olean", "build/ir/ArmASL.c", "build/lib/lean/JanusASL/Part37.olean",
		"build/lib/lean/Sail/Part37.olean", "packages/Sail/.lake/build/lib/lean/Sail.olean"}
	stale := []string{"build/lib/lean/ArmASL/Part37.olean", "build/lib/lean/ArmASL/Part37.ilean", "build/lib/lean/ArmASL/Part37.trace",
		"build/ir/ArmASL/Part37.c", "build/ir/ArmASL/Part41.c.o.export", "build/lib/lean/ArmASL/Part46.olean"}
	for _, r := range append(append([]string{}, keep...), stale...) {
		put(r)
	}
	model := map[string][]byte{"ArmASL/Part20.lean": nil, "ArmASL/Defs.lean": nil, "ArmASL.lean": nil, "lakefile.toml": nil}
	n, err := pruneStaleArmASL(lake, model)
	if err != nil {
		t.Fatal(err)
	}
	if n != len(stale) {
		t.Fatalf("pruned %d files, want %d", n, len(stale))
	}
	for _, r := range stale {
		if _, err := os.Lstat(filepath.Join(lake, filepath.FromSlash(r))); err == nil {
			t.Errorf("stale %s survived", r)
		}
	}
	for _, r := range keep {
		if _, err := os.Lstat(filepath.Join(lake, filepath.FromSlash(r))); err != nil {
			t.Errorf("%s was removed: %v", r, err)
		}
	}
	if n, err := pruneStaleArmASL(filepath.Join(t.TempDir(), "none"), model); err != nil || n != 0 {
		t.Fatalf("a missing .lake: n=%d err=%v", n, err)
	}
}
