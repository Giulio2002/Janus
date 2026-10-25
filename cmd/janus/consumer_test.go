package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"sort"
	"strings"
	"testing"
)

// Tests for consumer packages, verify-batch, init, explain, framework and --json. Those that
// run Lean are skipped with -short. They share a support cache under the system temp
// directory (JANUS_CACHE_DIR), so the framework is built once across test runs.

func useTestCache(t *testing.T) {
	t.Helper()
	// TestMain sets both for the whole process; only a test that changed them sets them again
	// (t.Setenv, which also rules out t.Parallel for that test).
	if os.Getenv("JANUS_CACHE_DIR") != testCacheDir() {
		t.Setenv("JANUS_CACHE_DIR", testCacheDir())
	}
	if os.Getenv("JANUS_ROOT") != "" {
		t.Setenv("JANUS_ROOT", "")
	}
}

// needLean: the test runs janus verify on single proof files (a few seconds each once the
// framework is built). These run with -short too, so -short still checks the verifier end to end:
// the honest proofs, the axiom/kernel/statement rejections and the hardening attacks.
func needLean(t *testing.T) {
	t.Helper()
	if _, err := findLake(); err != nil {
		t.Skip("lake not installed")
	}
}

// needLeanSlow: the test builds consumer packages or dependencies with Lake, copies or rebuilds
// a framework, or runs many janus processes (tens of seconds to minutes); -short skips it.
func needLeanSlow(t *testing.T) {
	t.Helper()
	if testing.Short() {
		t.Skip("runs Lake builds (skipped with -short)")
	}
	needLean(t)
}

func writeFile(t *testing.T, p, body string) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(p, []byte(body), 0o644); err != nil {
		t.Fatal(err)
	}
}

func pathManifest(name, dir string) string {
	b, _ := json.MarshalIndent(map[string]any{
		"version": "1.2.0", "packagesDir": ".lake/packages", "name": name, "lakeDir": ".lake", "fixedToolchain": false,
		"packages": []map[string]any{{"type": "path", "scope": "", "name": "janus", "manifestFile": "lake-manifest.json",
			"inherited": false, "dir": dir, "configFile": "lakefile.toml"}},
	}, "", " ")
	return string(b)
}

// consumerCopy copies examples/consumer into a new directory, requiring janus from the
// repository checkout by absolute path, with lakefile.toml or (kind "lean") lakefile.lean.
func consumerCopy(t *testing.T, kind string) string {
	t.Helper()
	return consumerCopyAt(t, kind, repoRoot, filepath.Join(t.TempDir(), "consumer"))
}

// consumerCopyAt is consumerCopy into dst (replacing its sources), requiring janus from janusDir.
func consumerCopyAt(t *testing.T, kind, janusDir, dst string) string {
	t.Helper()
	src := filepath.Join(repoRoot, "examples", "consumer")
	for _, f := range []string{"ConsumerExample.lean", "ConsumerExample/Spec.lean", "ConsumerExample/Add.lean", "ConsumerExample/Max.lean", "lean-toolchain"} {
		b, err := os.ReadFile(filepath.Join(src, f))
		if err != nil {
			t.Fatal(err)
		}
		writeFile(t, filepath.Join(dst, f), string(b))
	}
	if kind == "lean" {
		writeFile(t, filepath.Join(dst, "lakefile.lean"), fmt.Sprintf(`import Lake
open Lake DSL

package consumerExample

require janus from %s

@[default_target]
lean_lib ConsumerExample
`, leanString(janusDir)))
	} else {
		writeFile(t, filepath.Join(dst, "lakefile.toml"), fmt.Sprintf(`name = "consumerExample"
defaultTargets = ["ConsumerExample"]

[[require]]
name = "janus"
path = %s

[[lean_lib]]
name = "ConsumerExample"
`, tomlString(janusDir)))
	}
	writeFile(t, filepath.Join(dst, "lake-manifest.json"), pathManifest("consumerExample", janusDir))
	return dst
}

func readReport(t *testing.T, outdir string) *verifiedReport {
	t.Helper()
	b, err := os.ReadFile(filepath.Join(outdir, "verified.json"))
	if err != nil {
		t.Fatalf("verified.json: %v", err)
	}
	var r verifiedReport
	if err := json.Unmarshal(b, &r); err != nil {
		t.Fatal(err)
	}
	return &r
}

func TestTakeBoolFlags(t *testing.T) {
	rest, set := takeBoolFlags([]string{"a", "--json", "--proof", "x", "--fresh", "--", "--json"}, "json", "fresh")
	if !reflect.DeepEqual(rest, []string{"a", "--proof", "x", "--", "--json"}) || !set["json"] || !set["fresh"] {
		t.Fatalf("got %v %v", rest, set)
	}
}

// The embedded framework is exactly the Lean library of this checkout.
func TestEmbeddedFramework(t *testing.T) {
	t.Setenv("JANUS_ROOT", "")
	fw, err := loadFramework("")
	if err != nil {
		t.Fatal(err)
	}
	disk, err := loadFramework(repoRoot)
	if err != nil {
		t.Fatal(err)
	}
	if fw.Source != "embedded" || disk.Source != "directory" {
		t.Fatalf("sources %s %s", fw.Source, disk.Source)
	}
	if fw.Sha256 != disk.Sha256 || len(fw.Files) != len(disk.Files) {
		t.Fatalf("embedded framework %s (%d files) differs from the checkout %s (%d files); rebuild the test binary",
			fw.Sha256, len(fw.Files), disk.Sha256, len(disk.Files))
	}
	for _, p := range []string{"Janus.lean", "Janus/Program.lean", "Janus/Tactic.lean", "lakefile.toml", "lean-toolchain"} {
		if _, ok := fw.Files[p]; !ok {
			t.Errorf("embedded framework lacks %s", p)
		}
	}
	if fw.Toolchain == "" || !strings.HasPrefix(fw.Toolchain, "leanprover/lean4:") {
		t.Errorf("toolchain %q", fw.Toolchain)
	}
	code, out, stderr := runJanus(t, "framework", "--json")
	if code != 0 || !strings.Contains(out, fw.Sha256) || !strings.Contains(out, `"source": "embedded"`) {
		t.Fatalf("framework --json: %d %s %s", code, out, stderr)
	}
}

func copyFramework(t *testing.T, fw *framework) string {
	t.Helper()
	dir := filepath.Join(t.TempDir(), "janus")
	for p, b := range fw.Files {
		writeFile(t, filepath.Join(dir, filepath.FromSlash(p)), string(b))
	}
	return dir
}

func TestCompareFramework(t *testing.T) {
	t.Setenv("JANUS_ROOT", "")
	fw, err := loadFramework("")
	if err != nil {
		t.Fatal(err)
	}
	dir := copyFramework(t, fw)
	if err := compareFramework(dir, fw); err != nil {
		t.Fatalf("identical copy rejected: %v", err)
	}
	prog := filepath.Join(dir, "Janus", "Program.lean")
	orig, _ := os.ReadFile(prog)
	os.WriteFile(prog, bytes.ReplaceAll(orig, []byte("\n"), []byte("\r\n")), 0o644)
	if err := compareFramework(dir, fw); err != nil {
		t.Fatalf("CRLF copy rejected: %v", err)
	}
	expect := func(want string) {
		t.Helper()
		err := compareFramework(dir, fw)
		d, ok := err.(*diag)
		if !ok || !d.Invalid || d.Stage != "framework identity" || !strings.Contains(d.Msg, want) || d.Next == "" {
			t.Fatalf("want %q, got %v", want, err)
		}
	}
	os.WriteFile(prog, append(orig, []byte("\ntheorem extra : True := trivial\n")...), 0o644)
	expect("differs Janus/Program.lean")
	os.WriteFile(prog, orig, 0o644)
	writeFile(t, filepath.Join(dir, "Janus", "Extra.lean"), "def x := 1\n")
	expect("extra Janus/Extra.lean")
	os.Remove(filepath.Join(dir, "Janus", "Extra.lean"))
	os.Remove(filepath.Join(dir, "Janus", "Run.lean"))
	expect("missing Janus/Run.lean")
}

// Package validation that fails before any Lean runs.
func TestLoadConsumerRejects(t *testing.T) {
	t.Setenv("JANUS_ROOT", "")
	fw, err := loadFramework("")
	if err != nil {
		t.Fatal(err)
	}
	janusDir := copyFramework(t, fw)
	rev := strings.Repeat("ab", 20)
	gitManifest := func(inputRev string) string {
		return fmt.Sprintf(`{"version": "1.2.0", "packagesDir": ".lake/packages", "name": "c", "lakeDir": ".lake",
 "packages": [{"url": "https://github.com/Giulio2002/Janus", "type": "git", "subDir": null, "scope": "", "rev": %q,
   "name": "janus", "manifestFile": "lake-manifest.json", "inputRev": %q, "inherited": false, "configFile": "lakefile.toml"}]}`, rev, inputRev)
	}
	good := map[string]string{
		"lakefile.toml":      "name = \"c\"\n[[require]]\nname = \"janus\"\npath = \"" + filepath.ToSlash(janusDir) + "\"\n[[lean_lib]]\nname = \"C\"\n",
		"lean-toolchain":     fw.Toolchain + "\n",
		"lake-manifest.json": pathManifest("c", janusDir),
		"C/A.lean":           "import Extracted\n",
	}
	cases := []struct {
		name   string
		edit   func(m map[string]string)
		stage  string
		want   string
		before func(t *testing.T, root string)
	}{
		{"no lakefile", func(m map[string]string) { delete(m, "lakefile.toml") }, "consumer package", "no lakefile.toml or lakefile.lean", nil},
		{"two lakefiles", func(m map[string]string) { m["lakefile.lean"] = "import Lake\n" }, "consumer package", "both lakefile.toml and lakefile.lean", nil},
		{"no toolchain", func(m map[string]string) { delete(m, "lean-toolchain") }, "toolchain", "no lean-toolchain", nil},
		{"wrong toolchain", func(m map[string]string) { m["lean-toolchain"] = "leanprover/lean4:v4.0.0\n" }, "toolchain", "uses toolchain leanprover/lean4:v4.0.0", nil},
		{"unresolved", func(m map[string]string) { delete(m, "lake-manifest.json") }, "consumer manifest", "not resolved", nil},
		{"no janus", func(m map[string]string) {
			m["lake-manifest.json"] = `{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [], "name": "c"}`
		}, "consumer manifest", "does not list janus", nil},
		{"other path dependency", func(m map[string]string) {
			m["lake-manifest.json"] = manifestWith("c", janusDir, map[string]any{"type": "path", "scope": "", "name": "mathlib",
				"manifestFile": "lake-manifest.json", "inherited": false, "dir": janusDir, "configFile": "lakefile.toml"})
		}, "consumer manifest", "only janus may be a path dependency", nil},
		{"branch pin", func(m map[string]string) { m["lake-manifest.json"] = gitManifest("main") }, "consumer manifest", "not pinned to a full revision", nil},
		{"git not checked out", func(m map[string]string) { m["lake-manifest.json"] = gitManifest(rev) }, "consumer manifest", "not checked out", nil},
		{"different framework", func(m map[string]string) {}, "framework identity", "differs Janus/Run.lean", func(t *testing.T, root string) {
			p := filepath.Join(janusDir, "Janus", "Run.lean")
			b, _ := os.ReadFile(p)
			os.WriteFile(p, append(b, '\n', '-', '-', '\n'), 0o644)
			t.Cleanup(func() { os.WriteFile(p, b, 0o644) })
		}},
		{"reserved Extracted", func(m map[string]string) { m["Extracted.lean"] = "import Janus\n" }, "consumer package", "reserved", nil},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			files := map[string]string{}
			for k, v := range good {
				files[k] = v
			}
			c.edit(files)
			root := t.TempDir()
			for k, v := range files {
				writeFile(t, filepath.Join(root, k), v)
			}
			if c.before != nil {
				c.before(t, root)
			}
			_, err := loadConsumer(root, fw, nil, loadOpts{})
			d, ok := err.(*diag)
			if !ok || !d.Invalid || d.Stage != c.stage || !strings.Contains(d.Msg, c.want) || d.Next == "" {
				t.Fatalf("want stage %q and %q, got %#v", c.stage, c.want, err)
			}
		})
	}
	t.Run("accepted snapshot", func(t *testing.T) {
		root := t.TempDir()
		for k, v := range good {
			writeFile(t, filepath.Join(root, k), v)
		}
		writeFile(t, filepath.Join(root, ".lake", "build", "x.lean"), "")
		writeFile(t, filepath.Join(root, "artifacts", "Add", "Extracted.lean"), "")
		writeFile(t, filepath.Join(root, "notes.txt"), "")
		pkg, err := loadConsumer(root, fw, nil, loadOpts{})
		if err != nil {
			t.Fatal(err)
		}
		var got []string
		for p := range pkg.Files {
			got = append(got, p)
		}
		sort.Strings(got)
		if want := []string{"C/A.lean", "lake-manifest.json", "lakefile.toml", "lean-toolchain"}; !reflect.DeepEqual(got, want) {
			t.Fatalf("snapshot %v, want %v", got, want)
		}
		if _, err := pkg.proofRel(filepath.Join(root, "C", "A.lean")); err != nil {
			t.Fatal(err)
		}
		if _, err := pkg.proofRel(filepath.Join(root, "artifacts", "Add", "Extracted.lean")); err == nil {
			t.Fatal("a file in artifacts/ accepted as proof")
		}
		if _, err := pkg.proofRel(filepath.Join(t.TempDir(), "X.lean")); err == nil {
			t.Fatal("a proof outside the package accepted")
		}
	})
}

func TestVerifyJSONFailure(t *testing.T) {
	code, out, stderr := runJanus(t, "verify", filepath.Join(t.TempDir(), "missing"), "--json")
	var f failureJSON
	if code != 1 || json.Unmarshal([]byte(out), &f) != nil || f.Status != "invalid" || f.Stage != "artifact layout" ||
		!strings.Contains(stderr, "Invalid:") {
		t.Fatalf("got %d %q %q", code, out, stderr)
	}
	code, out, _ = runJanus(t, "verify", "--json")
	if code != 1 || json.Unmarshal([]byte(out), &f) != nil || f.Status != "error" || f.Stage != "command line" {
		t.Fatalf("usage error: %d %q", code, out)
	}
}

func TestInitScaffold(t *testing.T) {
	t.Setenv("JANUS_ROOT", "")
	rev := strings.Repeat("0123456789", 4)
	dir := filepath.Join(t.TempDir(), "my-proofs")
	code, out, stderr := runJanus(t, "init", dir, "--rev", rev, "--no-update")
	if code != 0 || !strings.Contains(out, "library MyProofs") {
		t.Fatalf("init: %d %s %s", code, out, stderr)
	}
	lf, _ := os.ReadFile(filepath.Join(dir, "lakefile.toml"))
	for _, s := range []string{`name = "myProofs"`, `git = "https://github.com/Giulio2002/Janus"`, `rev = "` + rev + `"`, `name = "MyProofs"`} {
		if !strings.Contains(string(lf), s) {
			t.Errorf("lakefile.toml lacks %s:\n%s", s, lf)
		}
	}
	fw, _ := loadFramework("")
	if tc, _ := os.ReadFile(filepath.Join(dir, "lean-toolchain")); strings.TrimSpace(string(tc)) != fw.Toolchain {
		t.Errorf("lean-toolchain %q", tc)
	}
	for _, f := range []string{"MyProofs.lean", "MyProofs/Spec.lean", "MyProofs/Add.lean", "go/main.go", "go/go.mod", "README.md", ".gitignore"} {
		if _, err := os.Stat(filepath.Join(dir, f)); err != nil {
			t.Errorf("missing %s", f)
		}
	}
	if code, _, stderr := runJanus(t, "init", dir, "--rev", rev, "--no-update"); code != 1 || !strings.Contains(stderr, "not empty") {
		t.Fatalf("init into a non-empty directory: %d %s", code, stderr)
	}
	if code, _, stderr := runJanus(t, "init", filepath.Join(t.TempDir(), "x"), "--rev", "main", "--no-update"); code != 1 || !strings.Contains(stderr, "full 40-hex") {
		t.Fatalf("short rev: %d %s", code, stderr)
	}
	if code, _, stderr := runJanus(t, "init", filepath.Join(t.TempDir(), "x"), "--janus-path", t.TempDir(), "--no-update"); code != 1 ||
		!strings.Contains(stderr, "Stage: framework identity") {
		t.Fatalf("janus-path to a non-framework: %d %s", code, stderr)
	}
	if code, _, stderr := runJanus(t, "init", filepath.Join(t.TempDir(), "x"), "--name", "Extracted", "--rev", rev, "--no-update"); code != 1 {
		t.Fatalf("reserved name accepted: %s", stderr)
	}
}

func TestExplain(t *testing.T) {
	dir := mustExtract(t, "example.com/basic.Get")
	id := readIdentity(t, dir)
	lean, _ := os.ReadFile(filepath.Join(dir, "Extracted.lean"))
	idb, _ := os.ReadFile(filepath.Join(dir, "identity.json"))
	proof := filepath.Join(t.TempDir(), "P.lean")
	writeFile(t, proof, "import Extracted\n")
	r := &verifiedReport{Schema: 1, Theorem: "Proof.correctness", Kind: "theorem", Module: "Proof",
		Statement: "Proof.correctness : Extracted.entry = Extracted.entry", Axioms: []string{}, AllowedAxioms: allowedAxioms,
		KernelReplay: kernelReplay{Tool: "leanchecker", Status: "passed", Modules: []string{"Janus", "Extracted", "Proof"}},
		Proof:        binaryRef(dir, proof), ProofSha256: sha256Hex([]byte("import Extracted\n")), Extracted: "Extracted.lean",
		ExtractedSha256: sha256Hex(lean), IdentitySha256: sha256Hex(idb), Binary: id.Binary, BinarySha256: id.BinarySha256,
		Symbol: id.Symbol, Address: id.Address, GoVersion: id.GoVersion, MainModule: id.MainModule, LeanVersion: "Lean (version 4)",
		ExtractorVersion: extractorVersion, Timestamp: "2026-10-23T00:00:00Z",
		Framework: &frameworkInfo{Source: "embedded", Sha256: strings.Repeat("f", 64), Files: 29, Toolchain: "leanprover/lean4:v4.34.1"}}
	if err := writeReport(filepath.Join(dir, "verified.json"), r); err != nil {
		t.Fatal(err)
	}
	code, out, stderr := runJanus(t, "explain", dir)
	if code != 0 {
		t.Fatalf("explain: %s", stderr)
	}
	for _, s := range []string{"theorem Proof.correctness", "Proof.correctness : Extracted.entry = Extracted.entry",
		"Function: example.com/basic.Get, entry address " + id.Address, "for linux/arm64", "runtime.panicBounds (panic)",
		id.BinarySha256 + "  matches", sha256Hex(lean) + "  matches", "Janus framework: embedded"} {
		if !strings.Contains(out, s) {
			t.Errorf("explain output lacks %q:\n%s", s, out)
		}
	}
	os.WriteFile(filepath.Join(dir, "Extracted.lean"), append(lean, '\n'), 0o644)
	_, out, _ = runJanus(t, "explain", filepath.Join(dir, "verified.json"))
	if !strings.Contains(out, sha256Hex(lean)+"  CHANGED") {
		t.Errorf("edited Extracted.lean not flagged:\n%s", out)
	}
	writeFile(t, filepath.Join(dir, "bad.json"), `{"schema": 1}`)
	if code, _, stderr := runJanus(t, "explain", filepath.Join(dir, "bad.json")); code != 1 || !strings.Contains(stderr, "not a janus verification report") {
		t.Fatalf("bad report: %d %s", code, stderr)
	}
}

func TestBatchRequestErrors(t *testing.T) {
	defer parallel(t)()
	if _, err := findLake(); err != nil {
		t.Skip("lake not installed")
	}
	useTestCache(t)
	d := t.TempDir()
	writeFile(t, filepath.Join(d, "bad.json"), `{"schema": 1, "requests": [{"outdir": "a", "prof": "x"}]}`)
	if code, _, stderr := runJanus(t, "verify-batch", filepath.Join(d, "bad.json")); code != 1 || !strings.Contains(stderr, "Stage: batch requests") {
		t.Fatalf("unknown field: %d %s", code, stderr)
	}
	// Every request fails before Lean: a duplicate output, a missing extraction, an
	// unresolved consumer package.
	art := mustExtract(t, "example.com/basic.Add")
	pkg := filepath.Join(d, "pkg")
	writeFile(t, filepath.Join(pkg, "lakefile.toml"), "name = \"p\"\n")
	writeFile(t, filepath.Join(pkg, "lean-toolchain"), "leanprover/lean4:v4.34.1\n")
	writeFile(t, filepath.Join(pkg, "P.lean"), "import Extracted\n")
	reqs := fmt.Sprintf(`{"schema": 1, "proofRoot": "pkg", "requests": [
  {"outdir": %q, "proof": "pkg/P.lean", "theorem": "P.t"},
  {"outdir": %q, "proof": "pkg/P.lean", "theorem": "P.u"},
  {"outdir": "missing", "proof": "pkg/P.lean", "theorem": "P.v"}]}`, art, art)
	writeFile(t, filepath.Join(d, "reqs.json"), reqs)
	results := filepath.Join(d, "results.json")
	code, out, stderr := runJanus(t, "verify-batch", filepath.Join(d, "reqs.json"), "--results", results)
	if code != 1 || !strings.Contains(stderr, "3 of 3 request(s) failed") {
		t.Fatalf("got %d\n%s\n%s", code, out, stderr)
	}
	var res batchResults
	b, _ := os.ReadFile(results)
	if err := json.Unmarshal(b, &res); err != nil {
		t.Fatal(err)
	}
	stages := []string{}
	for _, r := range res.Results {
		if r.Status != "failed" || r.Failure == nil {
			t.Fatalf("result %+v", r)
		}
		stages = append(stages, r.Failure.Stage)
	}
	if want := []string{"consumer manifest", "batch requests", "artifact layout"}; !reflect.DeepEqual(stages, want) {
		t.Fatalf("stages %v, want %v", stages, want)
	}
}

// TestConsumerVerify verifies examples/consumer (lakefile.toml) end to end: shared support
// reused across extractions, an unchanged second run rebuilds nothing, and failures in the
// package are located in its files.
func TestConsumerVerify(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	pkg := consumerCopy(t, "toml")
	add := mustExtract(t, "example.com/basic.Add")
	max := mustExtract(t, "example.com/basic.Max")
	verify := func(outdir, proof, thm string, extra ...string) (int, string, string) {
		return runJanus(t, append([]string{"verify", outdir, "--proof", filepath.Join(pkg, proof), "--proof-root", pkg, "--theorem", thm}, extra...)...)
	}

	code, out, stderr := verify(add, "ConsumerExample/Add.lean", "ConsumerExample.Add.correctness")
	if code != 0 || !strings.HasPrefix(out, "Verified: ConsumerExample.Add.correctness\n") {
		t.Fatalf("Add: %d\n%s\n%s", code, out, stderr)
	}
	r := readReport(t, add)
	if r.Module != "ConsumerExample.Add" || r.Consumer == nil || r.Consumer.Module != "ConsumerExample.Add" ||
		r.Consumer.Lakefile != "lakefile.toml" || r.Consumer.Dependency.Type != "path" || r.Framework == nil ||
		r.Framework.Source != "embedded" || r.KernelReplay.Status != "passed" || len(r.Axioms) == 0 {
		t.Fatalf("report: %+v %+v", r, r.Consumer)
	}
	// The replay covers the whole non-core import closure: every framework module the proof
	// imports, Extracted, JanusTrusted and the consumer modules; never Init/Std/Lean.
	replayedSet := map[string]bool{}
	for _, m := range r.KernelReplay.Modules {
		replayedSet[m] = true
		if isCoreModule(m) {
			t.Errorf("replayed the core module %s", m)
		}
	}
	for _, m := range []string{"Janus", "Janus.GoABI", "Janus.Arm64.Exec", "Janus.Tactic", "Extracted", "JanusTrusted", "ConsumerExample.Add", "ConsumerExample.Spec"} {
		if !replayedSet[m] {
			t.Errorf("replay %v lacks %s", r.KernelReplay.Modules, m)
		}
	}
	if !strings.Contains(strings.Join(r.Consumer.Rebuilt, " "), "ConsumerExample.Spec") {
		t.Errorf("first build of a new package rebuilt %v", r.Consumer.Rebuilt)
	}

	// Another extraction: the shared module comes from the sibling workspace.
	code, out, stderr = verify(max, "ConsumerExample/Max.lean", "ConsumerExample.Max.correctness")
	if code != 0 {
		t.Fatalf("Max: %d\n%s\n%s", code, out, stderr)
	}
	if got := readReport(t, max).Consumer.Rebuilt; !reflect.DeepEqual(got, []string{"ConsumerExample.Max", "Extracted"}) {
		t.Errorf("Max rebuilt %v, want only its own module and Extracted", got)
	}

	// Unchanged inputs: nothing is rebuilt; --json prints the report.
	code, out, stderr = verify(add, "ConsumerExample/Add.lean", "ConsumerExample.Add.correctness", "--json")
	if code != 0 {
		t.Fatalf("Add again: %d %s", code, stderr)
	}
	var jr verifiedReport
	if err := json.Unmarshal([]byte(out), &jr); err != nil || jr.Theorem != "ConsumerExample.Add.correctness" || jr.Consumer == nil {
		t.Fatalf("--json output: %v\n%s", err, out)
	}
	if len(jr.Consumer.Rebuilt) != 0 {
		t.Errorf("second run rebuilt %v", jr.Consumer.Rebuilt)
	}
	if !strings.Contains(" "+strings.Join(jr.KernelReplay.Cached, " ")+" ", " Janus.GoABI ") {
		t.Errorf("second run did not reuse the cached framework replays: cached %v", jr.KernelReplay.Cached)
	}
	if code, out, _ := runJanus(t, "explain", add); code != 0 || !strings.Contains(out, "Consumer package:") || !strings.Contains(out, "module ConsumerExample.Add") {
		t.Errorf("explain: %s", out)
	}

	// A theorem from another module of the package is not the proof's theorem.
	if code, _, stderr := verify(add, "ConsumerExample/Add.lean", "ConsumerExample.addSpec_toNat"); code != 1 ||
		!strings.Contains(stderr, "declared in module ConsumerExample.Spec") || !strings.Contains(stderr, "Stage: theorem audit") {
		t.Fatalf("foreign theorem: %d %s", code, stderr)
	}

	// Failures inside the package.
	writeFile(t, filepath.Join(pkg, "ConsumerExample", "Broken.lean"),
		"import Extracted\nimport ConsumerExample.Spec\nnamespace ConsumerExample.Broken\ntheorem t : Extracted.entry = 0 := rfl\nend ConsumerExample.Broken\n")
	writeFile(t, filepath.Join(pkg, "ConsumerExample", "Cheat.lean"), "import Janus\ntheorem ConsumerExample.cheat : False := sorry\n")
	writeFile(t, filepath.Join(pkg, "ConsumerExample", "UsesCheat.lean"),
		"import Extracted\nimport ConsumerExample.Cheat\ntheorem ConsumerExample.UsesCheat.t : Extracted.entry = 0 := ConsumerExample.cheat.elim\n")
	writeFile(t, filepath.Join(pkg, "ConsumerExample", "Evil.lean"), "import Lean\nset_option debug.skipKernelTC true in\n"+
		"run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {\n"+
		"  name := `ConsumerExample.fake, levelParams := [], type := Lean.mkConst ``False, value := Lean.mkConst ``True.intro })\n")
	writeFile(t, filepath.Join(pkg, "ConsumerExample", "UsesEvil.lean"),
		"import Extracted\nimport ConsumerExample.Evil\ntheorem ConsumerExample.UsesEvil.t : Extracted.entry = 0 := ConsumerExample.fake.elim\n")
	rejected := []struct{ proof, thm, want, stage string }{
		{"ConsumerExample/Broken.lean", "ConsumerExample.Broken.t", filepath.Join(pkg, "ConsumerExample", "Broken.lean") + ":4:", "proof checking"},
		{"ConsumerExample/UsesCheat.lean", "ConsumerExample.UsesCheat.t", "disallowed axioms: sorryAx", "axiom audit"},
		{"ConsumerExample/UsesEvil.lean", "ConsumerExample.UsesEvil.t", "Kernel replay rejected", "kernel replay"},
	}
	for _, c := range rejected {
		t.Run(c.thm, func(t *testing.T) {
			os.WriteFile(filepath.Join(add, "verified.json"), []byte("{}"), 0o644)
			code, out, stderr := verify(add, c.proof, c.thm)
			if code != 1 || out != "" || !strings.Contains(stderr, c.want) || !strings.Contains(stderr, "Stage: "+c.stage) {
				t.Fatalf("got %d\n%s\n%s", code, out, stderr)
			}
			if _, err := os.Stat(filepath.Join(add, "verified.json")); err == nil {
				t.Fatal("verified.json survived a failed verification")
			}
		})
	}
}

// TestConsumerLakefileLean: the same package configured with lakefile.lean.
func TestConsumerLakefileLean(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	pkg := consumerCopy(t, "lean")
	max := mustExtract(t, "example.com/basic.Max")
	code, out, stderr := runJanus(t, "verify", max, "--proof", filepath.Join(pkg, "ConsumerExample", "Max.lean"), "--proof-root", pkg,
		"--theorem", "ConsumerExample.Max.result_ge_left")
	if code != 0 || !strings.HasPrefix(out, "Verified: ConsumerExample.Max.result_ge_left\n") {
		t.Fatalf("%d\n%s\n%s", code, out, stderr)
	}
	if r := readReport(t, max); r.Consumer.Lakefile != "lakefile.lean" {
		t.Errorf("lakefile %s", r.Consumer.Lakefile)
	}
}

// TestConsumerGit: janus required from git, pinned to a full revision and resolved with
// lake update; a checkout that differs from the framework is rejected.
func TestConsumerGit(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git not installed")
	}
	fw, err := loadFramework("")
	if err != nil {
		t.Fatal(err)
	}
	repo := copyFramework(t, fw)
	gitc := func(dir string, args ...string) string {
		t.Helper()
		cmd := exec.Command("git", append([]string{"-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"}, args...)...)
		cmd.Dir = dir
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("git %v: %v\n%s", args, err, out)
		}
		return strings.TrimSpace(string(out))
	}
	gitc(repo, "init", "-q")
	gitc(repo, "add", "-A")
	gitc(repo, "commit", "-q", "-m", "framework")
	rev := gitc(repo, "rev-parse", "HEAD")

	pkg := consumerCopy(t, "toml")
	writeFile(t, filepath.Join(pkg, "lakefile.toml"), fmt.Sprintf("name = \"consumerExample\"\n\n[[require]]\nname = \"janus\"\ngit = %s\nrev = %q\n\n[[lean_lib]]\nname = \"ConsumerExample\"\n",
		tomlString("file://"+filepath.ToSlash(repo)), rev))
	os.Remove(filepath.Join(pkg, "lake-manifest.json"))
	lake, _ := findLake()
	cmd := exec.Command(lake, "update")
	cmd.Dir = pkg
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("lake update: %v\n%s", err, out)
	}
	add := mustExtract(t, "example.com/basic.Add")
	args := []string{"verify", add, "--proof", filepath.Join(pkg, "ConsumerExample", "Add.lean"), "--proof-root", pkg, "--theorem", "ConsumerExample.Add.correctness"}
	code, out, stderr := runJanus(t, args...)
	if code != 0 {
		t.Fatalf("%d\n%s\n%s", code, out, stderr)
	}
	if d := readReport(t, add).Consumer.Dependency; d.Type != "git" || d.Rev != rev {
		t.Errorf("dependency %+v", d)
	}
	dep := filepath.Join(pkg, ".lake", "packages", "janus", "Janus", "Program.lean")
	b, err := os.ReadFile(dep)
	if err != nil {
		t.Fatal(err)
	}
	os.WriteFile(dep, append(b, []byte("\n-- local edit\n")...), 0o644)
	if code, _, stderr := runJanus(t, args...); code != 1 || !strings.Contains(stderr, "Stage: framework identity") ||
		!strings.Contains(stderr, "differs Janus/Program.lean") {
		t.Fatalf("edited dependency: %d %s", code, stderr)
	}
}

// TestVerifyBatch: several requests, two extractions, one failing request that fails alone;
// a second run rebuilds nothing.
func TestVerifyBatch(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	pkg := consumerCopy(t, "toml")
	writeFile(t, filepath.Join(pkg, "ConsumerExample", "Broken.lean"),
		"import Extracted\nimport ConsumerExample.Spec\ntheorem ConsumerExample.Broken.t : Extracted.entry = 0 := rfl\n")
	d := t.TempDir()
	outs := map[string]string{}
	for name, sym := range map[string]string{"Add": "Add", "Max": "Max", "MaxBound": "Max", "Broken": "Add"} {
		outs[name] = filepath.Join(d, "artifacts", name)
		if code, _, stderr := runJanus(t, "extract", exampleBin, "example.com/basic."+sym, outs[name]); code != 0 {
			t.Fatal(stderr)
		}
	}
	type req struct {
		Outdir  string `json:"outdir"`
		Proof   string `json:"proof"`
		Theorem string `json:"theorem"`
	}
	write := func(name string, reqs ...req) string {
		b, _ := json.Marshal(map[string]any{"schema": 1, "proofRoot": pkg, "requests": reqs})
		p := filepath.Join(d, name)
		writeFile(t, p, string(b))
		return p
	}
	good := []req{
		{"artifacts/Add", filepath.Join(pkg, "ConsumerExample/Add.lean"), "ConsumerExample.Add.correctness"},
		{"artifacts/Max", filepath.Join(pkg, "ConsumerExample/Max.lean"), "ConsumerExample.Max.correctness"},
		{"artifacts/MaxBound", filepath.Join(pkg, "ConsumerExample/Max.lean"), "ConsumerExample.Max.result_ge_left"},
	}
	all := write("all.json", append(good, req{"artifacts/Broken", filepath.Join(pkg, "ConsumerExample/Broken.lean"), "ConsumerExample.Broken.t"})...)
	results := filepath.Join(d, "results.json")
	code, out, stderr := runJanus(t, "verify-batch", all, "--results", results)
	if code != 1 || strings.Count(out, "PASS ") != 3 || strings.Count(out, "FAIL ") != 1 || !strings.Contains(stderr, "1 of 4 request(s) failed") {
		t.Fatalf("batch: %d\n%s\n%s", code, out, stderr)
	}
	var res batchResults
	b, _ := os.ReadFile(results)
	if err := json.Unmarshal(b, &res); err != nil {
		t.Fatal(err)
	}
	if res.Passed != 3 || res.Failed != 1 || res.Snapshots != 1 || len(res.Groups) != 2 {
		t.Fatalf("results: %+v", res)
	}
	if f := res.Results[3].Failure; f == nil || f.Stage != "proof checking" || !strings.Contains(f.Message, "Broken.lean:3:") {
		t.Fatalf("broken request: %+v", res.Results[3])
	}
	if !reflect.DeepEqual(res.Groups[0].Requests, []int{0, 3}) || !reflect.DeepEqual(res.Groups[1].Requests, []int{1, 2}) {
		t.Errorf("groups %+v", res.Groups)
	}
	for _, name := range []string{"Add", "Max", "MaxBound"} {
		r := readReport(t, outs[name])
		if r.Consumer == nil || r.KernelReplay.Status != "passed" {
			t.Errorf("%s report %+v", name, r)
		}
	}
	if readReport(t, outs["MaxBound"]).Theorem != "ConsumerExample.Max.result_ge_left" {
		t.Error("MaxBound report is not independent")
	}
	if _, err := os.Stat(filepath.Join(outs["Broken"], "verified.json")); err == nil {
		t.Error("failed request has a verified.json")
	}

	code, out, stderr = runJanus(t, "verify-batch", write("good.json", good...), "--json")
	if code != 0 {
		t.Fatalf("second batch: %d\n%s\n%s", code, out, stderr)
	}
	if err := json.Unmarshal([]byte(out), &res); err != nil {
		t.Fatalf("--json: %v\n%s", err, out)
	}
	for _, g := range res.Groups {
		if len(g.Rebuilt) != 0 {
			t.Errorf("second run rebuilt %v", g.Rebuilt)
		}
	}
}

// TestInitEndToEnd: janus init, then the README's first verification.
func TestInitEndToEnd(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	dir := filepath.Join(t.TempDir(), "hello-proofs")
	if code, out, stderr := runJanus(t, "init", dir, "--janus-path", repoRoot); code != 0 || !strings.Contains(out, "Resolved dependencies") {
		t.Fatalf("init: %d %s %s", code, out, stderr)
	}
	bin := filepath.Join(dir, "artifacts", "hello-arm64")
	cmd := exec.Command("go", "build", "-trimpath", "-o", bin, ".")
	cmd.Dir = filepath.Join(dir, "go")
	cmd.Env = append(os.Environ(), "GOOS=linux", "GOARCH=arm64", "CGO_ENABLED=0")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("go build: %v\n%s", err, out)
	}
	art := filepath.Join(dir, "artifacts", "Add")
	if code, _, stderr := runJanus(t, "extract", bin, "main.Add", art); code != 0 {
		t.Fatal(stderr)
	}
	code, out, stderr := runJanus(t, "verify", art, "--proof", filepath.Join(dir, "HelloProofs", "Add.lean"), "--proof-root", dir,
		"--theorem", "HelloProofs.Add.correctness")
	if code != 0 || !strings.HasPrefix(out, "Verified: HelloProofs.Add.correctness\n") {
		t.Fatalf("verify: %d\n%s\n%s", code, out, stderr)
	}
}

// TestInstallOutsideRepo builds janus as a dependency of a module outside the repository
// (as go install does) and verifies from a directory outside it with no JANUS_ROOT: the
// framework comes from the binary.
func TestInstallOutsideRepo(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	mod := t.TempDir()
	writeFile(t, filepath.Join(mod, "go.mod"), fmt.Sprintf("module example.com/install\n\ngo 1.26.0\n\nrequire github.com/Giulio2002/Janus v0.0.0\n\nreplace github.com/Giulio2002/Janus => %s\n", repoRoot))
	writeFile(t, filepath.Join(mod, "tools.go"), "//go:build tools\n\npackage tools\n\nimport _ \"github.com/Giulio2002/Janus/cmd/janus\"\n")
	exe := filepath.Join(t.TempDir(), "janus")
	gocmd := func(args ...string) {
		t.Helper()
		cmd := exec.Command("go", args...)
		cmd.Dir = mod
		cmd.Env = append(os.Environ(), "GOFLAGS=-mod=mod", "GOPROXY=off", "GOWORK=off")
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("go %v: %v\n%s", args, err, out)
		}
	}
	gocmd("mod", "tidy")
	gocmd("build", "-o", exe, "github.com/Giulio2002/Janus/cmd/janus")

	work := t.TempDir()
	proof := filepath.Join(work, "Trivial.lean")
	tb, _ := os.ReadFile(filepath.Join("testdata", "Trivial.lean"))
	writeFile(t, proof, string(tb))
	runExe := func(args ...string) (string, string, error) {
		cmd := exec.Command(exe, args...)
		cmd.Dir = work
		cmd.Env = append(os.Environ(), "JANUS_ROOT=")
		var out, errb bytes.Buffer
		cmd.Stdout, cmd.Stderr = &out, &errb
		err := cmd.Run()
		return out.String(), errb.String(), err
	}
	if out, stderr, err := runExe("framework"); err != nil || !strings.Contains(out, "Janus framework: embedded") {
		t.Fatalf("framework: %v %s %s", err, out, stderr)
	}
	if _, stderr, err := runExe("extract", exampleBin, "example.com/basic.Get", "Get"); err != nil {
		t.Fatal(stderr)
	}
	out, stderr, err := runExe("verify", "Get", "--proof", "Trivial.lean", "--json")
	if err != nil {
		t.Fatalf("verify: %v\n%s\n%s", err, out, stderr)
	}
	var r verifiedReport
	if err := json.Unmarshal([]byte(out), &r); err != nil || r.Framework == nil || r.Framework.Source != "embedded" ||
		r.KernelReplay.Status != "passed" {
		t.Fatalf("report: %v %+v", err, r)
	}
	fw, _ := loadFramework(repoRoot)
	if r.Framework.Sha256 != fw.Sha256 {
		t.Errorf("installed binary carries framework %s, the checkout is %s", r.Framework.Sha256, fw.Sha256)
	}
	if strings.HasPrefix(r.JanusRoot, repoRoot) {
		t.Errorf("verification used the checkout %s", r.JanusRoot)
	}
}

// TestConsumerTwoCheckouts: two janus checkouts of the same framework (two agents' worktrees,
// byte-identical) and consumer packages that require one or the other, sharing one cache. Each
// verification must use a workspace of its own package and janus checkout and record the checkout
// the package resolved: a package that switches checkouts at the same path gets a new workspace,
// never the other checkout's.
func TestConsumerTwoCheckouts(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	fw, err := loadFramework("")
	if err != nil {
		t.Fatal(err)
	}
	x, y := copyFramework(t, fw), copyFramework(t, fw)
	add := mustExtract(t, "example.com/basic.Add")
	verify := func(pkg string) *consumerInfo {
		t.Helper()
		code, _, stderr := runJanus(t, "verify", add, "--proof", filepath.Join(pkg, "ConsumerExample", "Add.lean"), "--proof-root", pkg,
			"--theorem", "ConsumerExample.Add.correctness")
		if code != 0 {
			t.Fatalf("verify %s: %s", pkg, stderr)
		}
		r := readReport(t, add)
		if r.Consumer == nil {
			t.Fatal("no consumer record")
		}
		return r.Consumer
	}
	p := filepath.Join(t.TempDir(), "consumer")
	a := verify(consumerCopyAt(t, "toml", x, p))
	b := verify(consumerCopyAt(t, "toml", y, p)) // the same package path, now requiring the other checkout
	q := verify(consumerCopyAt(t, "toml", x, filepath.Join(t.TempDir(), "consumer")))
	if a.Dependency.Dir != x || b.Dependency.Dir != y || q.Dependency.Dir != x {
		t.Errorf("recorded janus checkouts %s, %s, %s; want %s, %s, %s", a.Dependency.Dir, b.Dependency.Dir, q.Dependency.Dir, x, y, x)
	}
	if a.Workspace == b.Workspace || a.Workspace == q.Workspace || b.Workspace == q.Workspace ||
		filepath.Dir(a.Workspace) == filepath.Dir(b.Workspace) || filepath.Dir(a.Workspace) == filepath.Dir(q.Workspace) {
		t.Errorf("workspaces shared between checkouts or packages: %s, %s, %s", a.Workspace, b.Workspace, q.Workspace)
	}
	// The second package's workspace was not seeded from the first's (another family).
	again := verify(consumerCopyAt(t, "toml", x, p))
	if again.Workspace != a.Workspace {
		t.Errorf("the same package and checkout got another workspace: %s, then %s", a.Workspace, again.Workspace)
	}
}
