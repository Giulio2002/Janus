package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// Tests of --full-errors and --keep-workspace (diagflags.go). The fast ones need no Lean; the
// end-to-end ones run janus verify on a deliberately broken proof, a passing proof, and the
// result cache around them.

func TestDiagFlagsOf(t *testing.T) {
	if d := diagFlagsOf(map[string]string{}); d.FullErrors || d.KeepWorkspace || d.errLimit() != 2000 {
		t.Fatalf("default: %+v limit %d", d, d.errLimit())
	}
	d := diagFlagsOf(map[string]string{"full-errors": "true", "keep-workspace": "true"})
	if !d.FullErrors || !d.KeepWorkspace || d.errLimit() <= 1<<40 {
		t.Fatalf("flags: %+v limit %d", d, d.errLimit())
	}
	// takeBoolFlags accepts both on verify and verify-batch
	_, set := takeBoolFlags([]string{"--full-errors", "x", "--keep-workspace"}, diagFlagNames...)
	if !set["full-errors"] || !set["keep-workspace"] {
		t.Fatalf("takeBoolFlags: %v", set)
	}
}

// The per-error cut of the terse summary is 2000 characters; --full-errors lifts it.
func TestSummarizeLimit(t *testing.T) {
	long := "A.lean:1:1: error: unsolved goals\n" + strings.Repeat("h : x = x\n", 600)
	short := summarizeLeanErrors(long, diagFlagsOf(nil).errLimit())
	full := summarizeLeanErrors(long, diagFlagsOf(map[string]string{"full-errors": "1"}).errLimit())
	if !strings.Contains(short, " ...") || strings.Contains(full, " ...") {
		t.Fatalf("terse cut / full cut wrong:\n%.200s\n%.200s", short, full)
	}
	if strings.Count(full, "h : x = x") != 600 {
		t.Fatalf("full summary lost hypotheses: %d", strings.Count(full, "h : x = x"))
	}
}

func TestDiagLog(t *testing.T) {
	if n := diagLogName("Fv256/Arm64/IsZero.lean"); n != "Fv256.Arm64.IsZero.lean.lean-output.log" {
		t.Fatalf("name %q", n)
	}
	dir := t.TempDir()
	p := writeFullOutput(dir, "A/B.lean", "full output\n")
	if p != filepath.Join(dir, diagDirName, "A.B.lean.lean-output.log") {
		t.Fatalf("path %q", p)
	}
	if b, err := os.ReadFile(p); err != nil || string(b) != "full output\n" {
		t.Fatalf("content %q %v", b, err)
	}
	d := withFullOutput(&diag{Next: "Fix."}, p)
	if !strings.Contains(d.Next, "Fix. The complete, untruncated Lean output is in ") || !strings.Contains(d.Next, "lean-output.log") {
		t.Fatalf("next %q", d.Next)
	}
	if d := withFullOutput(&diag{Next: "Fix."}, ""); d.Next != "Fix." {
		t.Fatalf("no path must leave Next alone: %q", d.Next)
	}
}

// The kept single-file workspace is a Lake package with the trusted Extracted module and the proof;
// a rerun replaces it, and a directory janus did not create is never touched.
func TestKeepSingleFileWorkspace(t *testing.T) {
	out, trusted, fw := t.TempDir(), t.TempDir(), t.TempDir()
	writeFile(t, filepath.Join(trusted, "Extracted.lean"), "namespace Extracted\nend Extracted\n")
	writeFile(t, filepath.Join(trusted, "Extracted.olean"), "olean-bytes")
	writeFile(t, filepath.Join(trusted, "Extracted.ilean"), "ilean-bytes")
	writeFile(t, filepath.Join(trusted, "JanusTrusted.olean"), "must not be copied")
	writeFile(t, filepath.Join(fw, "lean-toolchain"), "leanprover/lean4:v4.34.1\n")
	dir, err := keepSingleFileWorkspace(out, fw, trusted, "/x/Proof.lean", []byte("import Extracted\n"))
	if err != nil {
		t.Fatal(err)
	}
	if dir != filepath.Join(out, "workspace") {
		t.Fatalf("dir %q", dir)
	}
	for f, want := range map[string]string{
		".lake/build/lib/lean/Extracted.olean": "olean-bytes",
		".lake/build/lib/lean/Extracted.ilean": "ilean-bytes",
		"Extracted.lean":                       "namespace Extracted\nend Extracted\n",
		"Proof.lean":                           "import Extracted\n",
		"lean-toolchain":                       "leanprover/lean4:v4.34.1\n",
	} {
		if b, err := os.ReadFile(filepath.Join(dir, f)); err != nil || string(b) != want {
			t.Errorf("%s: %q %v", f, b, err)
		}
	}
	if _, err := os.Stat(filepath.Join(dir, ".lake/build/lib/lean/JanusTrusted.olean")); err == nil {
		t.Errorf("JanusTrusted was copied")
	}
	lf, _ := os.ReadFile(filepath.Join(dir, "lakefile.toml"))
	if !strings.Contains(string(lf), "name = \"janus\"") || !strings.Contains(string(lf), fw) || !strings.Contains(string(lf), "[[lean_lib]]") {
		t.Errorf("lakefile:\n%s", lf)
	}
	// a second run replaces it
	writeFile(t, filepath.Join(dir, "stale.txt"), "old")
	if _, err := keepSingleFileWorkspace(out, fw, trusted, "/x/Proof.lean", []byte("import Extracted\n-- v2\n")); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Join(dir, "stale.txt")); err == nil {
		t.Errorf("stale file survived the rerun")
	}
	if b, _ := os.ReadFile(filepath.Join(dir, "Proof.lean")); !strings.Contains(string(b), "v2") {
		t.Errorf("proof not refreshed: %q", b)
	}
	// someone else's directory of that name is refused, not deleted
	other := t.TempDir()
	writeFile(t, filepath.Join(other, "workspace", "mine.txt"), "keep me")
	if _, err := keepSingleFileWorkspace(other, fw, trusted, "/x/Proof.lean", nil); err == nil {
		t.Errorf("replaced a directory janus did not create")
	}
	if _, err := os.Stat(filepath.Join(other, "workspace", "mine.txt")); err != nil {
		t.Errorf("foreign file deleted: %v", err)
	}
	// without a compiled Extracted there is nothing to keep
	if _, err := keepSingleFileWorkspace(t.TempDir(), fw, t.TempDir(), "/x/Proof.lean", nil); err == nil {
		t.Errorf("kept a workspace without Extracted.olean")
	}
}

// Neither flag reaches a result-cache key: the keys hash named fields, never the options map.
func TestDiagFlagsDoNotEnterCacheKeys(t *testing.T) {
	if verifierComponent() == "" {
		t.Skip("no verifier identity")
	}
	tc := &toolchain{lean: "/l/lean", leanchecker: "/l/leanchecker", version: "v"}
	tc.idOnce.Do(func() { tc.id = "fixed-toolchain-id" })
	fw := &framework{Source: "embedded", Sha256: "fwsha"}
	pl := &pinnedLib{want: pins{"Janus": "abc"}}
	sb := &sandbox{mode: "bwrap", bwrap: "/usr/bin/bwrap"}
	outdir := t.TempDir()
	flagged := map[string]string{"full-errors": "true", "keep-workspace": "true"}
	single := func(opts map[string]string) string {
		in := resultInputs{fw: fw, fwPins: pl, auditExeSha: "a", tc: tc, sb: sb, thm: "Proof.correctness", outdir: outdir,
			proof: filepath.Join(outdir, "Proof.lean"), opts: opts, extracted: []byte("e"), identity: []byte("i"),
			binPath: filepath.Join(outdir, "bin"), binarySha: "b", proofSrc: []byte("p")}
		return in.key()
	}
	if a, b := single(nil), single(flagged); a == "" || a != b {
		t.Errorf("single-file key depends on the diagnostic flags: %q vs %q", a, b)
	}
	writeFile(t, filepath.Join(outdir, "identity.json"), "{}")
	pkg := &consumerPkg{Lakefile: "lakefile.toml", Sha256: "pkg",
		Files: map[string][]byte{"lakefile.toml": []byte("name = \"demo\"\n\n[[lean_lib]]\nname = \"Demo\"\n")}}
	req := &consumerRequest{Outdir: outdir, rel: "Demo/Add.lean", proofSrc: []byte("p"),
		cr: &CheckResult{Identity: &Identity{BinarySha256: "b"}, BinPath: filepath.Join(outdir, "bin"), Lean: []byte("e")}}
	cons := func(opts map[string]string) string {
		in := consumerResultInputs{fw: fw, fwPins: pl, auditExeSha: "a", tc: tc, lakeSha: "l", sb: sb, thm: "Demo.Add.correctness", opts: opts, pkg: pkg, req: req}
		return in.key()
	}
	if a, b := cons(nil), cons(flagged); a == "" || a != b {
		t.Errorf("consumer key depends on the diagnostic flags: %q vs %q", a, b)
	}
}

// brokenAddProof is the example Add proof with its last tactic removed: Lean reports the unsolved
// goal, with the machine state's hypotheses.
func brokenAddProof(t *testing.T) string {
	t.Helper()
	b, err := os.ReadFile(filepath.Join(repoRoot, "examples", "proofs", "Add.lean"))
	if err != nil {
		t.Fatal(err)
	}
	s := strings.Replace(string(b), "  janus_run\n", "", 1)
	if s == string(b) {
		t.Fatal("examples/proofs/Add.lean has no `janus_run` line to remove")
	}
	return s
}

var keptLineRE = regexp.MustCompile(`(?m)^Kept workspace: (.+)$`)

// TestFullErrorsSingleFile: the default failure is unchanged and writes nothing; --full-errors shows
// the failing goal with nothing elided, writes the complete output next to the artifact and still
// fails; a proof that compiles is unaffected.
func TestFullErrorsSingleFile(t *testing.T) {
	defer parallel(t)()
	needLean(t)
	if _, err := detectSandbox(false); err != nil {
		t.Skipf("no sandbox available: %v", err)
	}
	add := mustExtract(t, "example.com/basic.Add")
	proof := filepath.Join(t.TempDir(), "Broken.lean")
	writeFile(t, proof, brokenAddProof(t))
	code, out, errb := runJanus(t, "verify", add, "--proof", proof, "--janus-root", repoRoot)
	if code == 0 {
		t.Fatalf("a broken proof verified:\n%s", out)
	}
	if _, err := os.Stat(filepath.Join(add, diagDirName)); err == nil {
		t.Errorf("the default run wrote %s", diagDirName)
	}
	if strings.Contains(errb, "untruncated") {
		t.Errorf("the default failure mentions the full log:\n%s", errb)
	}
	code, out, errb = runJanus(t, "verify", add, "--proof", proof, "--janus-root", repoRoot, "--full-errors")
	if code == 0 {
		t.Fatalf("--full-errors made a broken proof verify:\n%s", out)
	}
	if !strings.Contains(errb, "unsolved goals") || strings.Contains(errb, "⋯") {
		t.Errorf("--full-errors output lacks the goal or still elides terms:\n%s", errb)
	}
	log := filepath.Join(add, diagDirName, "Broken.lean.lean-output.log")
	b, err := os.ReadFile(log)
	if err != nil {
		t.Fatalf("no full log: %v\n%s", err, errb)
	}
	if !strings.Contains(string(b), "unsolved goals") || strings.Contains(string(b), "⋯") || !strings.Contains(errb, "lean-output.log") {
		t.Errorf("full log wrong or not announced:\n%s\n--\n%s", b, errb)
	}
	if _, err := os.Stat(filepath.Join(add, "verified.json")); err == nil {
		t.Errorf("a failed verification left verified.json")
	}
	// --json carries the same untruncated details
	_, jout, _ := runJanus(t, "verify", add, "--proof", proof, "--janus-root", repoRoot, "--full-errors", "--json")
	if !strings.Contains(jout, `"status": "invalid"`) || !strings.Contains(jout, "unsolved goals") {
		t.Errorf("--json failure:\n%s", jout)
	}
}

// TestKeepWorkspaceSingleFile: after a pass AND after a failure there is a workspace in which
// `lake env lean` works against the built Extracted; the flag skips the result-cache read but
// leaves the cache exactly as a run without it (same entries, later hit identical).
func TestKeepWorkspaceSingleFile(t *testing.T) {
	defer parallel(t)()
	needLean(t)
	if _, err := detectSandbox(false); err != nil {
		t.Skipf("no sandbox available: %v", err)
	}
	lake, err := findLake()
	if err != nil {
		t.Skip("lake not installed")
	}
	add := mustExtract(t, "example.com/basic.Add")
	src, err := os.ReadFile(filepath.Join(repoRoot, "examples", "proofs", "Add.lean"))
	if err != nil {
		t.Fatal(err)
	}
	proof := filepath.Join(t.TempDir(), "KeepAdd.lean")
	writeFile(t, proof, string(src)+"\n-- TestKeepWorkspaceSingleFile "+t.Name()+filepath.Base(filepath.Dir(add))+"\n")
	entries := func() map[string]bool {
		m := map[string]bool{}
		_ = filepath.WalkDir(resultCacheDir(), func(p string, d os.DirEntry, err error) error {
			if err == nil && !d.IsDir() && strings.HasSuffix(p, ".json") {
				m[p] = true
			}
			return nil
		})
		return m
	}
	verify := func(extra ...string) (int, string, string) {
		return runJanus(t, append([]string{"verify", add, "--proof", proof, "--janus-root", repoRoot}, extra...)...)
	}
	strip := func(s string) string {
		var keep []string
		for _, l := range strings.Split(s, "\n") {
			if !strings.HasPrefix(l, "  Cached: ") {
				keep = append(keep, l)
			}
		}
		return strings.Join(keep, "\n")
	}
	if code, out, errb := verify(); code != 0 {
		t.Fatalf("first verify: %d\n%s\n%s", code, out, errb)
	}
	if code, out, _ := verify(); code != 0 || !strings.Contains(out, "\n  Cached: ") {
		t.Fatalf("second verify is not a cache hit:\n%s", out)
	}
	before := entries()
	// with the flag: a real run (no "Cached:"), a workspace, the same report
	code, out, errb := verify("--keep-workspace")
	if code != 0 || strings.Contains(out, "\n  Cached: ") {
		t.Fatalf("--keep-workspace run: %d\n%s\n%s", code, out, errb)
	}
	m := keptLineRE.FindStringSubmatch(errb)
	if m == nil {
		t.Fatalf("no 'Kept workspace:' line:\n%s", errb)
	}
	ws := m[1]
	if ws != filepath.Join(add, "workspace") {
		t.Errorf("workspace %q", ws)
	}
	after := entries()
	if len(after) != len(before) {
		t.Errorf("--keep-workspace changed the result cache: %d entries before, %d after", len(before), len(after))
	}
	for e := range before {
		if !after[e] {
			t.Errorf("entry %s vanished", e)
		}
	}
	_, hit, _ := verify()
	if !strings.Contains(hit, "\n  Cached: ") || strip(hit) != strip(out) {
		t.Errorf("a later plain run no longer hits the cache with the same report:\n%s\nvs\n%s", hit, out)
	}
	// `lake env lean` works in the kept workspace, against the built Extracted
	scratch := filepath.Join(ws, "Scratch.lean")
	writeFile(t, scratch, "import Extracted\nimport Janus\n#check Extracted.program\n#check Extracted.entry\n")
	cmd := exec.Command(lake, "env", "lean", "Scratch.lean")
	cmd.Dir = ws
	o, err := cmd.CombinedOutput()
	if err != nil || !strings.Contains(string(o), "Extracted.program") {
		t.Fatalf("lake env lean in the kept workspace: %v\n%s", err, o)
	}
	// the kept Proof.lean is the proof, and it compiles there too (a probe, not evidence)
	cmd = exec.Command(lake, "env", "lean", "Proof.lean")
	cmd.Dir = ws
	if o, err := cmd.CombinedOutput(); err != nil {
		t.Errorf("lake env lean Proof.lean in the kept workspace: %v\n%s", err, o)
	}
	// a failing proof also leaves a workspace
	broken := filepath.Join(t.TempDir(), "Broken.lean")
	writeFile(t, broken, brokenAddProof(t))
	code, _, errb = runJanus(t, "verify", add, "--proof", broken, "--janus-root", repoRoot, "--keep-workspace")
	if code == 0 || keptLineRE.FindStringSubmatch(errb) == nil {
		t.Fatalf("failed run: code %d, no kept workspace:\n%s", code, errb)
	}
	if b, _ := os.ReadFile(filepath.Join(ws, "Proof.lean")); !strings.Contains(string(b), "Add") || strings.Contains(string(b), "TestKeep") {
		t.Errorf("the failing proof is not in the kept workspace:\n%.300s", b)
	}
	if len(entries()) != len(before) {
		t.Errorf("a failing --keep-workspace run changed the result cache")
	}
}

// TestDiagFlagsConsumer: --proof-root. A broken module fails with the untruncated goals and a log;
// a passing one with --keep-workspace prints the consumer workspace, in which `lake env lean`
// runs against the built Extracted. The flags do not change the report.
func TestDiagFlagsConsumer(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	lake, err := findLake()
	if err != nil {
		t.Skip("lake not installed")
	}
	pkg := consumerCopy(t, "toml")
	add := mustExtract(t, "example.com/basic.Add")
	rel := "ConsumerExample/Add.lean"
	good, err := os.ReadFile(filepath.Join(pkg, rel))
	if err != nil {
		t.Fatal(err)
	}
	verify := func(extra ...string) (int, string, string) {
		return runJanus(t, append([]string{"verify", add, "--proof", filepath.Join(pkg, rel), "--proof-root", pkg,
			"--theorem", "ConsumerExample.Add.correctness"}, extra...)...)
	}
	bad := strings.Replace(string(good), "  janus_run [addSpec]\n", "", 1)
	if bad == string(good) {
		t.Fatal("no janus_run line in the consumer example")
	}
	writeFile(t, filepath.Join(pkg, rel), bad)
	code, _, errb := verify("--full-errors")
	if code == 0 || !strings.Contains(errb, "unsolved goals") || strings.Contains(errb, "⋯") {
		t.Fatalf("--full-errors on a broken module: %d\n%s", code, errb)
	}
	log := filepath.Join(add, diagDirName, "ConsumerExample.Add.lean.lean-output.log")
	if b, err := os.ReadFile(log); err != nil || !strings.Contains(string(b), "unsolved goals") || strings.Contains(string(b), "⋯") {
		t.Fatalf("full log: %v\n%s", err, b)
	}
	if !strings.Contains(errb, "lean-output.log") {
		t.Errorf("the failure does not name the log:\n%s", errb)
	}
	// the default failure is the terse one
	code, _, errb = verify()
	if code == 0 || strings.Contains(errb, "untruncated") {
		t.Fatalf("default failure: %d\n%s", code, errb)
	}
	// the honest proof, with and without the flag: same report apart from the workspace-dependent parts
	writeFile(t, filepath.Join(pkg, rel), string(good))
	code, plainOut, errb := verify("--no-result-cache")
	if code != 0 {
		t.Fatalf("plain verify: %d\n%s\n%s", code, plainOut, errb)
	}
	code, keptOut, errb := verify("--keep-workspace")
	if code != 0 {
		t.Fatalf("--keep-workspace verify: %d\n%s\n%s", code, keptOut, errb)
	}
	body := func(s string) string {
		var keep []string
		for _, l := range strings.Split(s, "\n") {
			// what differs between runs of the same verification: which modules were rebuilt, and how many
			// replays came from the replay cache
			if !strings.HasPrefix(l, "  Build: ") && !strings.HasPrefix(l, "  Cached: ") && !strings.HasPrefix(l, "  Kernel replay: ") {
				keep = append(keep, l)
			}
		}
		return strings.Join(keep, "\n")
	}
	if body(plainOut) != body(keptOut) {
		t.Errorf("--keep-workspace changed the report:\n%s\nvs\n%s", plainOut, keptOut)
	}
	for _, o := range []string{plainOut, keptOut} {
		if !strings.Contains(o, "\n  Kernel replay: leanchecker passed (") {
			t.Errorf("no passed kernel replay:\n%s", o)
		}
	}
	m := keptLineRE.FindStringSubmatch(errb)
	if m == nil {
		t.Fatalf("no 'Kept workspace:' line:\n%s", errb)
	}
	ws := m[1]
	if _, err := os.Stat(filepath.Join(ws, "janus", ".lake", "build", "lib", "lean", "Extracted.olean")); err != nil {
		t.Fatalf("no built Extracted in the kept workspace: %v", err)
	}
	root := filepath.Join(ws, "root")
	writeFile(t, filepath.Join(root, "Scratch.lean"), "import Extracted\nimport ConsumerExample.Spec\n#check Extracted.program\n#check ConsumerExample.addSpec\n")
	cmd := exec.Command(lake, "env", "lean", "Scratch.lean")
	cmd.Dir = root
	o, err := cmd.CombinedOutput()
	if err != nil || !strings.Contains(string(o), "Extracted.program") {
		t.Fatalf("lake env lean in the kept consumer workspace: %v\n%s", err, o)
	}
	// the scratch file is not part of the package snapshot of the next verification (the
	// workspace is re-synced from the snapshot, not read back)
	if code, out, errb := verify("--no-result-cache"); code != 0 {
		t.Fatalf("verify after probing the workspace: %d\n%s\n%s", code, out, errb)
	}
	if _, err := os.Stat(filepath.Join(root, "Scratch.lean")); err == nil {
		t.Logf("Scratch.lean still in the workspace (harmless: not part of the snapshot)")
	}
}
