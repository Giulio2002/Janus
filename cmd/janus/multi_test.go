package main

// Tests for several theorems in one `janus verify` run (verify.go, verifyMany; consumer.go,
// verifyConsumerMany): one compile of the proof (file or package), and for EVERY theorem its own
// audit, axiom check, kernel replay, result-cache entry and report. A theorem that fails (false,
// sorry, an extra axiom, a failed audit) fails alone, never another, and a multi-theorem run
// never passes a theorem a single-theorem run would fail.

import (
	"encoding/json"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

// multiProof is a proof file of Get's extraction with one honest theorem per kind of check and
// several that must each fail on their own.
const multiProof = `import Extracted
namespace Proof
theorem correctness : Extracted.entry = Extracted.entry := rfl
theorem segs : Extracted.program.segments.length = 1 := by decide
theorem usesSorry : Extracted.entry = 0 := sorry
axiom cheat : Extracted.entry = 1
theorem usesAxiom : Extracted.entry = 1 := cheat
theorem noExtracted : True := trivial
def aDef : Nat := Extracted.entry
end Proof
`

// keyFields is what a report says about a theorem, minus the run's own metadata.
type keyFields struct {
	Theorem, Kind, Module, Statement, StatementExplicit, ProofSha256, ExtractedSha256, Symbol string
	Axioms, Definitions, Notes                                                                []string
	ReplayStatus                                                                              string
	ReplayModules                                                                             []string
}

func keyOf(r *verifiedReport) keyFields {
	return keyFields{r.Theorem, r.Kind, r.Module, r.Statement, r.StatementExplicit, r.ProofSha256, r.ExtractedSha256, r.Symbol,
		r.Axioms, r.Definitions, r.Notes, r.KernelReplay.Status, r.KernelReplay.Modules}
}

func readJSONReport(t *testing.T, p string) *verifiedReport {
	t.Helper()
	b, err := os.ReadFile(p)
	if err != nil {
		t.Fatalf("%s: %v", p, err)
	}
	var r verifiedReport
	if err := json.Unmarshal(b, &r); err != nil {
		t.Fatal(err)
	}
	return &r
}

func readResults(t *testing.T, p string) map[string]multiJSONItem {
	t.Helper()
	b, err := os.ReadFile(p)
	if err != nil {
		t.Fatalf("results: %v", err)
	}
	var mj multiJSON
	if err := json.Unmarshal(b, &mj); err != nil || mj.Schema != 1 {
		t.Fatalf("results %s: %v", b, err)
	}
	m := map[string]multiJSONItem{}
	for _, it := range mj.Results {
		if _, dup := m[it.Theorem]; dup {
			t.Errorf("results list %s twice", it.Theorem)
		}
		m[it.Theorem] = it
	}
	return m
}

func pathExists(p string) bool { _, err := os.Stat(p); return err == nil }

func TestVerifyManyTheorems(t *testing.T) {
	defer parallel(t)()
	needLean(t)
	proofs := t.TempDir()
	proof := filepath.Join(proofs, "Multi.lean")
	writeFile(t, proof, multiProof)
	dir := mustExtract(t, "example.com/basic.Get")
	results := filepath.Join(t.TempDir(), "results.json")
	thm := func(names ...string) []string {
		a := []string{"verify", dir, "--proof", proof, "--janus-root", repoRoot, "--results", results}
		for _, n := range names {
			a = append(a, "--theorem", "Proof."+n)
		}
		return a
	}

	// One run, seven theorems: two honest, five that must each fail for their own reason.
	code, out, stderr := runJanus(t, thm("correctness", "usesSorry", "segs", "usesAxiom", "noExtracted", "aDef", "missing")...)
	if code != 1 {
		t.Fatalf("exit %d\n%s\n%s", code, out, stderr)
	}
	res := readResults(t, results)
	want := map[string]string{
		"Proof.correctness": "", "Proof.segs": "",
		"Proof.usesSorry":   "disallowed axioms: sorryAx",
		"Proof.usesAxiom":   "disallowed axioms: Proof.cheat",
		"Proof.noExtracted": "does not mention Extracted",
		"Proof.aDef":        "is a definition, not a theorem",
		"Proof.missing":     "does not define Proof.missing",
	}
	if len(res) != len(want) {
		t.Fatalf("results: %+v", res)
	}
	for name, why := range want {
		it, ok := res[name]
		switch {
		case !ok:
			t.Errorf("%s: no result", name)
		case why == "" && (it.Status != "verified" || it.Report == nil || it.Failure != nil):
			t.Errorf("%s should verify: %+v", name, it)
		case why != "" && (it.Status != "failed" || it.Report != nil || it.Failure == nil || !strings.Contains(it.Failure.Message, why)):
			t.Errorf("%s should fail with %q: %+v", name, why, it)
		}
		// A report file exists exactly for the theorems that passed.
		if f := filepath.Join(dir, "verified", name+".json"); pathExists(f) != (why == "") {
			t.Errorf("%s: report file present=%v, want %v", name, pathExists(f), why == "")
		}
	}
	// The text output has one marked block per theorem, in the order given, on stdout.
	if i, j := strings.Index(out, "=== Proof.correctness: verified ==="), strings.Index(out, "=== Proof.segs: verified ==="); i < 0 || j < i {
		t.Errorf("blocks missing or out of order:\n%s", out)
	}
	if !strings.Contains(out, "=== Proof.usesSorry: FAILED ===") || !strings.Contains(out, "Stage: axiom audit") {
		t.Errorf("failure block missing:\n%s", out)
	}
	// verified.json is the first theorem's report (it passed), nobody else's.
	if r := readReport(t, dir); r.Theorem != "Proof.correctness" {
		t.Errorf("verified.json is for %s", r.Theorem)
	}

	// Each report is what a run of that theorem alone says (a separate extraction, so no cache
	// entry can answer).
	for _, name := range []string{"correctness", "segs"} {
		solo := mustExtract(t, "example.com/basic.Get")
		if code, out, stderr := runJanus(t, "verify", solo, "--proof", proof, "--janus-root", repoRoot, "--theorem", "Proof."+name); code != 0 {
			t.Fatalf("solo %s: %d %s %s", name, code, out, stderr)
		}
		got := readJSONReport(t, filepath.Join(dir, "verified", "Proof."+name+".json"))
		if want := readReport(t, solo); !reflect.DeepEqual(keyOf(got), keyOf(want)) {
			t.Errorf("%s: multi report differs from the single run's:\n%+v\n%+v", name, keyOf(got), keyOf(want))
		}
		if len(got.KernelReplay.Modules) == 0 || got.KernelReplay.Status != "passed" {
			t.Errorf("%s: no kernel replay recorded: %+v", name, got.KernelReplay)
		}
	}

	// A withdrawn report stays withdrawn: a run whose theorems all fail leaves none behind.
	if code, _, _ := runJanus(t, thm("usesSorry", "usesAxiom")...); code != 1 || pathExists(filepath.Join(dir, "verified.json")) ||
		pathExists(filepath.Join(dir, "verified", "Proof.correctness.json")) {
		t.Errorf("stale reports survived (exit %d)", code)
	}
	// --json prints the per-theorem results.
	code, out, _ = runJanus(t, append(thm("correctness", "usesSorry"), "--json")...)
	var mj multiJSON
	if code != 1 || json.Unmarshal([]byte(out), &mj) != nil || len(mj.Results) != 2 || mj.Results[0].Status != "verified" || mj.Results[1].Status != "failed" {
		t.Errorf("--json: %d\n%s", code, out)
	}

	// Duplicates are refused before anything runs; a bad name fails alone.
	if code, out, stderr := runJanus(t, thm("correctness", "correctness")...); code != 1 || out != "" || !strings.Contains(stderr, "listed more than once") {
		t.Errorf("duplicate: %d %q %s", code, out, stderr)
	}
	outs := verifyMany(dir, map[string]string{"proof": proof, "janus-root": repoRoot}, []string{"Proof.correctness", "Proof.correctness", "Proof.x y", "Proof.segs"}, os.Stderr)
	if outs[0].Report == nil || outs[3].Report == nil ||
		outs[1].Err == nil || !strings.Contains(outs[1].Err.Error(), "listed more than once") ||
		outs[2].Err == nil || !strings.Contains(outs[2].Err.Error(), "not a plain dotted Lean name") {
		t.Errorf("verifyMany outcomes: %+v", outs)
	}
	// Module-qualified entries belong to --proof-root only.
	if code, _, stderr := runJanus(t, "verify", dir, "--proof", proof, "--janus-root", repoRoot, "--theorem", "X.lean::Proof.correctness"); code != 1 || !strings.Contains(stderr, "needs --proof-root") {
		t.Errorf("qualified without --proof-root: %d %s", code, stderr)
	}
	// A newline cannot smuggle a second theorem into one --theorem value.
	if code, _, stderr := runJanus(t, "verify", dir, "--proof", proof, "--janus-root", repoRoot, "--theorem", "Proof.correctness\nProof.segs"); code != 1 || !strings.Contains(stderr, "newline") {
		t.Errorf("newline: %d %s", code, stderr)
	}
}

// A proof that does not compile fails every theorem asked for (they share the compile), each with
// the compile's diagnostics; no report is written for any.
func TestVerifyManySharedFailure(t *testing.T) {
	defer parallel(t)()
	needLean(t)
	dir := mustExtract(t, "example.com/basic.Get")
	proof := filepath.Join(t.TempDir(), "Broken.lean")
	writeFile(t, proof, "import Extracted\nnamespace Proof\ntheorem correctness : Extracted.entry = 0 := rfl\ntheorem segs : Extracted.program.segments.length = 1 := by decide\nend Proof\n")
	results := filepath.Join(t.TempDir(), "r.json")
	code, _, _ := runJanus(t, "verify", dir, "--proof", proof, "--janus-root", repoRoot, "--results", results,
		"--theorem", "Proof.segs", "--theorem", "Proof.correctness")
	res := readResults(t, results)
	if code != 1 || len(res) != 2 {
		t.Fatalf("exit %d, %+v", code, res)
	}
	for name, it := range res {
		if it.Status != "failed" || it.Failure == nil || it.Failure.Stage != "proof checking" {
			t.Errorf("%s: %+v", name, it)
		}
	}
	if pathExists(filepath.Join(dir, "verified.json")) || pathExists(filepath.Join(dir, "verified")) {
		t.Error("a report was written")
	}
}

// The result cache binds every theorem on its own: an entry recorded for one theorem (or for one
// proof text) never answers for another, and a run that mixes hits with misses reports each as it
// is.
func TestVerifyManyCacheIsolation(t *testing.T) {
	defer parallel(t)()
	needLean(t)
	dir := mustExtract(t, "example.com/basic.Get")
	proof := filepath.Join(t.TempDir(), "Iso.lean")
	writeFile(t, proof, "import Extracted\nnamespace Proof\ntheorem a : Extracted.entry = Extracted.entry := rfl\ntheorem b : Extracted.entry = Extracted.entry := rfl\nend Proof\n")
	run := func(extra ...string) (int, string, string) {
		return runJanus(t, append([]string{"verify", dir, "--proof", proof, "--janus-root", repoRoot}, extra...)...)
	}
	// a alone is recorded...
	if code, out, stderr := run("--theorem", "Proof.a"); code != 0 {
		t.Fatalf("a: %d %s %s", code, out, stderr)
	}
	// ...b is not covered by a's entry: a is a hit, b is verified for real.
	code, out, stderr := run("--theorem", "Proof.a", "--theorem", "Proof.b")
	if code != 0 {
		t.Fatalf("a+b: %d %s %s", code, out, stderr)
	}
	ra, rb := readJSONReport(t, filepath.Join(dir, "verified", "Proof.a.json")), readJSONReport(t, filepath.Join(dir, "verified", "Proof.b.json"))
	if !ra.Cached || rb.Cached || ra.Theorem != "Proof.a" || rb.Theorem != "Proof.b" {
		t.Errorf("cached a=%v b=%v, want true/false (%s, %s)", ra.Cached, rb.Cached, ra.Theorem, rb.Theorem)
	}
	// Both recorded now: a repeat is all hits, and `a` still reports its own statement.
	if code, out, stderr := run("--theorem", "Proof.b", "--theorem", "Proof.a"); code != 0 || !readJSONReport(t, filepath.Join(dir, "verified", "Proof.b.json")).Cached {
		t.Fatalf("repeat: %d %s %s", code, out, stderr)
	}
	// Change the proof text: b is now false (sorry). The recorded passes of b (and a) must not
	// answer: the file's bytes are part of every key.
	writeFile(t, proof, "import Extracted\nnamespace Proof\ntheorem a : Extracted.entry = Extracted.entry := rfl\ntheorem b : Extracted.entry = 0 := sorry\nend Proof\n")
	results := filepath.Join(t.TempDir(), "r.json")
	code, _, _ = run("--theorem", "Proof.a", "--theorem", "Proof.b", "--results", results)
	res := readResults(t, results)
	if code != 1 || res["Proof.a"].Status != "verified" || res["Proof.b"].Status != "failed" ||
		res["Proof.b"].Failure == nil || !strings.Contains(res["Proof.b"].Failure.Message, "sorryAx") {
		t.Fatalf("after the edit: %d %+v", code, res)
	}
	if res["Proof.a"].Report.Cached {
		t.Error("a was answered from an entry recorded for the old proof text")
	}
	// A single run of b agrees.
	if code, _, stderr := run("--theorem", "Proof.b"); code != 1 || !strings.Contains(stderr, "sorryAx") {
		t.Errorf("b alone: %d %s", code, stderr)
	}
	// Mixed hit and failure in one run: a hits (recorded just above), b fails, and b stays failed
	// however often it is asked for.
	for i := 0; i < 2; i++ {
		code, _, _ = run("--theorem", "Proof.b", "--theorem", "Proof.a", "--results", results)
		res = readResults(t, results)
		if code != 1 || res["Proof.a"].Status != "verified" || !res["Proof.a"].Report.Cached || res["Proof.b"].Status != "failed" {
			t.Fatalf("mixed run %d: %d %+v", i, code, res)
		}
	}
	if pathExists(filepath.Join(dir, "verified", "Proof.b.json")) || pathExists(filepath.Join(dir, "verified.json")) {
		t.Error("the failed first theorem left a report (verified.json must not be another theorem's)")
	}
}

// The consumer path: theorems of different modules of one package, checked from one workspace
// (one Lake build); one failing alone leaves the others verified.
func TestConsumerVerifyMany(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	pkg := consumerCopy(t, "toml")
	add := mustExtract(t, "example.com/basic.Add")
	writeFile(t, filepath.Join(pkg, "ConsumerExample", "Twin.lean"),
		"import Extracted\nnamespace ConsumerExample.Twin\ntheorem t : Extracted.entry = Extracted.entry := rfl\nend ConsumerExample.Twin\n")
	writeFile(t, filepath.Join(pkg, "ConsumerExample", "Cheat.lean"), "import Janus\ntheorem ConsumerExample.cheat : False := sorry\n")
	writeFile(t, filepath.Join(pkg, "ConsumerExample", "UsesCheat.lean"),
		"import Extracted\nimport ConsumerExample.Cheat\ntheorem ConsumerExample.UsesCheat.t : Extracted.entry = 0 := ConsumerExample.cheat.elim\n")
	writeFile(t, filepath.Join(pkg, "ConsumerExample", "Broken.lean"),
		"import Extracted\nnamespace ConsumerExample.Broken\ntheorem t : Extracted.entry = 0 := rfl\nend ConsumerExample.Broken\n")
	spec := func(file, name string) string {
		return filepath.Join(pkg, "ConsumerExample", file+".lean") + "::" + name
	}
	results := filepath.Join(t.TempDir(), "r.json")
	run := func(specs ...string) (int, string, string) {
		a := []string{"verify", add, "--proof-root", pkg, "--janus-root", repoRoot, "--results", results}
		for _, s := range specs {
			a = append(a, "--theorem", s)
		}
		return runJanus(t, a...)
	}
	code, out, stderr := run(spec("Add", "ConsumerExample.Add.correctness"), spec("Twin", "ConsumerExample.Twin.t"),
		spec("UsesCheat", "ConsumerExample.UsesCheat.t"), spec("Broken", "ConsumerExample.Broken.t"))
	res := readResults(t, results)
	if code != 1 {
		t.Fatalf("exit %d\n%s\n%s", code, out, stderr)
	}
	for name, why := range map[string]string{
		"ConsumerExample.Add.correctness": "", "ConsumerExample.Twin.t": "",
		"ConsumerExample.UsesCheat.t": "disallowed axioms: sorryAx", "ConsumerExample.Broken.t": "Lean errors (",
	} {
		it := res[name]
		if (why == "") != (it.Status == "verified") || (why != "" && (it.Failure == nil || !strings.Contains(it.Failure.Message, why))) {
			t.Errorf("%s (want %q): %+v", name, why, it)
		}
		if f := filepath.Join(add, "verified", name+".json"); pathExists(f) != (why == "") {
			t.Errorf("%s: report file present=%v", name, pathExists(f))
		}
	}
	// Both passes were checked from one workspace, each with its own replay and module.
	ra := readJSONReport(t, filepath.Join(add, "verified", "ConsumerExample.Add.correctness.json"))
	rt := readJSONReport(t, filepath.Join(add, "verified", "ConsumerExample.Twin.t.json"))
	if ra.Module != "ConsumerExample.Add" || rt.Module != "ConsumerExample.Twin" || ra.Consumer.Workspace != rt.Consumer.Workspace ||
		ra.KernelReplay.Status != "passed" || rt.KernelReplay.Status != "passed" {
		t.Errorf("reports: %+v / %+v", ra.Consumer, rt.Consumer)
	}
	if r := readReport(t, add); r.Theorem != "ConsumerExample.Add.correctness" {
		t.Errorf("verified.json is for %s", r.Theorem)
	}
	// Same theorem name in two files cannot share verified/<name>.json: refused.
	if code, _, stderr := run(spec("Add", "ConsumerExample.Add.correctness"), spec("Twin", "ConsumerExample.Add.correctness")); code != 1 || !strings.Contains(stderr, "listed more than once") {
		t.Errorf("collision: %d %s", code, stderr)
	}
	// A theorem asked for in the wrong module fails alone.
	code, _, _ = run(spec("Add", "ConsumerExample.Add.correctness"), spec("Twin", "ConsumerExample.Add.nothere"))
	res = readResults(t, results)
	if code != 1 || res["ConsumerExample.Add.correctness"].Status != "verified" || res["ConsumerExample.Add.nothere"].Status != "failed" {
		t.Errorf("wrong module: %d %+v", code, res)
	}
}
