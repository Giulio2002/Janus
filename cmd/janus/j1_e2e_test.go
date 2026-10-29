package main

// J1 end-to-end rows: the prestarted auditor (auditserve.go) gives the same verdicts and the
// same report as the classic invocation, and runs none of the proof's code.

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func j1Report(t *testing.T, dir string) map[string]any {
	t.Helper()
	b, err := os.ReadFile(filepath.Join(dir, "verified.json"))
	if err != nil {
		t.Fatal(err)
	}
	var m map[string]any
	if err := json.Unmarshal(b, &m); err != nil {
		t.Fatal(err)
	}
	// what legitimately differs between two runs
	for _, k := range []string{"timestamp", "memoryGuard", "cached", "cachedFrom"} {
		delete(m, k)
	}
	// which modules the replay cache covered depends on what ran before, not on the auditor
	if kr, ok := m["kernelReplay"].(map[string]any); ok {
		delete(kr, "cached")
	}
	return m
}

// The report of a verification with the prestarted auditor equals the report of the classic
// invocation, and both reject the same bad proofs with the same diagnostic.
func TestJ1PrestartMatchesClassic(t *testing.T) {
	needLeanSlow(t)
	t.Setenv("JANUS_RESULT_CACHE", "off")
	dir := mustExtract(t, "example.com/basic.Get")
	proofs := t.TempDir()
	write := func(name, body string) string {
		p := filepath.Join(proofs, name)
		if err := os.WriteFile(p, []byte(body), 0o644); err != nil {
			t.Fatal(err)
		}
		return p
	}
	good := write("Good.lean", "import Extracted\nnamespace Proof\ntheorem correctness : Extracted.entry = Extracted.entry := rfl\n"+
		"theorem segs : Extracted.program.segments.length = 1 := by decide\nend Proof\n")
	bad := map[string]string{
		"Sorry.lean":   "import Extracted\nnamespace Proof\ntheorem correctness : Extracted.entry = 0 := sorry\nend Proof\n",
		"Axiom.lean":   "import Extracted\nnamespace Proof\naxiom cheat : Extracted.entry = 0\ntheorem correctness : Extracted.entry = 0 := cheat\nend Proof\n",
		"Missing.lean": "import Extracted\nnamespace Proof\ntheorem other : True := trivial\nend Proof\n",
		"Broken.lean":  "import Extracted\nnamespace Proof\ntheorem correctness : Extracted.entry = 0 := rfl\nend Proof\n",
		"NoExtr.lean":  "import Extracted\nnamespace Proof\ntheorem correctness : 1 = 1 := rfl\nend Proof\n",
	}
	verify := func(prestart string, proof string, extra ...string) (int, string) {
		t.Setenv("JANUS_AUDIT_PRESTART", prestart)
		code, out, stderr := runJanus(t, append([]string{"verify", dir, "--proof", proof, "--janus-root", repoRoot}, extra...)...)
		return code, out + stderr
	}
	var reports [2]map[string]any
	for i, mode := range []string{"off", "on"} {
		if code, out := verify(mode, good); code != 0 || !strings.Contains(out, "Verified: Proof.correctness") {
			t.Fatalf("prestart=%s: %d %s", mode, code, out)
		}
		reports[i] = j1Report(t, dir)
	}
	a, _ := json.Marshal(reports[0])
	b, _ := json.Marshal(reports[1])
	if string(a) != string(b) {
		t.Fatalf("the reports differ\nclassic:  %s\nprestart: %s", a, b)
	}
	if code, out := verify("on", good, "--theorem", "Proof.segs"); code != 0 || !strings.Contains(out, "Verified: Proof.segs") {
		t.Fatalf("second theorem: %d %s", code, out)
	}
	for name, body := range bad {
		var outs [2]string
		for i, mode := range []string{"off", "on"} {
			code, out := verify(mode, write(name, body))
			if code != 1 || !strings.Contains(out, "Invalid: ") {
				t.Fatalf("%s prestart=%s: %d %s", name, mode, code, out)
			}
			if _, err := os.Stat(filepath.Join(dir, "verified.json")); err == nil {
				t.Fatalf("%s prestart=%s: verified.json not removed", name, mode)
			}
			// the diagnostic, without paths and timing
			outs[i] = out
		}
		if stageOf(outs[0]) != stageOf(outs[1]) {
			t.Errorf("%s: classic stage %q, prestart stage %q", name, stageOf(outs[0]), stageOf(outs[1]))
		}
	}
}

func stageOf(s string) string {
	for _, l := range strings.Split(s, "\n") {
		if strings.HasPrefix(l, "Stage: ") {
			return l
		}
	}
	return ""
}

// The proof's `initialize` blocks never run in the prestarted auditor: the module is imported
// as data. (An initializer that ran would throw and fail the audit.)
func TestJ1ServeInitializerNotRun(t *testing.T) {
	needLeanSlow(t)
	t.Setenv("JANUS_RESULT_CACHE", "off")
	t.Setenv("JANUS_AUDIT_PRESTART", "on")
	dir := mustExtract(t, "example.com/basic.Get")
	p := filepath.Join(t.TempDir(), "Init.lean")
	body := "import Extracted\nimport Lean\n" +
		"initialize janusInitRan : Unit ← throw (IO.userError \"INITIALIZER-RAN\")\n" +
		"namespace Proof\ntheorem correctness : Extracted.entry = Extracted.entry := rfl\nend Proof\n"
	if err := os.WriteFile(p, []byte(body), 0o644); err != nil {
		t.Fatal(err)
	}
	code, out, stderr := runJanus(t, "verify", dir, "--proof", p, "--janus-root", repoRoot)
	if code != 0 || strings.Contains(out+stderr, "INITIALIZER-RAN") || !strings.HasPrefix(out, "Verified: Proof.correctness") {
		t.Fatalf("an initializer of the proof ran in the auditor or the verification failed: %d\n%s\n%s", code, out, stderr)
	}
}
