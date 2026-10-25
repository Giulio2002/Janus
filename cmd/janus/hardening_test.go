package main

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Regression tests for the soundness fixes in docs/AUDIT.md (F1, F2, F6). Each reproduces an
// attack from audit/attacks and asserts the verifier now blocks it (or verifies it with an
// honest, non-misleading statement). They run Lean, so -short skips them.

func attackPath(t *testing.T, name string) string {
	t.Helper()
	p := filepath.Join(repoRoot, "audit", "attacks", name)
	if _, err := os.Stat(p); err != nil {
		t.Skipf("attack file %s not present", name)
	}
	return p
}

// verifyAttack runs `janus verify <art> --proof <attack> [--theorem t]` against the shared
// repo as the framework.
func verifyAttack(t *testing.T, art, attackFile, theorem string) (int, string, string) {
	t.Helper()
	args := []string{"verify", art, "--proof", attackFile, "--janus-root", repoRoot}
	if theorem != "" {
		args = append(args, "--theorem", theorem)
	}
	return runJanus(t, args...)
}

// writeProof writes an inline proof and returns its path.
func writeProof(t *testing.T, body string) string {
	t.Helper()
	p := filepath.Join(t.TempDir(), "Proof.lean")
	if err := os.WriteFile(p, []byte(body), 0o644); err != nil {
		t.Fatal(err)
	}
	return p
}

func TestHardeningAttacks(t *testing.T) {
	defer parallel(t)()
	needLean(t)
	useTestCache(t)
	if _, err := detectSandbox(false); err != nil {
		t.Skipf("no sandbox available: %v", err)
	}

	// File-based attacks that do not use the Janus tactics (unaffected by the GoABI changes),
	// each of which must be rejected at the given stage.
	fileRejected := []struct{ name, theorem, wantStage, wantMsg string }{
		{"A3_initialize.lean", "Proof.correctness", "", ""}, // forged record must not appear (checked below)
		{"A5_skipkernel.lean", "Proof.correctness", "", ""}, // blocked at compile or kernel replay
		{"A7_private_shadow.lean", "Proof.correctness", "", ""},
		{"A10_exit.lean", "Proof.correctness", "theorem audit", "does not define"},
	}
	// Every subtest runs in parallel on its own extraction of Add (its own verified.json).
	for _, c := range fileRejected {
		t.Run(c.name, func(t *testing.T) {
			defer parallel(t)()
			add := mustExtract(t, "example.com/basic.Add")
			code, out, stderr := verifyAttack(t, add, attackPath(t, c.name), c.theorem)
			if code != 1 || out != "" {
				t.Fatalf("%s was not rejected: code %d\n%s\n%s", c.name, code, out, stderr)
			}
			if c.wantStage != "" && !strings.Contains(stderr, "Stage: "+c.wantStage) {
				t.Errorf("%s: want stage %q, got:\n%s", c.name, c.wantStage, stderr)
			}
			if c.wantMsg != "" && !strings.Contains(stderr, c.wantMsg) {
				t.Errorf("%s: want message %q, got:\n%s", c.name, c.wantMsg, stderr)
			}
			// A3: the proof's initialize block must not run inside the audit, so its forged
			// record ("… (forged)") never reaches the verifier.
			if strings.Contains(stderr, "(forged)") {
				t.Errorf("%s: the forged audit record was produced:\n%s", c.name, stderr)
			}
		})
	}

	verifyProof := func(t *testing.T, add, body, theorem string) (int, string, string) {
		return runJanus(t, "verify", add, "--proof", writeProof(t, body), "--janus-root", repoRoot, "--theorem", theorem)
	}

	// A1: a proof-local instance occupying an instance position of the statement's type is a
	// disguised redefinition; it is rejected.
	t.Run("A1 disguised instance", func(t *testing.T) {
		defer parallel(t)()
		add := mustExtract(t, "example.com/basic.Add")
		body := "import Extracted\n" +
			"instance (priority := high) evilMul : HMul Nat Nat Nat := ⟨Nat.add⟩\n" +
			"namespace Proof\n" +
			"theorem correctness : Extracted.entry = Extracted.entry ∧ @HMul.hMul Nat Nat Nat evilMul 2 3 = 5 := ⟨rfl, rfl⟩\n" +
			"end Proof\n"
		code, _, stderr := verifyProof(t, add, body, "Proof.correctness")
		if code != 1 || !strings.Contains(stderr, "disguised instance") || !strings.Contains(stderr, "Stage: statement identity") {
			t.Fatalf("A1 not rejected as a disguised instance: %d\n%s", code, stderr)
		}
	})

	// A2/A4: a proof-local unexpander must not change the printed statement. The proof verifies,
	// but the statement is printed in a clean environment without the proof's unexpander.
	t.Run("unexpander does not change the printed statement", func(t *testing.T) {
		defer parallel(t)()
		add := mustExtract(t, "example.com/basic.Add")
		body := "import Extracted\n" +
			"def Shown (a b : Nat) : Prop := a = b\n" +
			"open Lean PrettyPrinter in\n" +
			"@[app_unexpander Shown] def ue : Unexpander := fun _ => `(HONEST_LOOKING)\n" +
			"namespace Proof\n" +
			"theorem correctness : Shown Extracted.entry Extracted.entry := rfl\n" +
			"end Proof\n"
		code, _, stderr := verifyProof(t, add, body, "Proof.correctness")
		if code != 0 {
			t.Fatalf("unexpander proof should verify with an honest statement: %d\n%s", code, stderr)
		}
		r := readReport(t, add)
		if strings.Contains(r.Statement, "HONEST_LOOKING") || !strings.Contains(r.Statement, "Shown") ||
			!strings.Contains(r.Statement, "Extracted.entry") {
			t.Errorf("statement was altered by the proof's unexpander: %q", r.Statement)
		}
		if !strings.Contains(strings.Join(r.Definitions, " "), "Shown") {
			t.Errorf("the Shown definition was not disclosed: %v", r.Definitions)
		}
	})

	// A9: a proof declaring a name under the Extracted namespace (shadowing it) is rejected.
	t.Run("A9 namespace shadow", func(t *testing.T) {
		defer parallel(t)()
		add := mustExtract(t, "example.com/basic.Add")
		body := "import Extracted\n" +
			"namespace Proof\n" +
			"def Extracted.program : Janus.Program := _root_.Extracted.program\n" +
			"theorem correctness : Extracted.program.exitAddr = Extracted.program.exitAddr := rfl\n" +
			"end Proof\n"
		code, _, stderr := verifyProof(t, add, body, "Proof.correctness")
		if code != 1 || !strings.Contains(stderr, "shadows the Extracted namespace") {
			t.Fatalf("A9 namespace shadow not rejected: %d\n%s", code, stderr)
		}
	})

	// A6: a #eval doing IO cannot escape the sandbox to write outside the private build dir.
	t.Run("A6_eval_io cannot write outside the sandbox", func(t *testing.T) {
		defer parallel(t)()
		add := mustExtract(t, "example.com/basic.Add")
		target := filepath.Join(repoRoot, "audit", "work", "A6-written-during-verify.txt")
		_ = os.Remove(target)
		verifyAttack(t, add, attackPath(t, "A6_eval_io.lean"), "Proof.correctness")
		if _, err := os.Stat(target); err == nil {
			os.Remove(target)
			t.Fatal("A6 proof wrote a file outside the sandbox")
		}
	})
}

// B1: NeverPanics must not be satisfiable by a fault (fixed in GoABI by the hardening agent).
// The attack proof should now fail to prove its (vacuous) statement.
func TestHardeningB1(t *testing.T) {
	defer parallel(t)()
	needLean(t)
	useTestCache(t)
	if _, err := detectSandbox(false); err != nil {
		t.Skip("no sandbox available")
	}
	spec := filepath.Join(repoRoot, "audit", "specs", "B1_neverpanics_fault.lean")
	if _, err := os.Stat(spec); err != nil {
		t.Skip("B1 spec not present")
	}
	a := mustExtract(t, "example.com/basic.Add256")
	code, _, stderr := runJanus(t, "verify", a, "--proof", spec, "--janus-root", repoRoot)
	if code == 0 {
		t.Fatalf("B1 vacuous NeverPanics statement still verifies; GoABI fix missing")
	}
	_ = stderr
}

// F6: PIE (ET_DYN) binaries are rejected by list/extract.
func TestRejectPIE(t *testing.T) {
	pie := filepath.Join(repoRoot, "audit", "work", "examples-arm64-pie")
	if _, err := os.Stat(pie); err != nil {
		t.Skip("no PIE fixture (audit/work/examples-arm64-pie)")
	}
	code, _, stderr := runJanus(t, "list", pie)
	if code != 1 || !strings.Contains(stderr, "position-independent") || !strings.Contains(stderr, "Stage: binary validation") {
		t.Fatalf("PIE binary not rejected: %d %s", code, stderr)
	}
}

// The report records the sandbox mode, and --unsafe-no-sandbox is honoured and flagged.
func TestSandboxRecorded(t *testing.T) {
	defer parallel(t)()
	needLean(t)
	useTestCache(t)
	if _, err := detectSandbox(false); err != nil {
		t.Skip("no sandbox available")
	}
	add := mustExtract(t, "example.com/basic.Add")
	proof := filepath.Join("testdata", "Trivial.lean")
	code, _, stderr := runJanus(t, "verify", add, "--proof", proof, "--janus-root", repoRoot, "--json")
	if code != 0 {
		t.Fatalf("verify: %s", stderr)
	}
	r := readReport(t, add)
	if r.Sandbox.Mode != "bwrap" && r.Sandbox.Mode != "unshare" {
		t.Errorf("sandbox mode not recorded as a real sandbox: %q", r.Sandbox.Mode)
	}

	code, out, stderr := runJanus(t, "verify", add, "--proof", proof, "--janus-root", repoRoot, "--unsafe-no-sandbox", "--json")
	if code != 0 {
		t.Fatalf("verify --unsafe-no-sandbox: %s", stderr)
	}
	var jr verifiedReport
	if err := json.Unmarshal([]byte(out), &jr); err != nil || jr.Sandbox.Mode != "none" {
		t.Fatalf("--unsafe-no-sandbox not recorded as none: %v %q", err, out)
	}
}

// A planted module on the search path is detected (C1 defence). We cannot easily inject one
// into the private dirs, so we unit-test the guard directly.
func TestNoForeignModule(t *testing.T) {
	home := t.TempDir()
	other := t.TempDir()
	// Only the home dir has Extracted.olean: accepted.
	os.WriteFile(filepath.Join(home, "Extracted.olean"), []byte("x"), 0o644)
	if err := noForeignModule(map[string]string{"Extracted": home}, []string{home, other}); err != nil {
		t.Fatalf("clean path rejected: %v", err)
	}
	// A stray copy elsewhere on the path: rejected.
	os.WriteFile(filepath.Join(other, "Extracted.olean"), []byte("y"), 0o644)
	err := noForeignModule(map[string]string{"Extracted": home}, []string{home, other})
	d, ok := err.(*diag)
	if !ok || !strings.Contains(d.Msg, "second Extracted.olean") || d.Stage != "module identity" {
		t.Fatalf("stray module not detected: %v", err)
	}
}
