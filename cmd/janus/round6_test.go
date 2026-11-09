package main

import (
	"path/filepath"
	"strings"
	"testing"
)

// Round 6 F1/F2 (docs/audit/AUDIT-ROUND6.md): a proof-local name with lookalike letters
// (`Εxtracted.program`, `Janus.GoABI.Εnsures`) or a `«Extracted.program»` component prints like
// the trusted constant it imitates, and an out-of-range numeral (`18446744073709551616` at
// `BitVec 64`) reads as a value it is not. All must be rejected at the statement-identity stage;
// in-range numerals stay accepted.
func TestRound6StatementNames(t *testing.T) {
	defer parallel(t)()
	needLean(t)
	useTestCache(t)
	if _, err := detectSandbox(false); err != nil {
		t.Skipf("no sandbox available: %v", err)
	}
	add := mustExtract(t, "example.com/basic.Add")
	for a, want := range map[string]string{
		"F1a_homoglyph_extracted_program": "shadows the Extracted namespace",
		"F1b_guillemet_extracted":         "shadows the Extracted namespace",
		"F1c_homoglyph_ensures":           "lookalike letters",
		"F2b_wrapped_numeral_def":         "out-of-range numeral",
	} {
		p := filepath.Join(repoRoot, "audit", "round6", "attacks", a+".lean")
		code, _, stderr := runJanus(t, "verify", add, "--proof", p, "--janus-root", repoRoot)
		if code != 1 || !strings.Contains(stderr, want) || !strings.Contains(stderr, "Stage: statement identity") {
			t.Errorf("%s not rejected (%q): %d %s", a, want, code, stderr)
		}
	}
	// The control (F2c, in-range numerals) is verified together with its tied Witness.nonvacuous (a main theorem is verified only
	// with one; the attack file carries the witness at the concrete call Add(3, 4)).
	p := filepath.Join(repoRoot, "audit", "round6", "attacks", "F2c_numeral_in_range.lean")
	if code, out, stderr := runJanus(t, "verify", add, "--proof", p, "--janus-root", repoRoot,
		"--theorem", "Proof.correctness", "--theorem", "Proof.Witness.nonvacuous"); code != 0 {
		t.Errorf("F2c (in-range numerals) no longer verifies: %s\n%s", out, stderr)
	}
}
