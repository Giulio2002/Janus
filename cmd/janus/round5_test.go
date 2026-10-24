package main

import (
	"path/filepath"
	"strings"
	"testing"
)

// Round 5 E5 (docs/AUDIT-ROUND5.md): an instance bound inside the statement or a disclosed
// definition (`Exists fun [_ : HMul …] => r = x * y`, a class-typed binder, a nested `∀ [_ : C]`,
// or a def passed to `Exists` without its instance argument) makes `x * y` refer to a quantified
// instance, so the claim holds for every result while it prints as `… = x * y`. All of them
// must be rejected at the statement-identity stage; the theorem-level binder of round 3 (R2)
// stays accepted.
func TestBoundInstanceRejected(t *testing.T) {
	needLean(t)
	useTestCache(t)
	if _, err := detectSandbox(false); err != nil {
		t.Skipf("no sandbox available: %v", err)
	}
	add := mustExtract(t, "example.com/basic.Add")
	for _, a := range []string{"E5a_exists_instbinder_def", "E5b_exists_instbinder_stmt", "E5c_exists_default_classbinder",
		"E5d_hyp_forall_instbinder", "E5e_unapplied_inst_param", "E5f_unapplied_via_alias"} {
		p := filepath.Join(repoRoot, "audit", "round5", "attacks", a+".lean")
		code, _, stderr := runJanus(t, "verify", add, "--proof", p, "--janus-root", repoRoot)
		if code != 1 || !(strings.Contains(stderr, "binds the instance") || strings.Contains(stderr, "inline instance")) ||
			!strings.Contains(stderr, "Stage: statement identity") {
			t.Errorf("%s not rejected as a bound instance: %d %s", a, code, stderr)
		}
	}
	p := filepath.Join(repoRoot, "audit", "round3", "attacks", "R2_inst_binder.lean")
	if code, _, stderr := runJanus(t, "verify", add, "--proof", p, "--janus-root", repoRoot); code != 0 {
		t.Errorf("R2 (theorem-level instance binder) no longer verifies: %s", stderr)
	}
}
