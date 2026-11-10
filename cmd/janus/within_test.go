package main

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// Instruction-count bounds (v0.3.0): EnsuresWithin is an Ensures-family MAIN theorem and RunsAtLeastOnCall a universal run
// claim; both need a verified witness tied to them by name, exactly like Ensures. These tests pin the policy on the Go side
// (nonVacuityVerdict) and the places of the trusted Lean sources the audit relies on (a source pin: weakening any of them
// must fail here as well as in the red-team rows of test/redteam/rounds/roundwithin).

func TestWithinMainsNeedATiedWitness(t *testing.T) {
	for _, name := range []string{"Proof.within", "Proof.atLeast"} {
		main := &verifiedReport{Theorem: name, Module: "Proof", Role: "main"}
		st, w, _, d := nonVacuityVerdict(main, nil, false)
		if d == nil || !d.Invalid || d.Stage != "non-vacuity" || st != "" || w != "" {
			t.Fatalf("%s without a witness must be rejected at the non-vacuity stage: status=%q diag=%+v", name, st, d)
		}
		// a witness tied to `correctness` does not vouch for the bound claim
		corr := &verifiedReport{Theorem: "Proof.correctness", Module: "Proof", Role: "main"}
		wit := &verifiedReport{Theorem: "Proof.Witness.nonvacuous", Module: "Proof", Role: "witness-nonvacuous",
			MatchedMain: "Proof.correctness", MatchedMains: []string{"Proof.correctness"}, MatchedModules: []string{"Proof"}}
		if _, _, _, d := nonVacuityVerdict(main, []*verifiedReport{corr, wit}, false); d == nil {
			t.Fatalf("%s: the witness of `correctness` must not support it", name)
		}
		// its own witness (Witness.within / Witness.atLeast) does
		short := strings.TrimPrefix(name, "Proof.")
		own := &verifiedReport{Theorem: "Proof.Witness." + short, Module: "Proof", Role: "witness-nonvacuous",
			MatchedMain: name, MatchedMains: []string{name}, MatchedModules: []string{"Proof"}}
		st, w, _, d = nonVacuityVerdict(main, []*verifiedReport{corr, wit, own}, false)
		if d != nil || st != nvShown || w != own.Theorem {
			t.Fatalf("%s with its tied witness: status=%q witness=%q diag=%+v", name, st, w, d)
		}
		// a run-free exemption never applies to a main that reaches a run claim (the audit sets RunFree only when no
		// run claim is reachable; ReturnsWithin/RunsAtLeast are in that list, see TestWithinAuditSourcePins)
	}
}

func TestWithinAuditSourcePins(t *testing.T) {
	read := func(rel string) string {
		b, err := os.ReadFile(filepath.Join("..", "..", rel))
		if err != nil {
			t.Fatal(err)
		}
		return string(b)
	}
	audit := read("Janus/Tools/Audit.lean")
	// the run-claim list (runFree decision) names both bound predicates of both ISAs
	for _, c := range []string{"`Janus.GoABI.ReturnsWithin", "`Janus.GoABI.RunsAtLeast", "`Janus.Amd64.GoABI.ReturnsWithin", "`Janus.Amd64.GoABI.RunsAtLeast"} {
		if !strings.Contains(audit, c) {
			t.Errorf("Audit.lean: the run-claim list lost %s", c)
		}
	}
	// the precondition scan (the [RSP]-word rule) covers EnsuresWithin (pre = arg 4 of 6) and RunsAtLeastOnCall (arg 4 of 5)
	for _, c := range []string{
		"`Janus.GoABI.EnsuresWithin || n == `Janus.Amd64.GoABI.EnsuresWithin) && e.getAppNumArgs == 6 then acc.push (e.getArg! 4)",
		"`Janus.GoABI.RunsAtLeastOnCall || n == `Janus.Amd64.GoABI.RunsAtLeastOnCall) && e.getAppNumArgs == 5 then acc.push (e.getArg! 4)",
		"`Janus.GoABI.Ensures || n == `Janus.Amd64.GoABI.Ensures) && e.getAppNumArgs == 5 then acc.push (e.getArg! 3)", // unchanged
	} {
		if !strings.Contains(audit, c) {
			t.Errorf("Audit.lean: precondition scan lost %q", c)
		}
	}
	// the witness rule: a lower bound needs a returning run, a ReturnsWithin main is witnessed by Returns or ReturnsWithin
	for _, c := range []string{"def withoutBound", "def returnsRunAt", "isRunsAtLeast lastC", "U-WITNESS-RUN"} {
		if !strings.Contains(audit, c) {
			t.Errorf("Audit.lean: the witness rule for the bound claims lost %q", c)
		}
	}
	// the definitions are pinned verbatim (the meaning of a bound: run (n + 1), a lower bound is run m = outOfFuel)
	defs := map[string][]string{
		"Janus/GoABI.lean": {
			"∃ s', p.run (n + 1) s = .ok (.returned s') ∧ post s'",
			"p.run m s = .error .outOfFuel",
			"ReturnsWithin (bound s) (p.withExit ret) s (fun s' => ABIReturn s s' ∧ post s s')",
			"RunsAtLeast (lower s) (p.withExit ret) s",
		},
		"Janus/Amd64/GoABI.lean": {
			"∃ s', p.run (n + 1) s = .ok (.returned s') ∧ post s'",
			"p.run m s = .error .outOfFuel",
			"ReturnsWithin (bound s) (p.withExit ret) s (fun s' => ABIReturn s s' ∧ post s s')",
			"RunsAtLeast (lower s) (p.withExit ret) s",
		},
	}
	for f, ss := range defs {
		src := read(f)
		for _, s := range ss {
			if !strings.Contains(src, s) {
				t.Errorf("%s: the definition lost %q", f, s)
			}
		}
		for _, name := range []string{"def ReturnsWithin", "def RunsAtLeast ", "def EnsuresWithin", "def RunsAtLeastOnCall", "theorem exact_count", "theorem ReturnsWithin.returns", "theorem EnsuresWithin.ensures"} {
			if !strings.Contains(src, name) {
				t.Errorf("%s: missing %q", f, name)
			}
		}
		// no axiom, sorry or native_decide in the new section
		i := strings.Index(src, "section Within")
		if i < 0 {
			t.Fatalf("%s: no `section Within`", f)
		}
		sec := src[i:]
		if regexp.MustCompile(`\bsorry\b|\baxiom\b|native_decide|\bunsafe\b|\bopaque\b|implemented_by`).MatchString(sec) {
			t.Errorf("%s: the Within section uses sorry/axiom/native_decide/unsafe/opaque", f)
		}
	}
}
