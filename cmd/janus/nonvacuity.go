package main

// Non-vacuity policy (UP3c: EVERY main theorem, contract-free ones too, needs a verified tied witness). A MAIN theorem whose statement applies runtime-contract hypotheses
// (verified.json contractHyps non-empty) is accepted only together with a kernel-checked
// non-vacuity witness: a verified theorem of the same run (same proof module) whose audited role
// is witness-nonvacuous and whose matchedMain is THIS theorem. The auditor (Janus/Tools/Audit.lean,
// checkWitness) does the semantic matching: the witness must be an `∃ …` that exhibits a state
// and runtime satisfying the main theorem's whole precondition, contract hypotheses included.
// Every report states the status. There is NO opt-out for a theorem that assumes contracts: --allow-no-witness is
// accepted for compatibility and changes nothing. The only non-strict mode is --audit-only, which is not a
// verification: it checks the proof and the statement audit (for testing the auditor itself), prints "Audit-only",
// writes no verified.json and reports status "audit-only". See docs/SOUNDNESS.md.

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

const (
	nvShown     = "shown"
	nvNotShown  = "not-shown"
	nvAuditOnly = "audit-only"
	nvWitness   = "witness"
)

// nonVacuityVerdict computes the status of reps[i] (a verified main or witness report) against the
// verified reports of the same run. It returns the status, the witness names, and a diagnostic when
// the policy rejects the theorem.
func nonVacuityVerdict(r *verifiedReport, peers []*verifiedReport, auditOnly bool) (status, witness, returns string, d *diag) {
	if strings.HasPrefix(r.Role, "witness-") {
		return nvWitness, "", "", nil
	}
	for _, p := range peers {
		if p == nil || p == r || !supports(p, r) {
			continue
		}
		switch p.Role {
		case "witness-nonvacuous":
			if witness == "" {
				witness = p.Theorem
			}
		case "witness-returns":
			if returns == "" {
				returns = p.Theorem
			}
		}
	}
	if witness != "" {
		return nvShown, witness, returns, nil
	}
	if auditOnly {
		return nvAuditOnly, "", returns, nil
	}
	if len(r.ContractHyps) == 0 && (r.Refutation || r.RunFree) {
		return nvNotShown, "", returns, nil // a refutation claims no run
	}
	if len(r.ContractHyps) == 0 {
		// UP3c: EVERY main theorem needs a verified tied witness, contract-free ones included: an unsatisfiable or circular
		// precondition makes a contract-free theorem exactly as vacuous.
		msg := fmt.Sprintf("%s has no kernel-checked non-vacuity witness verified in this run: nothing shows that its precondition is satisfiable and that the program actually returns from a state satisfying it, so the theorem could be vacuous. Every main theorem is verified ONLY together with a verified Witness.nonvacuous that carries the returning run; --allow-no-witness does not bypass this and is ignored.", termSafe(r.Theorem))
		return "", "", "", &diag{Invalid: true, Stage: "non-vacuity", Msg: msg,
			Next: "Add a named theorem in the proof's Witness namespace (conventionally Witness.nonvacuous) of the form `∃ ret s <binders>, RetAddr … ∧ CallSetup … ∧ <the precondition> ∧ Returns … s (fun s' => ABIReturn s s' ∧ <the post>)` and verify it in the same run (--theorem " +
				witnessHint(r.Theorem) + ")."}
	}
	msg := fmt.Sprintf("%s assumes runtime contracts (%s) but no kernel-checked non-vacuity witness for it was verified in this run: nothing shows that its precondition, those contracts and this program are jointly satisfiable, so the theorem could be vacuous. A theorem that assumes contracts is verified ONLY together with a verified Witness.nonvacuous; --allow-no-witness does not bypass this and is ignored.",
		termSafe(r.Theorem), termSafe(strings.Join(r.ContractHyps, ", ")))
	if returns != "" {
		msg += fmt.Sprintf(" %s (a Witness.returns) was verified, but a concrete run does not state that the contract hypotheses hold of its runtime; it does not show non-vacuity.", termSafe(returns))
	}
	return "", "", "", &diag{Invalid: true, Stage: "non-vacuity", Msg: msg,
		Next: "Add a named theorem in the proof's Witness namespace (conventionally Witness.nonvacuous) of the form `∃ impl … s, <the main theorem's whole precondition, contract hypotheses included>` and verify it in the same run (--theorem " +
			witnessHint(r.Theorem) + "). The auditor matches witnesses by their statement, not their name, but an anonymous `example` cannot be referenced and is not accepted: state it as a named theorem. (--audit-only checks the proof and the statement audit without claiming a verification; it prints \"Audit-only\" and writes no verified.json.)"}
}

// supports: the witness report p is an instance of the main theorem r. The witness may sit in a module of its
// own (rtmisc's Witness.lean imports the main module), so the match is by the theorem's name AND the module
// that declares it (MatchedModules); reports without the module list fall back to the module of the witness.
func supports(p, r *verifiedReport) bool {
	if p.Theorem == r.Theorem {
		return false
	}
	for i, m := range p.MatchedMains {
		if m != r.Theorem {
			continue
		}
		if i < len(p.MatchedModules) {
			if p.MatchedModules[i] == r.Module {
				return true
			}
		} else if p.Module == r.Module {
			return true
		}
	}
	if len(p.MatchedMains) == 0 && p.MatchedMain == r.Theorem && p.Module == r.Module {
		return true
	}
	return false
}

func witnessHint(thm string) string {
	if i := strings.LastIndex(thm, "."); i >= 0 {
		return thm[:i] + ".Witness.nonvacuous"
	}
	return "Witness.nonvacuous"
}

func setNonVacuity(r *verifiedReport, status, witness, returns string) {
	r.NonVacuity, r.NonVacuityWitness, r.NonVacuityReturns = status, witness, returns
}

// nonVacuityLine is the report line (text) stating the status.
func nonVacuityLine(r *verifiedReport) string {
	switch r.NonVacuity {
	case nvShown:
		s := fmt.Sprintf("  Non-vacuity: shown by %s (kernel-checked witness: a concrete state and runtime satisfying the whole precondition, contract hypotheses included)", termSafe(r.NonVacuityWitness))
		if r.NonVacuityReturns != "" {
			s += "; fires: " + termSafe(r.NonVacuityReturns)
		}
		return s
	case nvAuditOnly:
		return "  Non-vacuity: NOT SHOWN (--audit-only: NOT a verification) -- this theorem assumes runtime contracts and nothing shows its hypotheses are jointly satisfiable"
	case nvWitness:
		return "  Non-vacuity: this is a witness (it is not a correctness claim)"
	case nvNotShown:
		if r.RunFree {
			return "  Non-vacuity: Verified (run-free: statement makes no claim about executing the program; hypothesis-free, nothing to witness)"
		}
		if r.Refutation {
			return "  Non-vacuity: Verified (refutation: the statement is a negation, it claims no run)"
		}
		return "  Non-vacuity: NOT SHOWN (no witness for this theorem was verified; it assumes no runtime contract)"
	}
	return "  Non-vacuity: NOT SHOWN (not evaluated)"
}

// applyNonVacuity runs the policy over the outcomes of one run (cmdVerifyMany) and rewrites the
// surviving reports with their status. A rejected theorem's report is withdrawn.
func applyNonVacuity(outdir string, outs []thmOutcome, allow bool) {
	var peers []*verifiedReport
	for _, o := range outs {
		if o.Err == nil && o.Report != nil {
			peers = append(peers, o.Report)
		}
	}
	for i := range outs {
		o := &outs[i]
		if o.Err != nil || o.Report == nil {
			continue
		}
		st, w, ret, d := nonVacuityVerdict(o.Report, peers, allow)
		if d != nil {
			o.Err, o.Report = d, nil
			_ = os.Remove(filepath.Join(outdir, verifiedDir, o.Theorem+".json"))
			if i == 0 {
				_ = os.Remove(filepath.Join(outdir, "verified.json"))
			}
			continue
		}
		setNonVacuity(o.Report, st, w, ret)
		if st == nvAuditOnly {
			// not a verification: no report is left behind that a consumer could take for one
			_ = os.Remove(filepath.Join(outdir, verifiedDir, o.Theorem+".json"))
			if i == 0 {
				_ = os.Remove(filepath.Join(outdir, "verified.json"))
			}
			continue
		}
		var werr error
		if len(outs) == 1 {
			werr = writeReport(filepath.Join(outdir, "verified.json"), o.Report)
		} else if werr = os.MkdirAll(filepath.Join(outdir, verifiedDir), 0o755); werr == nil {
			werr = writeReport(filepath.Join(outdir, verifiedDir, o.Theorem+".json"), o.Report)
			if werr == nil && i == 0 {
				werr = writeReport(filepath.Join(outdir, "verified.json"), o.Report)
			}
		}
		if werr != nil {
			o.Err, o.Report = werr, nil
		}
	}
}

// nonVacuitySingle is the policy for a one-theorem run: no witness can accompany it, so a
// contract-assuming main theorem fails unless opted out.
func nonVacuitySingle(outdir string, r *verifiedReport, allow bool) error {
	st, w, ret, d := nonVacuityVerdict(r, nil, allow)
	if d != nil {
		_ = os.Remove(filepath.Join(outdir, "verified.json"))
		return d
	}
	setNonVacuity(r, st, w, ret)
	if st == nvAuditOnly {
		_ = os.Remove(filepath.Join(outdir, "verified.json"))
		return nil
	}
	return writeReport(filepath.Join(outdir, "verified.json"), r)
}

// nonVacuityBatch is the policy for the requests of one batch group (one extraction). A witness only supports
// a main theorem of the SAME run, i.e. the same outdir (a request's "witnesses" share its outdir): another
// request's witness of the same module does not vouch for this one. A rejected request keeps no report.
func nonVacuityBatch(reqs []*consumerRequest, allow bool) {
	peersOf := func(of *consumerRequest) []*verifiedReport {
		var peers []*verifiedReport
		ao, _ := filepath.Abs(of.Outdir)
		for _, r := range reqs {
			if a, _ := filepath.Abs(r.Outdir); a == ao && r.Err == nil && r.Report != nil {
				peers = append(peers, r.Report)
			}
		}
		return peers
	}
	allPeers := map[*consumerRequest][]*verifiedReport{}
	for _, r := range reqs {
		allPeers[r] = peersOf(r)
	}
	for _, r := range reqs {
		if r.Err != nil || r.Report == nil {
			continue
		}
		st, w, ret, d := nonVacuityVerdict(r.Report, allPeers[r], allow)
		if d != nil {
			r.Err, r.Report = d, nil
			continue
		}
		setNonVacuity(r.Report, st, w, ret)
	}
}
