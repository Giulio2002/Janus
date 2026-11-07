# NOTES-UP3 (upstream-fix worker UP3, branch agent/up3-vacuity off integ/n11 b8ac6cca)
Goal: close RT-N11 ACCEPTED vacuity routes (1) size/w pinned via Ensures pre/conclusion, (2) via non-Prop binders (PLift/PProd/Fin), (3) joint unsatisfiability of nargs/above/stack.
## Changes
- (A) cmd/janus/nonvacuity.go, verify.go, batch.go: `--allow-no-witness` is INERT (still parsed). A theorem with contract hypotheses is verified only with a verified Witness.nonvacuous (all paths: single, many, batch). New `--audit-only` (verify only): proof + statement audit, prints `Audit-only:` (NOT `Verified:`), writes no verified.json, status `audit-only`; for testing the auditor.
- (B) Janus/Tools/Audit.lean checkContractHyps (main theorems): size vars and their bounding `w` occur nowhere else: not in non-Prop binders, not in the conclusion outside the POST of an Ensures (pre, entry, args, lets). Joint check: least fixpoint of stack>=8, above>=8+8*nargs over numeral lower bounds vs nargs<=64 / <2^47.
  DEVIATION from the brief: post-condition mentions are allowed (control N12 `w = w` in post must keep verifying; a post is an obligation, not an assumption).
- (C) audit/roundup3 (55 rows, runner), run twice per row (audit-only: expected verdict; allow-no-witness: never Verified). Old rounds: `--allow-no-witness` -> `--audit-only` + output shim (Audit-only: -> Verified:) in 12 scripts; round15 N7 rewritten.

## Witness side (coordinator requests after RT WIT1 / WIT5-P)
Implemented (Audit.lean `proofHead`, `witnessSizes`, called from `checkWitness` with the witness's kernel value): the witness proof
term is walked (`∃`->Exists.intro, `∧`->And.intro; sees through theorem/def unfolding, Eq.mpr/mp/cast/id/Eq.rec, let, beta, whnfCore) and
every contract instance in a leaf must have stack>=8 (<2^47), nargs<=64, above>=8+8*nargs (<2^47), d<2^47, and (ICallContract) P not
literally False. Unreadable positions are rejected naming contract + position + stuck constant. Rows audit/roundup3/wit WIT1-WIT6 (WIT6 = RT's P:=False).
Dev hook JANUS_STOP_AFTER_AUDIT=1 (verify stops after the statement audit; prints AUDIT-STAGE-OK; never a verification).
NOT implemented (too large for this pass; DESIGN): the principled check. A syntactic pre-filter cannot catch an unsatisfiable P/R/keep
that is not literally False (e.g. `1 = 2`, `fun s => s.sp = s.sp + 1`).
 * Janus defines per family `XInhabited args : Prop := ∃ s, <CallOK/ICallPre … ∧ P s>` (ICall: `∃ s, ICallPre nargs stack above rt P s`; Rt*/Newobject*/Mem*: their CallOK+pre).
 * The witness checker (it already locates each instance) elaborates the obligation `XInhabited <instance args>` with the witness's concrete
   args (after the same walk), and discharges it by `first | decide | omega | simp [stock lemmas]` inside a generated Lean theorem run through the
   normal compile + kernel replay path (Go side: janus appends the generated theorems to the sandboxed Proof compile, like the proof itself). Stock
   forms (P:=True, literal sizes, standard R/keep/RtPreserves) need Janus lemmas `ICallInhabited_of_true` etc. (one per family, kernel-checked once).
 * Failing auto-discharge: the author supplies a lemma named `<witness>.inhabited_<n>` (convention), looked up by the checker; absent -> reject.
 * Cost: one Janus lemma per family (ICall, ICall64, RtContract[64], RtLive*, Newobject*, Mem family `d`), an Audit.lean obligation generator and a Go hook.

## U-ICALL-INHABITED (decision 2026-11-07; supersedes the generic ContractInhabited design above)
Honesty is a statement property. Janus/Tools/Audit.lean `inhabitationLemma` (called in checkContractHyps for MAIN theorems): every
`ICallContract`/`ICallContract64` whose call-site property P is not (reducibly) `fun _ => True` needs a kernel-checked theorem in a NON-trusted
module (any name; found by statement, axioms limited to propext/Classical.choice/Quot.sound, checked with collectAxioms) of the form

    theorem <name> : ∃ (<vars…>), ∃ s, ICallPre nargs stack above rt P s            -- arm64   (Janus.Contracts.ICall.ICallPre)
    theorem <name> : ∃ (<vars…>), ∃ s, ICallPre64 nargs stack above rt P s          -- amd64   (Janus.Contracts.ICall.ICallPre64)

(any leading ∀/∃ binders are instantiated; the statement's own variables — sizes, rt, the variables P mentions — are existential: the contract may
not be unsatisfiable for EVERY instantiation. nargs/stack/above/rt/P are unified with defeq against the statement's contract, up to those variables.)
ICallPre is exactly the Summary precondition (`CallOK ∧ 8+8·nargs ≤ above ∧ Outside … ∧ P s`), so a vacuous contract has no such lemma. `P := False`
(or `fun s => s.sp = s.sp + 1`) has none: rejected at statement level. Stock `fun _ => True`: no lemma. keep/preserves/R: keep is any (a callee writing nothing
meets it), preserves is restricted by the existing rules (`fun _ _ => True` | `RtPreserves R2`), R and rt are variables; RtContract/RtLiveContract specs are framework constants only
(frameworkConstParamType) so no author-chosen predicate exists there. ICall* is the only family with an author-supplied predicate (P).
Example for fv-uint256 Format (7 uses `ICallContract … stack 96 rt (fun _ => []) R (WP z w)`, arm64 ErlP*): 

    theorem erlp_pre_inhabited : ∃ (z w : BitVec 64) (stack : Nat) (rt : List (Nat × Nat)) (s : State),
        Janus.Contracts.ICall.ICallPre 4 stack 96 rt (WP z w) s

(an existing witness state of ErlpWit.lean gives it; the stack can be fixed to any value >= 8 the lemma's state supports).
SAT gate (ii): `python3 -I audit/round9/sat_check.py` on this tree: `SAT contracts=247 witnessed=251 open=0 missing=0`, pinnedContracts allowlist (232 predicates) matches: every family used in contracts is witnessed satisfiable for some R.
Tests: JanusTests/ICallAudit.lean U-ICALL-INHABITED rows (P:=True accepted; non-stock P with lemma accepted; P:=False and unsatisfiable P without lemma rejected).

## U-WITNESS-RUN (user decision 2026-11-07): the tied returning-run witness is the gating witness
**Dropped:** the "size/w not in the Ensures pre" half of the size rule (real frame facts: `8 ≤ stack`, `StackOK s (48 + stack) 40`). Kept: binder rule (PLift/PProd/Fin/…),
joint-satisfiability fixpoint, witness-side size walk, U-ICALL-INHABITED. `--allow-no-witness` stays inert; `--audit-only` is test-only.

**Rule (Audit.lean `matchNonvacuous`, no new role, no helper def):** `Witness.nonvacuous` (any name; role from its `∃` statement) must, in addition to a conjunct for every
hypothesis and every unfolded-conclusion premise (return address, CallSetup, entry, each pre conjunct), contain as a conjunct the conclusion's FINAL claim at the same
instantiation: for `Ensures`, `Returns ((Extracted.program.link impl).withExit ret) s (fun s' => ABIReturn s s' ∧ <post s s'>)` (for `EnsuresGo*`, the `GoReturns …`).
It is found by unification against the main statement's unfolded body, so the same impl/R/R2/rt/sizes/s/ret instantiate hypotheses, pre and run. A witness proved by
`exfalso` (unsatisfiable size, `P := False`, empty R, a pin in the pre) cannot supply a `Returns` of a program whose call is taken.
**Canonical shape** (copy the main statement; ∀ → ∃; append the Returns conjunct):

    theorem nonvacuous : ∃ (<all statement variables>) (ret : Nat) (s : State),
        <every hypothesis> ∧ RetAddr (Extracted.program.link impl) ret ∧
        CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [<args>] s ∧ (<the whole Ensures pre, as one conjunct group>) ∧
        Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ <post s s'>
      := ⟨…, hc, hret, setup, ⟨pre items⟩, correctness … hc ret hret s setup ⟨pre items⟩⟩

Worked example: examples/proofs/WriteTo.lean (arm64; amd64 analogue examples/proofs-amd64/WriteTo/Proof.lean to follow the same pattern with `Returns`/`ABIReturn` of Janus.Amd64.GoABI).
The old `Witness.returns` stays (informational; example sweep demands it) and is no longer needed for non-vacuity.

**Contract exercise (design trade-off, NOT built):** the run conjunct proves the program returns with the contracts instantiated, but does not by itself show the run TAKES each call
(a path avoiding the callee leaves its contract vacuous on the paths that call). Options: (a) accept: with a concrete callee the run witness normally calls it (WriteTo's only path does);
(b) per-contract `CallsThrough` conjunct stated in Janus and proved by the run: requires a trace predicate of `Program.run` (a Run that records which stub/contract addresses were entered) in
Janus core, i.e. a new definition plus a lemma per proof style: costly; (c) auditor-side: the witness' concrete state `s` is a closed term, and the auditor evaluates `Program.run` on it
with a tracing evaluator (kernel-checked only in the sense of decide, not trusted): cheap but adds trusted evaluation. Recommendation: ship (a) now, add (b) for the sweep's multi-path rows later.

# HANDOVER (written at ~300k context, 2026-11-07 ~22:50)
Branch agent/up3-vacuity in /srv/janus-up3, base integ/n11 b8ac6cca. Last commit 1de13d78 (+ uncommitted: ICallAudit.lean row cleanup + wp row, Audit.lean `dbg` diagnostic in inhabitationLemma).
## Committed so far
- (A) cmd/janus: `--allow-no-witness` inert in verify/verify-batch/multi; `--audit-only` (test-only, prints `Audit-only:`, no verified.json); dev hook JANUS_STOP_AFTER_AUDIT=1 (prints AUDIT-STAGE-OK per audited theorem, never a verification). nonvacuity_test.go updated (+TestAllowNoWitnessIsInert); Go tests NOT yet run (go test ./cmd/janus hangs ~11 min in TestMain; leave to the gotest lane).
- (B) Audit.lean: binder rule (size/w in non-Prop binder), joint-satisfiability fixpoint; the conclusion-pre half DROPPED (real frame facts). Witness side: proofHead/witnessSizes (proof-term walk, range check, P literally False); U-ICALL-INHABITED (inhabitationLemma: non-stock ICallContract P needs an `∃ …, ∃ s, ICallPre[64] nargs stack above rt P s` theorem in a non-trusted module); U-WITNESS-RUN (matchNonvacuous: witness must contain the unfolded conclusion's final `Returns …` conjunct at the same instantiation).
- (C) audit/roundup3: rows/ (55 N-rows, copied from RT) + wit/WIT1-WIT6 + run-roundup3.sh; 12 old audit scripts switched to --audit-only with an `Audit-only:`->`Verified:` shim; round15 N7 rewritten. N33 expectation flipped to rejected (U-ICALL-INHABITED).
- Examples: inhabitation lemmas added to WriteTo/CountThenWrite (both ISAs); WriteTo arm64 nonvacuous upgraded with the Returns conjunct (UNVERIFIED, see open diagnostic).
## Open diagnostic (blocks freezing the shape)
Direct run in progress (task bf2yd23nn): `bin/janus verify artifacts/WriteTo --proof examples/proofs/WriteTo.lean --theorem Proof.correctness --theorem Proof.Witness.nonvacuous --janus-root /srv/janus-up3` with JANUS_CACHE_DIR=<scratchpad>/cache. Previous run: audit rejected correctness with "no kernel-checked theorem states ∃ s, ICallPre … for P = fun sc => sc.regs 0 = w ∧ …" although `Proof.Witness.inhabited_write` exists in the file. JanusTests row `inhab_wp` (variable-bearing P) passes, so the matcher works in the test env; the real env differs (audit env stubs, namespace Proof.Witness, or collectAxioms). The error message now lists candidates with `head ok`/`unifies but axioms …`: read it, fix, re-run. Suspects: (1) the audit env holds proof-module theorems as type-only stubs -> collectAxioms sees no value (then accept stubs of the PROOF module whose axioms the Go side already checks per theorem? NO: the lemma is not a verified theorem; it must be kernel-replayed: ask the Go side to also verify it, or require the lemma to be listed as a --theorem), (2) universe/level params.
 Design note for (1): simplest sound route = the lemma must itself be verified in the same run (listed with --theorem like witnesses; role `witness-inhabited` from its ∃ ICallPre statement), and the auditor looks it up among the VERIFIED theorems (Go side supplies the list), mirroring how nonvacuous witnesses are matched in nonvacuity.go. Without that the lemma's proof is only compiled, not replayed (the replay covers the module closure, so actually it IS replayed with Proof; check).
## Remaining steps (order fixed by coordinator)
1. Freeze the returning-run shape (needs WriteTo arm64 to pass); write exact Lean text + measured verify time before/after (baseline integ/n11 sweep: arm64 WriteTo 11.4 s, amd64 10.6 s, verify-all-examples.times) here; TELL MAIN the moment frozen.
2. Per-contract call-reach: for each contract hypothesis c a conjunct, in the SAME returning-run witness, `∃ s_c, Steps (link impl) s s_c ∧ s_c.pc = <callee entry fn> ∧ <family pre at s_c>` obtained as a prefix of the run (no separate re-execution, no new Janus core def; speed constraint from the user). Auditor: structural match per contract+callee. NOTE: the Add-based RT rows (N10,N11,N18,N62,N65,N13,N16,N17,N60,N64,N50-52, WIT*) have a run that never calls: with the Returns conjunct alone a witness for them is still satisfiable (Add returns without using the vacuous contract), so ONLY the call-reach requirement rejects them. Until step 2 lands they are accepted by U-WITNESS-RUN alone.
3. Regressions: every N/WIT/R row stays; expected statuses: statement-level audit-only verdict now Verified for the rows whose syntactic rule was dropped (N10 N11 N18 N62 N65 + the six removed ICallAudit rows: `k = 7`, `7 = k`, `w < 8` with k<=w, `w < 20`, `let w2 := w; w2 < 8`, `a = 48`), and REJECTED at verify level with and without --allow-no-witness for "no call-reaching run witness / witness missing" (runner already checks the without-witness case; add a with-witness variant per row once step 2 exists). R01 (/srv/janus-rt-n11/audit/roundn11/rows2/R01_R_pinned_false_in_pre.lean) must be copied into audit/roundup3/rows2 and rejected the same way. Controls (N01-06, N12, C1, V15, F01, F08, W02, W03, 15 relaxation examples, Mbar) must verify.
4. Upgrade examples to the shape: WriteTo amd64, CountThenWrite both ISAs, then the whole example sweep (every contract-bearing example's nonvacuous). fv-uint256 corpus (~30 modules) upgrade by FV workers.
5. Corpus check script: <scratchpad>/fv/run.sh (witness-only, JANUS_STOP_AFTER_AUDIT=1, pinned --janus-root /srv/janus-up3; needs a janus built from the committed tree: `CGO_ENABLED=0 go build -o bin/janus ./cmd/janus` AFTER committing, else "framework identity differs"). Never started successfully (cold framework build ~20 min).
6. check-merge: `scripts/check-merge.sh -j 2` under `/srv/janus-ops/bin/heavy-run -s 2 -- memcap -m 96G …`, plus `python3 -I audit/round9/sat_check.py /srv/janus-up3` (last: contracts=247 witnessed=251 open=0 missing=0). Timings to report.
## Environment facts
artifacts/examples-arm64 copied from integ/n11 (untracked). `lake build Janus.Tools.Audit janus-audit` then `go build -o bin/janus ./cmd/janus` after every Audit.lean edit. Test row runner: audit/roundup3/run-roundup3.sh.

# SHAPE FROZEN (step 1) — returning-run witness, arm64 WriteTo verified at commit after 17ec1188
`janus verify artifacts/WriteTo --proof examples/proofs/WriteTo.lean --theorem Proof.correctness --theorem Proof.Witness.nonvacuous --no-result-cache`:
correctness verified, "Non-vacuity: shown by Proof.Witness.nonvacuous"; witness verified (axioms propext/Classical.choice/Quot.sound, kernel replay passed).
Exact text to copy (examples/proofs/WriteTo.lean, `Witness.nonvacuous`): take the main theorem's binders as ∃, then
    <every hypothesis> ∧ RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [<args>] s ∧
    (<the whole Ensures pre, one parenthesised conjunction>) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ <post s s'>
proved by ⟨…vars…, hc, hret, setup, ⟨pre items⟩, correctness <vars> hc ret hret s setup ⟨pre items⟩⟩ (the main theorem itself gives the run).
amd64: same with Janus.Amd64.GoABI's Returns/ABIReturn. ALSO required for any non-stock ICallContract P: a lemma
`theorem <any name> : ∃ (<vars>) (s : State), Janus.Contracts.ICall.ICallPre[64] nargs stack above rt P s` (see WriteTo inhabited_write).
Timing: cold framework runs (7 min) are not comparable; warm before/after for WriteTo to be recorded next (baseline integ/n11 sweep arm64 11.4 s, amd64 10.6 s).
Step 2 (call-reach conjunct) NOT yet built; until then Add-based rows with a never-called contract are not closed by the Returns conjunct.
