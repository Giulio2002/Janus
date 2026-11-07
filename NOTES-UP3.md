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
