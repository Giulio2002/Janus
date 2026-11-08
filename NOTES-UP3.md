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

# FULL HANDOVER for UP3b (written ~322k context; coordinator accepted the frozen shape; FV-WRUN upgrades fv-uint256 witnesses on branch fv/wrun against it — tell it via main if the shape changes)
## Committed state (branch agent/up3-vacuity, /srv/janus-up3, head f0c6bbef, base integ/n11 b8ac6cca; working tree clean except untracked artifacts/)
All of: inert --allow-no-witness + --audit-only + JANUS_STOP_AFTER_AUDIT dev hook; binder rule; joint-sat fixpoint; witness-side proofHead/witnessSizes walk; U-ICALL-INHABITED (candidates computed in the full env into `inhabRef`, matched by statement); U-WITNESS-RUN (`matchNonvacuous` demands the unfolded conclusion's final `Returns …` conjunct); roundup3 rows + WIT1-6; WriteTo/CountThenWrite inhabitation lemmas (4 files); arm64 WriteTo nonvacuous upgraded and VERIFIED. NOT yet verified: WriteTo amd64, CountThenWrite (both ISAs: the Returns conjunct is missing there, so they will FAIL until upgraded), every other contract-bearing example in examples/ (sweep).
## Step 2 design (call-reach; NOT started in code)
Goal: for each contract hypothesis c of a main theorem, some witness proves the run REACHES c's call with c's family pre holding, tied to the same variables, with no new Janus core def and no second execution.
Facts found: `Returns p s Q := ∃ fuel s', p.run fuel s = .ok (.returned s') ∧ Q s'`; `Summary p fn pre post := ∀ s, s.pc = fn → pre s → ReachesRet …`; `Program.Steps p s k s'` exists (Janus/Tactic/Basic.lean `ReachesRet` unfolds to `∃ k s', Program.Steps p s k s' ∧ s'.pc = ret ∧ Q s'`). The main theorem's proof is opaque to the witness, so a call-site state cannot be extracted from `correctness`; the witness must itself exhibit `s_c`.
Proposed statement shape (a conjunct appended to the same nonvacuous): for each c with callee address `fn` and call precondition `CP` (= ICallPre[64] nargs stack above rt P; RtPre/… for other families via a table `contractPre : Name → …`):
    ∃ (k : Nat) (s_c : State), Program.Steps ((Extracted.program.link impl).withExit ret) s k s_c ∧ s_c.pc = BitVec.ofNat 64 fn ∧ CP s_c
Cheapest proof: the witness already fixes concrete s, impl, so `by decide`/`janus_run`-style evaluation of the first k steps; the SAME run: derive `Returns` from `Steps` prefix + `Summary` of the contract? No: Returns comes from correctness (cheap); the Steps prefix is a separate concrete evaluation of a PREFIX (k small), not a re-run to the end. Auditor: structural match per contract application: find a conjunct `Steps … ∧ pc = <fn arg of c> ∧ <ICallPre args of c>` (use findConj with the contract's own args instantiated); for stub-address contracts fn = contractAddr "name". Families other than ICall: their call pre = the `CallOK`/`Ready` part of the Summary precondition — read it off the contract's definition body (`bodyIsSummary` gives Summary p fn pre post: pre is the 3rd arg of the Summary application after unfolding the contract def with its args): generic, no per-family table needed: the conjunct is `∃ k s_c, Steps … s k s_c ∧ s_c.pc = fn ∧ <pre-of-Summary> s_c`.
Trade-off if Steps prefixes are too costly to prove per witness: ask main for the per-path alternative (a witness whose concrete callee is the toy writer and whose start state is one step before the call, `pc = fn` already, i.e. k = 0 starting AT the call site) — weaker (does not show the caller reaches it).
Add-based RT rows (never call the contract) are only closed by this step: with it they cannot supply a Steps prefix to fn.
## Remaining steps
1. Step 2 as above (Audit.lean `matchNonvacuous`, after the U-WITNESS-RUN block; helper to unfold the contract application to its Summary pre). Publish the exact statement + a worked WriteTo example HERE and tell main (FV-WRUN must follow). Keep the check structural (speed constraint: no re-execution in the auditor).
2. Upgrade examples: WriteTo amd64, CountThenWrite arm64+amd64, then all contract-bearing examples of the sweep (`scripts/verify-examples.sh -j 1 <Names>`, `scripts/verify-amd64-examples.sh`); record WARM before/after verify time of WriteTo (baseline integ/n11: arm64 11.4 s, amd64 10.6 s; run twice, second is warm) HERE.
3. Regressions: audit/roundup3: statement-only rows N10/N11/N18/N62/N65 and the six removed ICallAudit pins (k=7, 7=k, w<8, w<20, let-w2<8, a=48) now pass the statement audit; they must be rejected at verify level with and without --allow-no-witness for "no call-reaching run witness". Add R01 (/srv/janus-rt-n11/audit/roundn11/rows2/R01_R_pinned_false_in_pre.lean) and WIT rows with expected-rejection reasons into run-roundup3.sh (needs a verify-level loop: build a witness-bearing Add variant per row, or accept the expected reason "witness missing"). Controls verify: N01-06, N12, C1, V15, F01, F08, W02, W03, 15 relaxation examples, Mbar.
4. Corpus check (fv/wrun branch of /srv/fv-uint256 once FV-WRUN is done, else master 47243a67): <scratchpad>/fv/run.sh style, JANUS_STOP_AFTER_AUDIT=1, janus built from the COMMITTED tree (`CGO_ENABLED=0 go build -o bin/janus ./cmd/janus`, else "framework identity differs"). Zero false rejects.
5. check-merge: `/srv/janus-ops/bin/heavy-run -s 2 -- memcap -m 96G scripts/check-merge.sh -j 2` then `python3 -I audit/round9/sat_check.py /srv/janus-up3` (last: contracts=247 witnessed=251 open=0 missing=0). Also run the Go non-vacuity tests via the gotest lane (`go test ./cmd/janus -run 'NonVacuity|AllowNoWitness'` hangs ~11 min in TestMain when run alone). Report head, timings, rows to main; do NOT merge.
## Commands cheat sheet
Build: `memcap -m 24G lake build Janus.Tools.Audit janus-audit JanusTests.ICallAudit` then `go build -o bin/janus ./cmd/janus`; verify one example: `JANUS_CACHE_DIR=<dir> bin/janus verify artifacts/<Name> --proof examples/proofs/<Name>.lean --theorem Proof.correctness --theorem Proof.Witness.nonvacuous --janus-root /srv/janus-up3` (artifacts/<Name> comes from scripts/verify-examples.sh; artifacts/examples-arm64 copied from integ/n11). Heavy jobs one at a time, memcap, load<62, MemAvailable>=60G, df / >=70G.

**Known limitation (UP3, accepted for the release): path reachability is not required.** The witness exhibits, per contract hypothesis, a
state `s_c` at the callee's entry with the contract's call precondition (tied variables), and a returning run of the whole theorem. It does not
show that the caller's path reaches the call with those arguments. A contract that is vacuous ONLY at the arguments of a call no witness run
takes (an `R` empty only at the caller's real argument values, pinned by the `Ensures` precondition) is accepted (audit/roundup3/known-accepted/KA1).
Universal pins, size pins, `P`/`keep` pins and an empty `R` are rejected. Post-release: optional `Steps`-prefix reachability witnesses.

# FROZEN (step 2): U-WITNESS-CALLSITE — arm64 WriteTo VERIFIED (correctness + nonvacuous, commit after c109a5cc's parent; head below)
For EVERY contract hypothesis `c` of the main theorem, `Witness.nonvacuous` must contain (inside the same `∃ … ,` conjunction, i.e. next to the hypotheses
and the Returns run) the conjunct, with the contract's OWN instantiated entry and arguments:

    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 <entry of c> ∧ <family pre of c, as in the contract's Summary> s_c)
    -- arm64 State = Janus.Arm64.State, `.pc`; amd64: Janus.Amd64.State, `.rip`
    -- ICallContract[64] fn nargs stack above rt keep R P pres:  s_c.pc = BitVec.ofNat 64 fn ∧ ICallPre[64] nargs stack above rt P s_c
    -- other families: the `pre` argument of the Summary the contract definition unfolds to (the auditor reads it generically; write the family's own Pre def)
Proof in the witness: `⟨wsCall, rfl, wsCall_pre⟩` with a closed `def wsCall : State` (at the callee entry) and `theorem wsCall_pre : ICallPre … wsCall` (the stock
callee states in Janus/Contracts/ICallSat[Amd64].lean `wstate`/`wstate_pre` show how; set the argument registers P needs). Worked example: examples/proofs/WriteTo.lean
(`wsCall`, `wsCall_pre`, the conjunct before the `Returns`). The untied inhabitation lemma (U-ICALL-INHABITED) is DROPPED (only literal `P := False` is still rejected at statement level).
Order of conjuncts in the witness does not matter; the auditor matches `s_c.pc = …` and `pre s_c` on the flattened conjuncts with one state. A contract that does not unfold to a `Summary` is rejected.
Timing (cold framework, --no-result-cache, one machine at load ~50): arm64 WriteTo verify correctness+nonvacuous = 5m06s; NOT comparable with the sweep baseline (11.4 s arm64 / 10.6 s amd64): the framework cache was cold. WARM before/after still to measure.
## HANDOVER delta for UP3b (supersedes "Step 2 design" above)
Done: step 2 as frozen above; limitation documented (NOTES, docs/SOUNDNESS.md), audit/roundup3/known-accepted/KA1 (md only; no executable row).
Remaining: (2) upgrade examples: WriteTo amd64, CountThenWrite both ISAs, every contract-bearing example; record WARM timing; (3) regressions: the Add-based RT rows now fail ONLY at the witness (U-WITNESS-CALLSITE / pins make pre uninhabited): needs a verify-level runner variant with a witness-bearing Add proof per row (statement-only rows stay Verified in --audit-only: N10 N11 N18 N62 N65 and the six removed ICallAudit pins); add R01 (rows2) and WIT rows with expected reasons; controls verify; (4) corpus (fv/wrun once FV-WRUN is done) zero false rejects — watch "does not unfold to a Summary" rejections; (5) `check-merge` + SAT (commands above); Go tests via gotest lane. Head: see `git log -1` on agent/up3-vacuity.

# FROZEN (step 2b, UP3b b9871e0a): U-WITNESS-CALLSITE for EVERY contract shape (checked over all pinned families of Janus/Contracts)
The auditor unfolds each contract hypothesis `c` generically (forallMetaTelescope over the unfolded body; the telescope's data binders become the
witness's own existential variables, tied to the same ones by unification) and needs, among the FLATTENED conjuncts of `Witness.nonvacuous`:
1. Bare `Summary p entry pre post` (ICall, Alloc, Cmpstring, Hash, Iface, Instrument, Libc/Lock, Wb, Soft, Cmp, Mem*, Eq*, Panic Deferproc*/Gorecover, Rt, KeepAlive, ConvT64, Sched ...):
       (∃ s_c : State, s_c.pc = BitVec.ofNat 64 <entry> ∧ <pre> s_c)               -- amd64: Janus.Amd64.State, s_c.rip
   `<pre>` = the Summary's 3rd argument with the contract's arguments substituted; write it as its conjuncts (any nesting, matched up to defeq).
2. `∀ xs, Summary p entry pre post` (all *Live families: Newobject/Mallocgc/Makeslice/Growslice/Wb/Rt/Memmove/Typed*/Memclr*Live (+64), ErrorfLive, PoolGet/PutLive
   [PoolPutLive: xs = L b rs]; the map families `∀ f` (Access1/2, Assign, Delete, Clear, IterStart, IterNext `∀ mp f k ks`, ...); Iface InterfaceSwitch `∀ cs`):
       (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.pc = BitVec.ofNat 64 <entry> ∧ <pre with xs := L b> s_c)
   Each x in xs is an existential of the SAME conjunct; it may also be a closed term (`L := []`, `b := 0x400`) inside the pre instead of a bound variable.
   Tiny example (NewobjectLiveContract, arm64):
       (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.pc = BitVec.ofNat 64 addr ∧ NewobjectPre stack s_c ∧ StackRoom s_c stack 1 ∧
          LiveAt R addr [(s_c.regs 0).toNat] L b (newobjectRound s_c) (s_c.regs 28).toNat s_c.mem (calleeStack s_c stack 1))
   WbLiveContract: same with its own pre (see its def in Janus/Contracts/LiveAmd64.lean / Live.lean); map `∀ f`: `∃ (f : …) (s_c : State), s_c.pc = … ∧ RTPre M 3 s_c ∧ …`.
3. Premise chain, no Summary (panic engine: DeferreturnContract `∀ s, s.pc = addr → DeferreturnPre P s → Engine …`; GopanicContract / GoexitContract
   `∀ s fi, s.pc = addr → FuncInfo.find T (s.regs 30).toNat = some fi → GopanicPre P fi s → Engine …`; MorestackContract `∀ g lo hi s_m, MorestackPre … s_m → ∃ …`):
   the conjunct is ∃ the data binders, each PREMISE (as a flattened conjunct, same variables):
       (∃ (s : State) (fi : FuncInfo), s.pc = BitVec.ofNat 64 addr ∧ FuncInfo.find T (s.regs 30).toNat = some fi ∧ GopanicPre P fi s)
       (∃ (s : State), s.pc = BitVec.ofNat 64 addr ∧ DeferreturnPre P s)                          -- amd64: s.rip
       (∃ (g lo hi : Nat) (s_m : State), MorestackPre p FT pool rt H g lo hi s_m)
   A contract that is neither a Summary nor has a premise is rejected ("does not unfold to a Summary or a ∀ xs, premises → … claim").
The reject message prints the exact expected conjunct. Also fixed (needed by two call-site conjuncts): the printed statement is made with pp.deepTerms (the depth limit elided
the tail of a deep witness as `⋯`, which read back as a hole: "elaborates back only partially"). Verified audit-only: WriteTo + CountThenWrite on both ISAs ok; the Live shape
is checked only negatively so far (ScratchSum/ErrWrap print the expected conjunct); first positive Live witness = FV-WRUN's IntoBig.

# GUIDE for workers (JX1/JX2): how to upgrade an example witness (UP3b)
Per-example audit results at 8615b09c: audit/roundup3/sweep-results-8615b09c.tsv (ISA, name, ok|REJECT|NOPROOF, first reason). Check one file:
`JANUS_FRAMEWORK_STORE=/srv/janus-ops/fwstore audit/roundup3/audit-sweep.sh OUTDIR arm64|amd64 Name ...` (audit-only, one `AUDIT-STAGE-OK` per theorem; the REJECT reason prints the exact missing conjunct). Then verify for real with scripts/verify-examples.sh -j 1 Name / scripts/verify-amd64-examples.sh Name.
A witness (`Witness.nonvacuous`) needs, in ONE conjunction at the example's own concrete instantiation: (a) the hypotheses, (b) the pre, (c) per contract hypothesis the call-site conjunct, (d) the run `Returns p s (fun s' => ABIReturn s s' ∧ post)` (for Summary-style mains: `ReachesRet p (s.regs 30) s (post)`), supplied by the main theorem (the example's `returns` lemma, instantiated: put it BEFORE nonvacuous and pass it as the last component).
(c) per contract kind, with the state `wsCall : State` a closed def at the callee's entry and `wsCall_pre : <pre> wsCall` a lemma (the stock callee states and their pre proofs are in Janus/Contracts/*Sat*.lean `wstate`/`wstate_pre`/`*_satisfiable`):
- bare Summary (ICall, Hash, Mem*, Rt, Cmpstring ...):  `(∃ s_c : State, s_c.pc = BitVec.ofNat 64 <entry> ∧ <the Summary's pre, same variables> s_c)`   e.g. WriteTo: `⟨wsCall, rfl, wsCall_pre⟩`; amd64 `s_c.rip`.
- ∀-Live / map families (`∀ L b, Summary …`, `∀ f, Summary …`):  `(∃ L b (s_c : State), s_c.pc = … ∧ <pre with L b> s_c)`; L, b, f may instead be closed terms inside the pre: `⟨[], 0x400, wsCall, rfl, wsCall_pre⟩`.
- premise families (Gopanic/Goexit `∀ s fi, s.pc = a → FuncInfo.find … = some fi → GopanicPre P fi s → Engine …`; Deferreturn; Morestack `∀ g lo hi s_m, MorestackPre … → ∃ …`): `(∃ (s : State) (fi : FuncInfo), s.pc = BitVec.ofNat 64 a ∧ FuncInfo.find T (s.regs 30).toNat = some fi ∧ GopanicPre P fi s)`; `(∃ g lo hi (s_m : State), MorestackPre … s_m)`.
The reject message prints the exact expected conjunct (copy it). Conjunct order is free; nested ∧/∃ are flattened. The pre of the call-site state is the contract's pre at the SAME variables as the witness's instantiated contract hypothesis (the witness fixes concrete values, so a stock `_satisfiable` state is reusable only when its parameters equal the example's; otherwise build a state like the stock one with the example's stack/R/args).

# HANDOVER (UP3b -> next worker), written 2026-11-08 ~01:20 at head after 056c9381 + WIP commit
Branch agent/up3-vacuity, /srv/janus-up3. Auditor batch announced to main: 056c9381 (generic call-site unfold incl. ∀/premise contracts, pp.deepTerms, Exists.rec/And.rec walk). Do NOT change Audit.lean again without announcing (workers pin it).
## Done
- Examples upgraded and audit-only OK: WriteTo + CountThenWrite on both ISAs. Worker guide + per-family conjunct text above. Results of the first sweep: audit/roundup3/sweep-results-8615b09c.tsv (29 ok, 149 REJECT: 115 CALLSITE, 32 RUN, 2 SIZES(fixed); 29 Alg*/Mbar* NOPROOF because the sweep lacked runtime_symbol (fixed in audit-sweep.sh; RERUN them)).
- JX1/JX2 (coordinator): call-site states for Map*/MapVar*/MapStr, Iface*, Hash* (JX1); Rt/panic/Morestack/Mem*/alloc/Errorf/Pool/Cmpstring (JX2), on child branches.
- RUN-conjunct upgrades (script audit/roundup3/upgrade-run.py, simple `∃ …, A ∧ B := ⟨…⟩` + `returns` at s0): 25 files UPGRADED (UNCOMMITTED until audited: re-audit with audit-sweep.sh), 7 shapes need hand edits: arm64 CycA, IsEven (IsEven edited by hand, re-audit), amd64 CycA, IsEven, BitLen64, BitLen64V3, Double. Pattern: move `returns` before `nonvacuous`, add `∧ Returns … s (…)` per member, pass `returns.1 …`.
- Verify-level runner audit/roundup3/run-verify-rows.sh (+ gen-ctl.py -> ctl/ controls N01-N06,N12, gen-vrows.py -> vrows/ PIN1-6, ATT_*): first full run was running (vr.log in the work dir /srv/janus-ops/work.up3b.nibT); an earlier run had an `out` scoping bug (fixed). KA1 executable row NOT written (draft vrows/_KA1_draft.lean.txt; needs R-weakening of the stock writer contract: Summary.mono from R0 to RK given P: X0 = 9). Controls C1/F01/F08/W02/W03 have pre False (no witness can exist): the runner checks --audit-only Verified for them; V15 likewise.
## Remaining
1. Finish RUN conjunct hand edits; re-audit all upgraded files (audit-sweep.sh OUT arm64 ... ; JANUS_FRAMEWORK_STORE=/srv/janus-ops/fwstore); then real verify (scripts/verify-examples.sh -j 1 NAMES, scripts/verify-amd64-examples.sh NAMES).
2. Rerun the Alg*/Mbar* 29 examples; rerun JANUS_SWEEP_ALL=1 for the non-contract examples with a Witness namespace (the RUN rule applies to them too: IsEven/CycA/Eq32 etc. were RUN rejects).
3. Merge JX1/JX2 results; full sweep must be zero rejects. Corpus: audit fv/wrun tree pinned to the final head (fv-uint256 false rejects = auditor bugs; Exists.rec walk done; watch other proof shapes).
4. Regression runner clean pass (+KA1 row), warm timing (WriteTo before/after: baseline integ/n11 arm64 11.4 s amd64 10.6 s; audit-only warm 5.6 s arm64 / 6.6 s amd64 at load ~25), then check-merge + SAT (commands in the cheat sheet above). Do NOT merge.

# HANDOVER (UP3c, 2026-11-08 ~03:50)
Branch agent/up3-vacuity (/srv/janus-up3). Auditor commits by UP3c: e21fc0f0 (call-site pre: every conjunct matched) + 0af9cc0a (ALSO accepts the whole pre as ONE reducible-wrapper conjunct). Announced; workers repin OK.
Done: hand edits (IsEven amd64, CycA x2, BitLen64, BitLen64V3, Double x2); upgrade-alg.py + hand fixes for Alg*equal/Memhash0/Eq32/MulAlgo/WriteBarrier(wb1 only suffices)/SumRec/BigLocal/HoldPtr; 29 Alg*/Mbar* arm64+amd64 call-site+RUN (subagents); JX1 merged (46 examples; its tracked bin/artifacts symlinks + .sw removed, gitignored); runner audit/roundup3/run-verify-rows.sh passes (rows N/R/PIN/WIT/ATT rejected with and without --allow-no-witness, controls N01-N06,N12 verify, KA1 executable known-accepted row audit/roundup3/vrows/KA1.lean verifies). Full-sweep results: audit/roundup3/sweep-all-c0.tsv (before the fixes; CALLSITE rejects left there belong to JX2 families).
Work dir /srv/janus-ops/work.up3c: `one.sh arm64|amd64 Name...` (audit-only, shared warm cache all/cache; cold = ~5 min after any auditor rebuild), all/ = sweep out dir (reuse it: `JANUS_SWEEP_ALL=1 audit/roundup3/audit-sweep.sh /srv/janus-ops/work.up3c/all both`), intobig.sh (fv/csa corpus sample; needs janus package = git archive of head in csa/lean/.lake/packages/janus).
Remaining: merge JX2 (agent/jx2-examples) -> full sweep zero rejects -> real verify of examples touched (scripts/verify-examples.sh -j 1 / verify-amd64-examples.sh) -> corpus audit vs FV-WRUN tree -> warm timings -> check-merge -j 2 under heavy-run + sat_check -> report to main. HAZARD: never merge a branch that tracks `bin`/`artifacts` symlinks without checking `git diff --stat`.
UPDATE 03:55: full sweep all2 (audit/.. /srv/janus-ops/work.up3c/all2.tsv): 297 ok, 51 CALLSITE rejects (all JX2 families: Morestack/Gopanic/Defer/Rt/Newobject/Makeslice/Errorf etc., both ISAs incl. arm64 BigLocal/HoldPtr/SumRec), 0 RUN rejects, 0 other (amd64 WriteBarrier fixed: Janus/Contracts/WriteBarrier.lean gained reducible WbPost64; library change, not auditor). Next: merge agent/jx2-examples when JX2 reports done, re-run sweep, then corpus/timings/check-merge/SAT.
UPDATE 06:30 (UP3c): contract-free witnesses written: arm64 all (WrongAdd exempt = refutation rule: main statement under its binders is `¬ …`; audit record field `refutation`, Go policy), amd64 all 88. Auditor additions (uncommitted->committed, NOT yet announced): panic-only conjuncts (Panics ↔ guard / guard → Panics) need a tied second instance (anchored on the witness's `Panics p s2`), see Div/Mod/Get/Slice2/Slice3. cmd/janus/nonvacuity.go: contract-free main WITHOUT verified witness is now refused (flip is in the tree; fixtures for Go tests still to update: run the gotest lane and fix). Red-team C1-C3 (roundn12/circ) now rejected ("no kernel-checked non-vacuity witness"). Family workers (asm/sys/consumer/rtmisc and cgo/print) still adding witnesses; then: full re-sweep (sweep script covers only arm64/amd64; other families via their verify scripts), Go tests lane fixtures, announce head, real verifies, timings, corpus, check-merge+SAT. CAUTION: rebuilding the framework (lake build) while others audit gives SHA mismatch for them; avoid.

# HANDOVER (UP3c -> UP3d), written 2026-11-08 ~17:30, head = `git log -1` (5fa16ae1 + later)
Branch agent/up3-vacuity (/srv/janus-up3). JX1, JX2 merged. ALL examples have tied witnesses (arm64 349/350 audit-ok, 1 = WrongAdd refutation exempt; amd64, asm, sys, rtmisc, consumer, cgo, print).
## Final rules in the tree (auditor + cmd)
- U-WITNESS-CALLSITE (every contract hyp: flattened conjuncts OR one reducible-wrapper conjunct), U-WITNESS-RUN (every returning conjunct), panic-only conjuncts (head Panics / ↔ with Panics side) need a tied second instance (Div/Mod/Get/Slice2/Slice3 examples); cmd/janus/nonvacuity.go refuses ANY main theorem without a verified tied witness. Exemptions: `refutation` (top-level ¬ ∀ …, C headed by a run-claim definition: WrongAdd, rows PIN9_*) and `runFree` (hypothesis-free: binders only BitVec/Nat/Int/Bool/UInt*, conservative walk reaches no run claim; verdict says "run-free"; rows PIN7/8/10, RF1).
- verify-batch: optional per-request `witnesses` list (companions same outdir, verified/<thm>.json), same-outdir peers, names validated, symlinked outdirs refused. janus init scaffold ships a witness.
## Gotchas learned
- An UNUSED VARIABLE anywhere in Audit.lean makes Lean persist the lint message WITH THE BUILD PATH into Audit.olean => TestForeignFrameworkWriteDetected fails (non-reproducible olean). Keep Audit.lean warning-free for unusedVariables (check `strings Audit.olean | grep ^/.*Audit.lean` = 0).
- Never lake-build / edit Janus/ while another job uses the tree (framework identity). Never merge a branch that tracks `bin`/`artifacts` symlinks.
- Gate is slow on this box (load 40-80): check-merge -j 5 under heavy-run -s 3 ~ 1 item/min; RuneLen 190 s baseline = unchanged (witness cost ~0; Add main+witness warm 4.5 s).
## State / remaining (see also main's queue)
- check-merge running (log /srv/janus-ops/work.up3c/cm5.log). Known failures being fixed: sys WriteOut both ISAs (worker a68ae7e8: call-site + run witnesses). Watch for more families failing in the verify lane (cgo/print with contracts).
- Then: gotest lane green (33/34 single-test green earlier; Foreign + Init fixed since), SAT (python3 -I audit/round9/sat_check.py /srv/janus-up3), runner audit/roundup3/run-verify-rows.sh (rerun: new rows PIN7-10, RF1, ATT_NOCS/NORUN, KA1), corpus audit by FV-WRUN2 at the final head, report head+timings to main. Do NOT merge into integ/*.
UPDATE (UP3c, gate verdict): check-merge -j 5 (heavy-run -s 3) at tree 5fa16ae1+handover (log /srv/janus-ops/work.up3c/cm5.log, lanes artifacts/gate/20261108T160149Z): GATE FAIL in 1h25m27s: PASS govet, axiom/lint, gotest (1h24m58s, all Go tests green), all pre-*; FAIL verify (483 items, 433 pass, 50 fail: list /srv/janus-ops/work.up3c/gate-verify-fails.txt; sys WriteOut/AESField/SVEField since fixed in 07e19030) and rounds (8 audit rows DIFFER from expectations: N10 N11 N18 N46 N62 N65 now audit-only Verified, N45 N53 now rejected: update the round expectation files, see lanes/rounds.log). Remaining: fix the 50 verify rows (witness gaps: rtmisc rows with contracts, amd64 panic/Slice, float posts, WriteBarrier/Atomic*, EncryptBlock corollaries), update round expectations, rerun failed rows, then SAT, runner, corpus audit, final report.


# UP3d: strict witness pairing (auditor change, requested by main)
Branch up3d-pairing (worktree /srv/janus-up3d; to land on agent/up3-vacuity once the check-merge gate in /srv/janus-up3 has finished: editing/building the framework in that tree would break its SHA identity).
Rule: `Witness.nonvacuous` <-> `correctness`; `Witness.<X>` <-> main `<X>` only (Audit.lean `mainsNamed`, `checkWitness`). Verify scripts must pass `Proof.Witness.<X>` for every extra main (`panics exact outOfRange faults forAllValues anyCPU saturation traps full_write corollary*`).
Rows: audit/roundup3/pair/PAIR_ok_control, PAIR1-4 (wired into run-verify-rows.sh). Worked: amd64 Div (`Witness.panics`, a tied `Panics` instance), EncryptBlock corollaries (concrete FIPS-197 C.1 call state s1), WriteBarrier (nonvacuous restated against `correctness`: all eight contracts, call-site premises and eight ReachesRet).
Gotcha: audit-only (JANUS_STOP_AFTER_AUDIT) does NOT show a missing witness for a main (that verdict is Go-side in nonvacuity.go); only a REAL verify does. Warm real verifies take seconds.
