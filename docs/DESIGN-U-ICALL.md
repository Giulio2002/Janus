# DESIGN ONLY: U-ICALL, an abstract callee for dynamic interface method calls

Status: proposal for approval (engine proof-speed worker, 2026-11-06). Branch agent/icall (off integ 5b023ef3). No code yet.

## What exists

Runtime contracts are `Summary` hypotheses at a LITERAL entry (a stub address of the extraction), used by
`janus_run calls [h]` (`Reaches.call`, `applySummary`: prove the precondition at the call site, then continue from
the callee's return state), with satisfiability witnesses (`...Sat`: code at `A0` of a toy program satisfies
the contract) and a "Runtime contracts assumed" section in the printed statement. A dynamic call is followed only
to a target pinned by `ItabIs`/`FuncvalIs` (Janus/Spec/Dynamic.lean) whose code is extracted. An arbitrary
callee has no contract.

## The contract

`Janus.Contracts.ICall` (both ISAs, in `ICall.lean` / `ICallAmd64.lean`, same pattern as `Iface`):

    def ICallSummary (p : Program) (fn : Nat) (W : ICallModel) (P : State → Prop) : Prop :=
      Summary p fn (ICallPre W P) (ICallPost W)

* `fn : Nat` is a theorem PARAMETER (any address), `W : ICallModel` a parameter (its `rt : List (Nat × Nat)`
  is the callee's private memory, a ghost), `P` the CALL-SITE PROPERTY chosen by the theorem.
* `ICallPre W P s` = the ABI facts of a call (`CallOK`-style: return address in X30 / on the stack, stack
  window and guard like `CallPre`), the argument bytes accessible, `W.rt` disjoint from the caller's frame window
  and from the argument buffer, and `P s`. Because it is the PRECONDITION of the hypothesis, `janus_run`
  must PROVE `P` at the call site (`provePre`): a theorem that assumes `ICallSummary ... P` and is proved
  therefore guarantees that every call of the callee is entered with `P` (for EncodeRLP:
  `P s := bytes at (X1, X2) = rlp z`, the call-site argument property). `P` is part of the printed statement.
* `ICallPost W s s'` = ONLY: pc = return address; SP, callee-saved registers (X18, X19..X29 minus the
  scratch set of the ABI; amd64: RBP, R14 (g), R15 per ABIInternal, SP) equal; the caller's non-escaping
  frame and the argument bytes unchanged; memory differs from `s.mem` only inside `W.rt` and inside memory
  not accessible to the caller as frame (`MemFrame s.mem s'.mem (W.rt ++ calleeStack ...)`); regions
  unchanged. Results X0..X2 / RAX,RBX,RCX are ARBITRARY (existentially quantified, not constrained).
  Nothing says heap objects reachable from `z` are untouched (the callee is arbitrary Go).
* "Result forwarded unchanged" is then a property of the CALLER, stated in its theorem: the final
  registers equal the callee's result registers. Since the callee's result is an existential inside the
  hypothesis, the theorem states it with the usual `calls [hS := S]` naming trick turned into a statement:
  `Ensures ... (fun s s' => ∃ s_c, ICallPost W s_c ... ∧ s'.regs 0 = s_c.regs 0 ∧ s'.regs 1 = s_c.regs 1 ...)`
  is awkward, so the contract exposes a ghost: `ICallPost` takes the result triple as part of the model's
  output `W.out : State → (W64 × W64 × W64)` (an uninterpreted function of the call state, chosen once;
  the post says `s'.regs 0 = (W.out s).1` etc.). The theorem then concludes `s'.regs 0 = (W.out s_call).1`
  where `s_call` is the call-site state, expressed through a ghost `W.callState`? NO: see Open question 2.

## Engine change (small)

`stepGoalCore` fails with "the pc ... is not a concrete address" when the BLR/CALL target is `ofNat fn`
for a symbolic `fn`. Change: `calls [h]` accepts a hypothesis whose entry is not evaluable (an fvar `fn`),
kept in `Cfg.symCalls : Array (Expr × Expr)`; when `statePC` gives no literal, compare the normal form of the pc
with `BitVec.ofNat 64 fn` for each symbolic entry (syntactic after `simp` with the hypothesis
`hF : s.mem.readLE (tab + 24) 8 = fn` that links the itab slot to `fn`), and on a match call
`applySummary` unchanged (its lemma `Reaches.call` needs only `hpc : s.pc = ofNat fn`). Everything else (provePre,
destructPost, frames) is reused. Both ISAs (Core.lean for arm64, the amd64 core likewise).

The itab link is a hypothesis `ITabFun s.mem tab 0 fn` (Janus.Spec.Dynamic): `tab`'s `Fun[0]` word is `fn`,
the itab bytes are accessible read-only. It replaces `ItabIs` (which pins one static itab).

## Soundness note

The assumed callee is an arbitrary function behaving as `ICallSummary` says, exactly like every runtime
contract: the theorem is conditional on it and prints it under "Runtime contracts assumed". The contract assumes
nothing a Go function is not entitled to rely on: ABI preservation and that our non-escaping frame is
not written. The statement is for EVERY `fn` and every model `W` satisfying the hypothesis (the quantifiers
are in the theorem), not for one dummy address. Vacuity guard: `ICallSummary` has a satisfiability witness
(`ICallSat`, both ISAs): `W0.rt = [(0x30000, 0x31000)]`, an implementation `implW` at `A0` that stores `len`
in a counter in `W0.rt` and returns `(len, nil)`, an itab whose `Fun[0]` is `A0`, and a concrete call state
satisfying `ICallPre`; proofs that `implW` satisfies `ICallPost` and that EncodeRLP's `Witness.nonvacuous`
precondition holds.

## Red-team rows (audit)

1. A callee that clobbers a callee-saved register: the witness variant `implBad1` writes X19 (amd64: RBP);
   `ICallSummary` for it is refuted (its Summary cannot be proved), the consumer theorem is not applicable;
   plus an audit row showing a forged hypothesis `ICallSummary` with a weakened post (missing the register
   clause) makes the caller's theorem about a preserved register unprovable (the proof needs the clause).
2. A callee that writes the caller's frame: `implBad2` stores into [SP, SP+8); refuted likewise.
3. A call site whose argument bytes differ from `P`: the consumer proof fails at `provePre`.
4. Forged `fn` (hypothesis for fn1, call reaches fn2): `Reaches.call` needs `hpc : pc = ofNat fn`; the
   executor reports the unmatched target (no silent use).

## Consumer example

`examples/proofs/WriteTo.lean` (arm64) and `WriteToAmd64.lean`: `func WriteTo(w io.Writer, b []byte) (int, error) { return w.Write(b) }`
(plus a variant that forwards a computed sub-slice), proving: the callee is entered with
`P := bytes = b[...]`, and the results are the callee's, for every writer. Then EncodeRLP (FV-H) uses the same
contract with `P := bytes = rlp z`.

## Open questions for approval

1. Is `P` as a precondition-parameter of the hypothesis acceptable as the "call-site property" mechanism
   (the alternative, a ghost log `W.log`, needs a state-threaded ghost the Summary form cannot carry)?
2. "Result forwarded unchanged": I propose the theorem concludes
   `∃ vs, ICallResults ... ∧ s'.regs 0 = vs.1 ...` is not expressible without naming the callee's return
   state; the simplest sound form is that the CONTRACT's post fixes `s'.regs 0..2 = W.res (W.entryState s)`
   where `W.res` is a theorem-level parameter function (uninterpreted), and the caller's theorem states
   `s'.regs 0 = W.res (callState)` with `callState` the explicit state at the call (as the printed
   statement shows it). Please confirm, or prefer an existential result in a conjunct.
3. May `fn` be an unconstrained Nat parameter (any address, even inside the extracted program)? I assume yes:
   the Summary at `fn` is then a hypothesis about code the theorem does not extract.
