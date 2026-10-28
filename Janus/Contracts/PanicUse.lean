import Janus.Contracts.Panic

/-!
# Using the panic engine contracts in a proof

`DeferreturnContract.apply` (as `GopanicContract.apply` and `GoexitContract.apply` in
`Janus.Contracts.Panic`): at a call `S` of `runtime.deferreturn`, continue a `GoReturns` goal from
the engine's description of the calls the runtime makes.
-/

namespace Janus.Contracts.Panic

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-- Use the `deferreturn` contract at a call `S` inside a proof of a `GoReturns` goal at `S`. -/
theorem DeferreturnContract.apply {p p' : Program} {addr : Nat} {P : PanicRuntime}
    {U : State → Nat → Nat → Prop} {S : State} {C : GoClass} {Q : GoOutcome → Prop}
    (h : DeferreturnContract p addr P U) (hpc : S.pc = BitVec.ofNat 64 addr) (hpre : DeferreturnPre P S)
    (k : Engine p P U (S.regs 28) (S.regs 18) (retFrame P S)
      (frameKeep S.mem (retFrame P S) (frameItems S.mem (retFrame P S) (P.defers S.mem (gOf S))))
      .ret (RetFin P S (P.defers S.mem (gOf S))) (P.panics S.mem (gOf S)) (P.room S.mem (gOf S))
      (frameItems S.mem (retFrame P S) (P.defers S.mem (gOf S))) S → GoReturns p' C S Q) :
    GoReturns p' C S Q :=
  k (h S hpc hpre)

/-- The empty range at `0` is outside every list of ranges. -/
theorem outside_zero : ∀ rs : List (Nat × Nat), Outside 0 0 rs
  | [] => trivial
  | (lo, hi) :: rs => ⟨Or.inl (by omega), outside_zero rs⟩

/-- A deferred call that changed nothing in memory returned as `DeferReturned` says (the chain of
panics and the record chain are those at the call). -/
theorem DeferReturned.of_same {P : PanicRuntime} (hl : P.Laws) {x28 x18 : W64} {fsp : Nat}
    {keep : List (Nat × Nat)} {e e' : State} (hpc : e'.pc = e.regs 30) (hsp : e'.sp = e.sp)
    (h28 : e'.regs 28 = x28) (h18 : e'.regs 18 = x18) (hm : e'.mem = e.mem) (henv : P.Env e.mem) :
    DeferReturned P x28 x18 fsp keep e e' ∧ P.panics e'.mem x28.toNat = P.panics e.mem x28.toNat :=
  DeferReturned.of_window hl hpc hsp h28 h18 henv (lo := 0) (hi := 0) (by rw [hm]; exact MemFrame.refl _ _)
    (outside_zero _)

/-- Name the state of a `ReachesRet` goal (to replace a large symbolic state by its facts). -/
theorem _root_.Janus.Tactic.ReachesRet.name {p : Program} {tgt : W64} {S : State} {Q : State → Prop}
    (h : ∀ S', S' = S → ReachesRet p tgt S' Q) : ReachesRet p tgt S Q := h S rfl

end Janus.Contracts.Panic
