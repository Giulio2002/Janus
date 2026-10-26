import Janus
import Extracted

/-!
# `runtime.memequal0` (amd64) meets the `MemequalN … 0` contract

**Guarantee.** For every stack bound `d`, the amd64 machine code of Go 1.26's
`runtime.memequal0(a, b)` (the equality function of zero-size types) satisfies
`Janus.Contracts.MemAmd64.MemequalN … d 0`: from every call state with the contract's
precondition it returns to `[RSP]` without faulting, with `RSP + 8`, `RBP`, `R14`, `X15`, `DF`,
`FS` and `MXCSR` kept, changes no memory, and returns `true` in `AL` (the zero bytes at `a` and
`b` always agree).

**What the code does.** `MOVL $1, AX; RET`: it reads nothing.

**Assumptions.** Only the contract's precondition (of which the code needs the return address).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts.MemAmd64
open Janus.Contracts.Mem (BoolRes)

namespace Proof

theorem correctness (d : Nat) : MemequalN Extracted.program Extracted.entry d 0 := by
  intro s hpc ⟨⟨hg, ⟨hal, hd, hsp, hacc, hx, hdf, hra⟩, hgo⟩, _, _⟩
  janus64_run
  refine EqRet.intro ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (MemFrame.refl _ _) ?_ <;> simp_all [BoolRes, setRegF, retAddrOf]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- The witness call state: `memequal0(VAL, VAL)` on `EqHashModel.wmem64` (return address `wret`
at `[wsp]`), goroutine `wg` (its stack guard word is 0), `RSP = wsp`. -/
def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 3 then BitVec.ofNat 64 VAL
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

/-- The precondition holds at `s0` (stack bound 64). -/
theorem pre : EqPre 64 2 s0 ∧ Input s0 64 2 (s0.regs 0).toNat 0 ∧ Input s0 64 2 (s0.regs 3).toNat 0 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [CallOK, Input, calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil] <;> decide

theorem nonvacuous : ∃ s, s.rip = BitVec.ofNat 64 Extracted.entry ∧
    (EqPre 64 2 s ∧ Input s 64 2 (s.regs 0).toNat 0 ∧ Input s 64 2 (s.regs 3).toNat 0) :=
  ⟨s0, rfl, pre⟩

/-- `correctness` at `s0`: the call returns `true`. -/
theorem returns : ReachesRet Extracted.program (retAddrOf s0) s0
    (fun s' => EqRet 64 2 s0 s' fun r => BoolRes r true) := by
  refine (correctness 64 s0 rfl pre).mono ?_
  intro s' h; simpa using h

end Witness

end Proof
