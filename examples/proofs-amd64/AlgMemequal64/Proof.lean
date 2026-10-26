import Janus
import Extracted

/-!
# `runtime.memequal64` (amd64) meets the `MemequalN … 8` contract

**Guarantee.** For every stack bound `d`, the amd64 machine code of Go 1.26's
`runtime.memequal64(a, b)` (the equality function of 8-byte memory types) satisfies
`Janus.Contracts.MemAmd64.MemequalN … d 8`: from every call state with the contract's
precondition (the stack guard and ABI conditions, the 8 bytes at `a` and at `b` readable) it
returns to `[RSP]` without faulting, with `RSP + 8`, `RBP`, `R14`, `X15`, `DF`, `FS` and `MXCSR`
kept, changes no memory, and returns in `AL` whether the 8 bytes at `a` equal the 8
bytes at `b`.

**What the code does.** `MOVQ 0(AX), CX; CMPQ 0(BX), CX; SETEQ AL; RET`: one load, one compare with memory, no frame, no
stack check.

**Assumptions.** Only the contract's precondition.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts.MemAmd64
open Janus.Contracts.Mem (BoolRes)

namespace Proof

theorem correctness (d : Nat) : MemequalN Extracted.program Extracted.entry d 8 := by
  intro s hpc ⟨⟨hg, ⟨hal, hd, hsp, hacc, hx, hdf, hra⟩, hgo⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  janus64_run
  refine EqRet.intro ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (MemFrame.refl _ _) ?_
  all_goals try (simp_all [setRegF, retAddrOf]; done)
  simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff]
  rw [Janus.Contracts.IfaceAmd64.setcc_low_byte]
  have h0 := Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  have h1 := Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 8
  generalize s.mem.readLE (s.regs 0).toNat 8 = x at *
  generalize s.mem.readLE (s.regs 3).toNat 8 = y at *
  split
  · have : x = y := by omega
    subst this; simp
  · have : x ≠ y := by omega
    simp [beq_false_of_ne this]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- The witness call state: `memequal64(VAL, VAL)` on `EqHashModel.wmem64` (return address
`wret` at `[wsp]`), goroutine `wg` (its stack guard word is 0), `RSP = wsp`. -/
def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 3 then BitVec.ofNat 64 VAL
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

/-- The precondition holds at `s0` (stack bound 64). -/
theorem pre : EqPre 64 2 s0 ∧ Input s0 64 2 (s0.regs 0).toNat 8 ∧ Input s0 64 2 (s0.regs 3).toNat 8 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [CallOK, Input, calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons,
      outside_nil] <;> decide

theorem nonvacuous : ∃ s, s.rip = BitVec.ofNat 64 Extracted.entry ∧
    (EqPre 64 2 s ∧ Input s 64 2 (s.regs 0).toNat 8 ∧ Input s 64 2 (s.regs 3).toNat 8) :=
  ⟨s0, rfl, pre⟩

/-- `correctness` at `s0`: the call returns `true` (the same bytes). -/
theorem returns : ReachesRet Extracted.program (retAddrOf s0) s0
    (fun s' => EqRet 64 2 s0 s' fun r => BoolRes r true) := by
  have h03 : s0.regs 3 = s0.regs 0 := rfl
  refine (correctness 64 s0 rfl pre).mono ?_
  intro s' h; simpa only [h03, beq_self_eq_true] using h

end Witness

end Proof
