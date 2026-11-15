import Extracted
import ConsumerExample.Spec

/-!
# `example.com/basic.Add` computes `addSpec`

Verify against an extraction of `example.com/basic.Add` (see README.md).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace ConsumerExample.Add

theorem correctness : Computes Extracted.program Extracted.entry addSpec := by
  intro x y
  janus_ensures_old
  intro ret hret s hs _
  janus_intro hs
  janus_run [addSpec]


namespace Witness

def ret : Nat := 0x1000

def s0 : State :=
  { regs := fun i => if i = 0 then (3 : BitVec 64) else if i = 1 then (4 : BitVec 64)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 0x100000, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := ⟨fun _ => 0, []⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup0 Extracted.entry [(3 : BitVec 64), (4 : BitVec 64)] s0 :=
  ⟨rfl, by first | decide | simp | omega, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

/-- The theorem fires at a concrete call: `Add(3, 4)` returns `addSpec 3 4`. -/
theorem returns : Returns (Extracted.program.withExit ret) (s0.setRet ret)
    (fun s' => ABIReturn (s0.setRet ret) s' ∧ s'.regs 0 = addSpec 3 4) :=
  (correctness 3 4) s0 setup trivial ret hret

/-- All the hypotheses of `correctness` hold together at a concrete call, and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup0 Extracted.entry [x, y] s ∧ True ∧
    Returns (Extracted.program.withExit ret) (s.setRet ret) (fun s' => ABIReturn (s.setRet ret) s' ∧ s'.regs 0 = addSpec x y) ∧
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True) (fun _ s' => s'.regs 0 = addSpec x y) :=
  ⟨ret, s0, 3, 4, hret, setup, trivial, returns, correctness 3 4⟩

end Witness

end ConsumerExample.Add
