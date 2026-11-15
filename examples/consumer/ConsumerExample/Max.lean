import Extracted
import ConsumerExample.Spec

/-!
# `example.com/basic.Max` computes `maxSpec`

Verify against an extraction of `example.com/basic.Max` (see README.md). Both sides of the
compiled branch (`cmp x1, x0; b.cs`) are covered.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace ConsumerExample.Max

theorem correctness : Computes Extracted.program Extracted.entry maxSpec := by
  intro x y
  janus_ensures_old
  intro ret hret s hs _
  janus_intro hs
  janus_run [maxSpec]
  all_goals split <;> first | rfl | omega

/-- A consequence through the shared lemmas: the result is at least `x`. -/
theorem result_ge_left (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => x.toNat ≤ (s'.regs 0).toNat) := by
  janus_ensures_old
  intro ret hret s hs hpre
  refine Returns.mono ((correctness x y).toOld ret hret s hs hpre) fun s' h => ⟨h.1, ?_⟩
  have h2 : s'.regs 0 = maxSpec x y := h.2
  show x.toNat ≤ (s'.regs 0).toNat
  rw [h2]
  exact le_maxSpec_left x y


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

/-- The theorem fires at a concrete call: `Max(3, 4)` returns `maxSpec 3 4`. -/
theorem returns : Returns (Extracted.program.withExit ret) (s0.setRet ret)
    (fun s' => ABIReturn (s0.setRet ret) s' ∧ s'.regs 0 = maxSpec 3 4) :=
  (correctness 3 4) s0 setup trivial ret hret

/-- All the hypotheses of `correctness` hold together at a concrete call, and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup0 Extracted.entry [x, y] s ∧ True ∧
    Returns (Extracted.program.withExit ret) (s.setRet ret) (fun s' => ABIReturn (s.setRet ret) s' ∧ s'.regs 0 = maxSpec x y) ∧
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True) (fun _ s' => s'.regs 0 = maxSpec x y) :=
  ⟨ret, s0, 3, 4, hret, setup, trivial, returns, correctness 3 4⟩

end Witness

end ConsumerExample.Max
