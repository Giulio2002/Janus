import Extracted

/-! Round n11, witness row WIT5: the contract hypothesis has call-site property P := False (accepted by the audit, N33), so its pre is unsatisfiable and the witness proves it by exfalso. Expected (airtight backstop): rejected. Run WITHOUT --allow-no-witness. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.ICall Janus.Contracts

namespace Proof

theorem correctness (impl : List Segment) (fn : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hc : ICallContract (Extracted.program.link impl) fn 4 16 48 rt (fun _ => []) R (fun _ => False)) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

namespace Witness

def ret : Nat := 0x1000
def sp0 : Nat := 0x200000
def g0 : Nat := 0x300000

def s0 : State :=
  { regs := fun i => if i = 0 then 3 else if i = 1 then 4 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨sp0 - 64, 104, true⟩, ⟨g0, 0x100, false⟩]⟩ }

theorem hc7 : ICallContract (Extracted.program.link ([] : List Segment)) 0 4 16 48 [] (fun _ => [])
    (fun _ _ _ _ _ _ _ => True) (fun _ => False) := by
  intro s _ h
  exact h.2.2.2.elim

theorem hret : RetAddr (Extracted.program.link ([] : List Segment)) ret := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link ([] : List Segment)).withExit ret) Extracted.entry [3, 4] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

theorem nonvacuous : ∃ (impl : List Segment) (fn : Nat) (rt : List (Nat × Nat)) (R : Res) (ret : Nat) (s : State)
    (x y : BitVec 64),
    ICallContract (Extracted.program.link impl) fn 4 16 48 rt (fun _ => []) R (fun _ => False) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x, y] s :=
  ⟨[], 0, [], fun _ _ _ _ _ _ _ => True, ret, s0, 3, 4, hc7, hret, setup⟩

end Witness
end Proof
