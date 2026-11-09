import Extracted

/-! Verify-level attacker witness ATT_N18_let_w2_lt_8: the pre pins the contract size to an unsatisfiable value (the contract holds vacuously); the witness proves it by exfalso and OMITS the call-site state
Expected-verdict: rejected
Expected-reason: U-ICALL-STACK|does not exhibit a call-site state
The proof is `Add`'s; the hypotheses are never used. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.ICall Janus.Contracts

namespace Proof

theorem correctness (impl : List Segment) (fn k w a : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hw : k ≤ w)
    (hc : ICallContract (Extracted.program.link impl) fn 4 k 48 rt (fun _ => []) R (fun _ => True)) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => (let w2 := w; w2 < 8))
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

theorem hc7 : ICallContract (Extracted.program.link ([] : List Segment)) 0 4 7 48 [] (fun _ => [])
    (fun _ _ _ _ _ _ _ => True) (fun _ => True) := by
  intro s _ h
  exfalso
  have := h.1.2.2.2.2.1
  omega

theorem hret : RetAddr (Extracted.program.link ([] : List Segment)) ret := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link ([] : List Segment)).withExit ret) Extracted.entry [3, 4] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

theorem returns : Returns ((Extracted.program.link ([] : List Segment)).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    (s'.regs 0).toNat = ((3 : BitVec 64).toNat + (4 : BitVec 64).toNat) % 2 ^ 64 :=
  correctness [] 0 7 7 0 [] (fun _ _ _ _ _ _ _ => True) 3 4 (by decide) hc7 ret hret s0 setup (by decide)

theorem nonvacuous : ∃ (impl : List Segment) (fn k w a : Nat) (rt : List (Nat × Nat)) (R : Res) (ret : Nat) (s : State) (x y : BitVec 64),
    (k ≤ w) ∧ ICallContract (Extracted.program.link impl) fn 4 k 48 rt (fun _ => []) R (fun _ => True) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x, y] s ∧ (let w2 := w; w2 < 8) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64 :=
  ⟨[], 0, 7, 7, 0, [], fun _ _ _ _ _ _ _ => True, ret, s0, 3, 4, by decide, hc7, hret, setup, by decide, returns⟩

end Witness

end Proof
