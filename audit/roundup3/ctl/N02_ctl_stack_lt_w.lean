import Extracted

/-! Round n11 red team, row N02_ctl_stack_lt_w: CONTROL: stack k, 8 <= k, k < w
Expected: Verified (witness-bearing control). The proof is `Add`'s; the hypotheses are never used, so only the audit decides. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof


theorem correctness (impl : List Segment) (fn fn2 k w n a : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hk : 8 ≤ k) (hw : k < w)
    (hc : ICallContract (Extracted.program.link impl) fn 4 k 48 rt (fun _ => []) R (fun _ => True)) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run


namespace Witness
open Janus.Contracts.EqHashModel (codeIn_link Summary.of_codeIn)
open Janus.Contracts.ICallSat (impl A0 rt0 R0)

def ret : Nat := 0x1000
def sp0 : Nat := 0x200000
def g0 : Nat := 0x300000

def s0 : State :=
  { regs := fun i => if i = 0 then 3 else if i = 1 then 4 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨sp0 - 64, 104, true⟩, ⟨g0, 0x100, false⟩]⟩ }

theorem hc : ICallContract (Extracted.program.link impl) A0 4 16 48 rt0 (fun _ => []) R0 (fun _ => True) :=
  Summary.of_codeIn (codeIn_link Extracted.program _ (by decide))
    (Janus.Contracts.ICallSat.impl_okP (nargs := 4) (stack := 16) (above := 48) (P := fun _ => True) (fun _ _ => True) (fun _ => trivial))

def wsCall : State := Janus.Contracts.ICallSat.wstate

theorem wsCall_pre : ICallPre 4 16 48 rt0 (fun _ => True) wsCall := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, by decide, ?_, trivial⟩
  show Janus.Outside 0x17f8 (48 + 8) rt0
  simp [rt0]

theorem hret : RetAddr (Extracted.program.link impl) ret := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [3, 4] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧ (s'.regs 0).toNat = ((3 : BitVec 64).toNat + (4 : BitVec 64).toNat) % 2 ^ 64 :=
  correctness impl A0 0 16 17 0 0 rt0 R0 3 4 (by decide) (by decide) hc ret hret s0 setup trivial

theorem nonvacuous : ∃ (impl : List Segment) (fn k w : Nat) (rt : List (Nat × Nat)) (R : Res) (ret : Nat) (s : State) (x y : BitVec 64),
    (8 ≤ k) ∧ (k < w) ∧
    ICallContract (Extracted.program.link impl) fn 4 k 48 rt (fun _ => []) R (fun _ => True) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x, y] s ∧ True ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 fn ∧ ICallPre 4 k 48 rt (fun _ => True) s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64 :=
  ⟨impl, A0, 16, 17, rt0, R0, ret, s0, 3, 4, by decide, by decide, hc, hret, setup, trivial, ⟨wsCall, rfl, wsCall_pre⟩, returns⟩

end Witness

end Proof
