import Extracted

/-! KA1 (known-accepted limitation, docs/SOUNDNESS.md "UP3: known limitation"): the Ensures pre pins `¬ R` at the SPECIFIC arguments (1, 2, 3, 4)
of a call no witness run takes. The witness exhibits the contract at other arguments (P: X0 = 9, R non-empty there), a call-site state with X0 = 9, and a returning run.
Expected-verdict: Verified
Expected-reason: known-accepted (path reachability is not required)
The proof is `Add`'s; the hypotheses are never used. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.ICall Janus.Contracts

namespace Proof

theorem correctness (impl : List Segment) (fn : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hc : ICallContract (Extracted.program.link impl) fn 4 16 48 rt (fun _ => []) R (fun sc => sc.regs 0 = 9)) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => ∀ n e1 e2, ¬ R 1 2 3 4 n e1 e2)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

namespace Witness
open Janus.Contracts.EqHashModel (codeIn_link Summary.of_codeIn)
open Janus.Contracts.ICallSat (impl A0 rt0 R0)

def RK : Res := fun a _ c _ n e1 e2 => a = 9 ∧ n = c ∧ e1 = 0 ∧ e2 = 0

def ret : Nat := 0x1000
def sp0 : Nat := 0x200000
def g0 : Nat := 0x300000

def s0 : State :=
  { regs := fun i => if i = 0 then 3 else if i = 1 then 4 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨sp0 - 64, 104, true⟩, ⟨g0, 0x100, false⟩]⟩ }

/-- The stock writer meets the contract with the weaker `R` (it only has to answer calls with `X0 = 9`). -/
theorem hc0 : ICallContract (Extracted.program.link impl) A0 4 16 48 rt0 (fun _ => []) RK (fun sc => sc.regs 0 = 9) := by
  have h := Janus.Contracts.ICallSat.impl_okP (nargs := 4) (stack := 16) (above := 48)
    (P := fun sc => sc.regs 0 = 9) (fun _ _ => True) (fun _ => trivial)
  have h2 : ICallContract (Extracted.program.link impl) A0 4 16 48 rt0 (fun _ => []) RK (fun sc => sc.regs 0 = 9) := by
    refine Summary.of_codeIn (codeIn_link Extracted.program _ (by decide)) ?_
    unfold ICallContract at h
    refine Summary.mono h (fun _ hp => hp) ?_
    rintro s s' ⟨_, _, _, hP⟩ ⟨junk, f, v, m, ex, ep, h1, h2, h3, ⟨hn, he1, he2⟩, hpr⟩
    exact ⟨junk, f, v, m, ex, ep, h1, h2, h3, ⟨hP, hn, he1, he2⟩, hpr⟩
  exact h2

theorem hret : RetAddr (Extracted.program.link impl) ret := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [3, 4] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

theorem pin : ∀ n e1 e2, ¬ RK 1 2 3 4 n e1 e2 := by
  intro n e1 e2 h; exact absurd h.1 (by decide)

def wsCall : State :=
  { Janus.Contracts.ICallSat.wstate with regs := fun i => if i = 30 then 0x200000#64 else if i = 0 then 9#64 else 0#64 }

theorem wsCall_pre : ICallPre 4 16 48 rt0 (fun sc => sc.regs 0 = 9) wsCall :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, by decide,
    by show Janus.Outside 0x17f8 56 rt0; simp [rt0], rfl⟩

theorem nonvacuous : ∃ (impl : List Segment) (fn : Nat) (rt : List (Nat × Nat)) (R : Res) (ret : Nat) (s : State)
    (x y : BitVec 64),
    ICallContract (Extracted.program.link impl) fn 4 16 48 rt (fun _ => []) R (fun sc => sc.regs 0 = 9) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x, y] s ∧
    (∀ n e1 e2, ¬ R 1 2 3 4 n e1 e2) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 fn ∧ ICallPre 4 16 48 rt (fun sc => sc.regs 0 = 9) s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s
      (fun s' => ABIReturn s s' ∧ (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) :=
  ⟨impl, A0, rt0, RK, ret, s0, 3, 4, hc0, hret, setup, pin, ⟨wsCall, rfl, wsCall_pre⟩,
    correctness impl A0 rt0 RK 3 4 hc0 ret hret s0 setup pin⟩

end Witness
end Proof
