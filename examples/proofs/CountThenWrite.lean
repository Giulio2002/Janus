import Extracted

/-!
# `CountThenWrite(s Sink, p []byte) (int, error)`: two interface calls to arbitrary callees

`n := s.Count(); if n == 0 { return 0, nil }; return s.Write(p)`. Two `calls [hc1, hc2]` hypotheses, one per itab slot
(`Fun[0]` = `Count`, `Fun[1]` = `Write`), each about a code address that is a parameter of the theorem
(`ICallContract fn₁ …`, `ICallContract fn₂ …`), with their own call-site properties (the receiver for `Count`; the
receiver and the slice for `Write`) and their own result relations `R₁`, `R₂`.

**Guarantee.** For every `fn₁`, `fn₂`, callee memory `rt` and relations `R₁`, `R₂`, if the two callees satisfy their
contracts, `CountThenWrite` returns, and: `Count` was entered with the receiver `w`; its result `c` satisfies `R₁`; if
`c = 0` the function returns `(0, nil)`; otherwise `Write` was entered with `w` and the slice `(ptr, len, cap)` and the
function returns what it returned, unchanged (`R₂`). The continuation holds for **every** value `c` returns. The
assumptions are the two contracts, the link between each itab word and its `fn`, `CodePtrOK` of both, and that the
itab words are outside the callees' memory `rt`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.ICall

namespace Proof

theorem correctness (impl : List Segment) (fn1 fn2 stack : Nat) (rt : List (Nat × Nat)) (R1 R2 : Res)
    (tab w ptr len cap : BitVec 64) :
    ICallContract (Extracted.program.link impl) fn1 1 stack 96 rt (fun _ => []) R1 (fun sc => sc.regs 0 = w) →
    ICallContract (Extracted.program.link impl) fn2 4 stack 96 rt (fun _ => []) R2
      (fun sc => sc.regs 0 = w ∧ sc.regs 1 = ptr ∧ sc.regs 2 = len ∧ sc.regs 3 = cap) →
    Ensures (Extracted.program.link impl) Extracted.entry [tab, w, ptr, len, cap]
      (fun s => 8 ≤ stack ∧ CodePtrOK fn1 ∧ CodePtrOK fn2 ∧
        Disjoint (tab.toNat + 24) 16 (s.sp.toNat - (48 + stack)) (96 + stack) ∧
        GuardOK s 0 ∧ StackOK s (48 + stack) 48 ∧
        tab.toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 16 false = true ∧
        s.mem.readLE (tab.toNat + 24) 8 = fn1 ∧ s.mem.readLE (tab.toNat + 32) 8 = fn2 ∧
        Outside (tab.toNat + 24) 16 rt ∧ Outside (s.sp.toNat - 56) 104 rt)
      (fun _ s' => ∃ c a1 a2 a3 e1 e2, R1 w a1 a2 a3 c e1 e2 ∧
        ((c = 0 ∧ s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0) ∨
         (c ≠ 0 ∧ ∃ n f1 f2, R2 w ptr len cap n f1 f2 ∧ s'.regs 0 = n ∧ s'.regs 1 = f1 ∧ s'.regs 2 = f2))) := by
  intro hc1 hc2 ret hret s hs ⟨h8, ⟨hf14, hf1⟩, ⟨hf24, hf2⟩, hd, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, htb, ht, hF1, hF2, hot, hrt⟩
  janus_intro hs
  simp only [Disjoint] at hd
  have hrt' : Outside (s.sp.toNat - 48 - 8) (96 + 8) rt := hrt.of_sub (by omega) (by omega)
  janus_run [hF1, hF2] calls [hc1, hc2]
  · exact ⟨_, _, _, _, _, _, by janus_assumption, Or.inl (by janus_assumption)⟩
  · exact ⟨_, _, _, _, _, _, by janus_assumption, Or.inr ⟨by janus_assumption, _, _, _, by janus_assumption, rfl, rfl, rfl⟩⟩

/-! ## Non-vacuity witness

A concrete writer (`Janus.Contracts.ICallSat`: A64 code at `0x100000` returning `(len, nil)`) serves both itab slots (`Count` and
`Write`): it meets both contracts in the example's linked program (`Summary.of_codeIn`), the itab's `Fun[0]` and `Fun[1]` words are its
address, and a call state of `CountThenWrite` satisfies the whole precondition. -/

namespace Witness

open Janus.Contracts.EqHashModel (codeIn_link Summary.of_codeIn)
open Janus.Contracts.ICallSat (impl A0 rt0 R0)

def ret : Nat := 0x1000
def sp0 : Nat := 0x200000
def g0 : Nat := 0x300000
def tabA : Nat := 0x400000

/-- The itab: `Fun[0]` (offset 24) and `Fun[1]` (offset 32) are the writer's address, little-endian; zero elsewhere. -/
def bytes (a : Nat) : Byte :=
  if tabA + 24 ≤ a ∧ a < tabA + 40 then BitVec.ofNat 8 ((A0 / 256 ^ ((a - (tabA + 24)) % 8)) % 256) else 0

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 tabA else if i = 1 then 0x600000 else if i = 2 then 0x500000
      else if i = 3 then 3 else if i = 4 then 3 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 64, 112, true⟩, ⟨g0, 0x100, false⟩, ⟨tabA, 0x40, false⟩]⟩ }

theorem hc1 : ICallContract (Extracted.program.link impl) A0 1 16 96 rt0 (fun _ => []) R0 (fun sc => sc.regs 0 = 0x600000) :=
  Summary.of_codeIn (codeIn_link Extracted.program _ (by decide))
    (Janus.Contracts.ICallSat.impl_okP (nargs := 1) (stack := 16) (above := 96) (P := fun sc => sc.regs 0 = 0x600000)
      (fun _ _ => True) (fun _ => trivial))

theorem hc2 : ICallContract (Extracted.program.link impl) A0 4 16 96 rt0 (fun _ => []) R0
    (fun sc => sc.regs 0 = 0x600000 ∧ sc.regs 1 = 0x500000 ∧ sc.regs 2 = 3 ∧ sc.regs 3 = 3) :=
  Summary.of_codeIn (codeIn_link Extracted.program _ (by decide))
    (Janus.Contracts.ICallSat.impl_okP (nargs := 4) (stack := 16) (above := 96)
      (P := fun sc => sc.regs 0 = 0x600000 ∧ sc.regs 1 = 0x500000 ∧ sc.regs 2 = 3 ∧ sc.regs 3 = 3)
      (fun _ _ => True) (fun _ => trivial))

/-- UP3 (U-ICALL-INHABITED): the call-site property of the contract of `correctness` is satisfiable at a call state. -/
theorem inhabited_count : ∃ (stack : Nat) (rt : List (Nat × Nat)) (w : BitVec 64) (s : Janus.Arm64.State),
    Janus.Contracts.ICall.ICallPre 1 stack 96 rt (fun sc => sc.regs 0 = w) s :=
  ⟨16, Janus.Contracts.ICallSat.rt0, 0x600000, { Janus.Contracts.ICallSat.wstate with regs := fun i => if i = 30 then 0x200000#64 else if i = 0 then 0x600000#64 else 0#64 },
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, by decide,
    by show Janus.Outside 0x17f8 104 Janus.Contracts.ICallSat.rt0; simp [Janus.Contracts.ICallSat.rt0], rfl⟩

/-- UP3 (U-ICALL-INHABITED): the call-site property of the contract of `correctness` is satisfiable at a call state. -/
theorem inhabited_write : ∃ (stack : Nat) (rt : List (Nat × Nat)) (w ptr len cap : BitVec 64) (s : Janus.Arm64.State),
    Janus.Contracts.ICall.ICallPre 4 stack 96 rt (fun sc => sc.regs 0 = w ∧ sc.regs 1 = ptr ∧ sc.regs 2 = len ∧ sc.regs 3 = cap) s :=
  ⟨16, Janus.Contracts.ICallSat.rt0, 0x600000, 0x500000, 3, 3, { Janus.Contracts.ICallSat.wstate with regs := fun i => if i = 30 then 0x200000#64 else if i = 0 then 0x600000#64 else if i = 1 then 0x500000#64 else if i = 2 then 3#64 else if i = 3 then 3#64 else 0#64 },
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, by decide,
    by show Janus.Outside 0x17f8 104 Janus.Contracts.ICallSat.rt0; simp [Janus.Contracts.ICallSat.rt0], rfl, rfl, rfl, rfl⟩

theorem hret : RetAddr (Extracted.program.link impl) ret := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry
    [BitVec.ofNat 64 tabA, 0x600000, 0x500000, 3, 3] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

theorem nonvacuous : ∃ (impl : List Segment) (fn1 fn2 stack : Nat) (rt : List (Nat × Nat)) (R1 R2 : Res) (ret : Nat) (s : State)
    (tab w ptr len cap : BitVec 64),
    ICallContract (Extracted.program.link impl) fn1 1 stack 96 rt (fun _ => []) R1 (fun sc => sc.regs 0 = w) ∧
    ICallContract (Extracted.program.link impl) fn2 4 stack 96 rt (fun _ => []) R2
      (fun sc => sc.regs 0 = w ∧ sc.regs 1 = ptr ∧ sc.regs 2 = len ∧ sc.regs 3 = cap) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [tab, w, ptr, len, cap] s ∧
    (8 ≤ stack ∧ CodePtrOK fn1 ∧ CodePtrOK fn2 ∧
      Disjoint (tab.toNat + 24) 16 (s.sp.toNat - (48 + stack)) (96 + stack) ∧
      GuardOK s 0 ∧ StackOK s (48 + stack) 48 ∧
      tab.toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 16 false = true ∧
      s.mem.readLE (tab.toNat + 24) 8 = fn1 ∧ s.mem.readLE (tab.toNat + 32) 8 = fn2 ∧
      Outside (tab.toNat + 24) 16 rt ∧ Outside (s.sp.toNat - 56) 104 rt) :=
  ⟨impl, A0, A0, 16, rt0, R0, R0, ret, s0, BitVec.ofNat 64 tabA, 0x600000, 0x500000, 3, 3, hc1, hc2, hret, setup,
    by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, (by unfold Janus.Spec.Disjoint; decide),
    ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩,
    by decide, by decide, by decide, by decide, by simp [tabA, rt0], by simp [s0, sp0, rt0]⟩

/-- The theorem fires: the concrete call of `CountThenWrite` (the concrete writer serves the itab) returns, and its results are the ones
`correctness` describes. -/
theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    ∃ c a1 a2 a3 e1 e2, R0 0x600000 a1 a2 a3 c e1 e2 ∧
        ((c = 0 ∧ s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0) ∨
         (c ≠ 0 ∧ ∃ n f1 f2, R0 0x600000 0x500000 3 3 n f1 f2 ∧ s'.regs 0 = n ∧ s'.regs 1 = f1 ∧ s'.regs 2 = f2)) :=
  correctness impl A0 A0 16 rt0 R0 R0 (BitVec.ofNat 64 tabA) 0x600000 0x500000 3 3 hc1 hc2 ret hret s0 setup
    ⟨by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, (by unfold Janus.Spec.Disjoint; decide),
    ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩,
    by decide, by decide, by decide, by decide, by simp [tabA, rt0], by simp [s0, sp0, rt0]⟩

end Witness

end Proof
