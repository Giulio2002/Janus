import Janus
import Extracted

/-! `example.com/basic.CountThenWrite(s Sink, p []byte) (int, error)` on amd64: `n := s.Count(); if n == 0 { return 0, nil };
return s.Write(p)`, two interface calls through the itab (`MOVQ 24(AX), CX; CALL CX` and `MOVQ 32(DX), DX; CALL DX`) to arbitrary
callees. As the arm64 proof (`examples/proofs/CountThenWrite.lean`): two `ICallContract64` hypotheses for two code addresses
`fn₁`, `fn₂` (statement variables, linked to the itab words), `calls [hc1, hc2]`, and a continuation that holds for every
result the first callee returns. -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.ICall

theorem correctness (impl : List Janus.Amd64.Segment) (fn1 fn2 stack : Nat) (rt : List (Nat × Nat)) (R1 R2 : Res)
    (tab w ptr len cap : BitVec 64) :
    ICallContract64 (Extracted.program.link impl) fn1 1 stack 96 rt (fun _ => []) R1 (fun sc => sc.regs 0 = w) →
    ICallContract64 (Extracted.program.link impl) fn2 4 stack 96 rt (fun _ => []) R2
      (fun sc => sc.regs 0 = w ∧ sc.regs 3 = ptr ∧ sc.regs 1 = len ∧ sc.regs 7 = cap) →
    Ensures (Extracted.program.link impl) Extracted.entry [tab, w, ptr, len, cap]
      (fun s => 8 ≤ stack ∧ CodePtrOK64 fn1 ∧ CodePtrOK64 fn2 ∧
        (tab.toNat + 24 + 16 ≤ (s.regs 4).toNat - (48 + stack) ∨ (s.regs 4).toNat + 48 ≤ tab.toNat + 24) ∧
        StackGuardOK s 0 ∧ StackWritable s (48 + stack) 48 ∧ SPAligned s ∧
        tab.toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 16 false = true ∧
        s.mem.readLE (tab.toNat + 24) 8 = fn1 ∧ s.mem.readLE (tab.toNat + 32) 8 = fn2 ∧
        Outside (tab.toNat + 24) 16 rt ∧ Outside ((s.regs 4).toNat - 48) 96 rt)
      (fun _ s' => ∃ c a1 a2 a3 e1 e2, R1 w a1 a2 a3 c e1 e2 ∧
        ((c = 0 ∧ s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ s'.regs 1 = 0) ∨
         (c ≠ 0 ∧ ∃ n f1 f2, R2 w ptr len cap n f1 f2 ∧ s'.regs 0 = n ∧ s'.regs 3 = f1 ∧ s'.regs 1 = f2))) := by
  intro hc1 hc2 ret hret s hs ⟨h8, hf1, hf2, hd, hg, ⟨hle, hnw, hacc⟩, hal, htb, ht, hF1, hF2, hot, hrt⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [CodePtrOK64] at hf1 hf2
  simp only [regSP, regG, stackguard0Offset, stackguard0, SPAligned] at hacc hle hnw hgl hgb hnw2 hgr hal hd hF1 hF2 hrt hot
  have hal48 : ((s.regs 4).toNat - 48) % 8 = 0 := by omega
  have hrt' : Outside ((s.regs 4).toNat - 8 - 32 - 8) 96 rt := hrt.of_sub (by omega) (by omega)
  janus64_run [hF1, hF2] calls [hc1, hc2]
  · exact ⟨_, _, _, _, _, _, by janus_assumption, Or.inl (by janus_assumption)⟩
  · exact ⟨_, _, _, _, _, _, by janus_assumption, Or.inr ⟨by janus_assumption, _, _, _, by janus_assumption, rfl, rfl, rfl⟩⟩

/-! ## Non-vacuity witness

As the arm64 proof: a concrete writer (`Janus.Contracts.ICallSatAmd64`) serves both itab slots; it meets both contracts in the
example's linked program, the itab's `Fun[0]`, `Fun[1]` words are its address, and a call state of `CountThenWrite` satisfies the
whole precondition. -/

namespace Witness

open Janus.Contracts.EqHashModel (codeIn_link64 Summary.of_codeIn64)
open Janus.Contracts.ICallSat (rt0 R0)
open Janus.Contracts.ICallSatAmd64 (impl A0 impl_okP)

def ret : Nat := 0x1000
def sp0 : Nat := 0x200000
def g0 : Nat := 0x300000
def tabA : Nat := 0x400000

def bytes (a : Nat) : Janus.Arm64.Byte :=
  if tabA + 24 ≤ a ∧ a < tabA + 40 then BitVec.ofNat 8 ((A0 / 256 ^ ((a - (tabA + 24)) % 8)) % 256)
  else if sp0 ≤ a ∧ a < sp0 + 8 then BitVec.ofNat 8 ((ret / 256 ^ (a - sp0)) % 256) else 0

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 tabA else if i = 3 then 0x600000 else if i = 1 then 0x500000
      else if i = 7 then 3 else if i = 6 then 3 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 64, 112, true⟩, ⟨g0, 0x100, false⟩, ⟨tabA, 0x40, false⟩]⟩ }

theorem hc1 : ICallContract64 (Extracted.program.link impl) A0 1 16 96 rt0 (fun _ => []) R0 (fun sc => sc.regs 0 = 0x600000) :=
  Summary.of_codeIn64 (codeIn_link64 Extracted.program _ (by decide))
    (impl_okP (nargs := 1) (stack := 16) (above := 96) (P := fun sc => sc.regs 0 = 0x600000) (fun _ _ => True) (fun _ => trivial))

theorem hc2 : ICallContract64 (Extracted.program.link impl) A0 4 16 96 rt0 (fun _ => []) R0
    (fun sc => sc.regs 0 = 0x600000 ∧ sc.regs 3 = 0x500000 ∧ sc.regs 1 = 3 ∧ sc.regs 7 = 3) :=
  Summary.of_codeIn64 (codeIn_link64 Extracted.program _ (by decide))
    (impl_okP (nargs := 4) (stack := 16) (above := 96)
      (P := fun sc => sc.regs 0 = 0x600000 ∧ sc.regs 3 = 0x500000 ∧ sc.regs 1 = 3 ∧ sc.regs 7 = 3) (fun _ _ => True) (fun _ => trivial))

/-- UP3 (U-ICALL-INHABITED): the call-site property of the contract of `correctness` is satisfiable at a call state. -/
theorem inhabited_count : ∃ (stack : Nat) (rt : List (Nat × Nat)) (w : BitVec 64) (s : Janus.Amd64.State),
    Janus.Contracts.ICall.ICallPre64 1 stack 96 rt (fun sc => sc.regs 0 = w) s :=
  ⟨16, Janus.Contracts.ICallSat.rt0, 0x600000, { Janus.Contracts.ICallSatAmd64.wstate with regs := fun i => if i = 4 then 0x1800#64 else if i = 0 then 0x600000#64 else 0#64 },
    ⟨by decide, by decide, by decide, by decide, by decide⟩, by decide,
    by show Janus.Outside 0x1800 96 Janus.Contracts.ICallSat.rt0; simp [Janus.Contracts.ICallSat.rt0], rfl⟩

/-- UP3 (U-ICALL-INHABITED): the call-site property of the contract of `correctness` is satisfiable at a call state. -/
theorem inhabited_write : ∃ (stack : Nat) (rt : List (Nat × Nat)) (w ptr len cap : BitVec 64) (s : Janus.Amd64.State),
    Janus.Contracts.ICall.ICallPre64 4 stack 96 rt (fun sc => sc.regs 0 = w ∧ sc.regs 3 = ptr ∧ sc.regs 1 = len ∧ sc.regs 7 = cap) s :=
  ⟨16, Janus.Contracts.ICallSat.rt0, 0x600000, 0x500000, 3, 3, { Janus.Contracts.ICallSatAmd64.wstate with regs := fun i => if i = 4 then 0x1800#64 else if i = 0 then 0x600000#64 else if i = 3 then 0x500000#64 else if i = 1 then 3#64 else if i = 7 then 3#64 else 0#64 },
    ⟨by decide, by decide, by decide, by decide, by decide⟩, by decide,
    by show Janus.Outside 0x1800 96 Janus.Contracts.ICallSat.rt0; simp [Janus.Contracts.ICallSat.rt0], rfl, rfl, rfl, rfl⟩

theorem hret : RetAddr (Extracted.program.link impl) ret := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry
    [BitVec.ofNat 64 tabA, 0x600000, 0x500000, 3, 3] s0 :=
  ⟨rfl, by decide, rfl, by decide, (fun i h => by
      have h5 : i < 5 := by simpa using h
      match i, h5 with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
      | 3, _ => rfl
      | 4, _ => rfl), rfl⟩

theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (fn1 fn2 stack : Nat) (rt : List (Nat × Nat)) (R1 R2 : Res) (ret : Nat)
    (s : State) (tab w ptr len cap : BitVec 64),
    ICallContract64 (Extracted.program.link impl) fn1 1 stack 96 rt (fun _ => []) R1 (fun sc => sc.regs 0 = w) ∧
    ICallContract64 (Extracted.program.link impl) fn2 4 stack 96 rt (fun _ => []) R2
      (fun sc => sc.regs 0 = w ∧ sc.regs 3 = ptr ∧ sc.regs 1 = len ∧ sc.regs 7 = cap) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [tab, w, ptr, len, cap] s ∧
    (8 ≤ stack ∧ CodePtrOK64 fn1 ∧ CodePtrOK64 fn2 ∧
      (tab.toNat + 24 + 16 ≤ (s.regs 4).toNat - (48 + stack) ∨ (s.regs 4).toNat + 48 ≤ tab.toNat + 24) ∧
      StackGuardOK s 0 ∧ StackWritable s (48 + stack) 48 ∧ SPAligned s ∧
      tab.toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 16 false = true ∧
      s.mem.readLE (tab.toNat + 24) 8 = fn1 ∧ s.mem.readLE (tab.toNat + 32) 8 = fn2 ∧
      Outside (tab.toNat + 24) 16 rt ∧ Outside ((s.regs 4).toNat - 48) 96 rt) :=
  ⟨impl, A0, A0, 16, rt0, R0, R0, ret, s0, BitVec.ofNat 64 tabA, 0x600000, 0x500000, 3, 3, hc1, hc2, hret, setup,
    by decide, (by unfold CodePtrOK64; decide), (by unfold CodePtrOK64; decide), by decide,
    ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, (by unfold SPAligned; decide),
    by decide, by decide, by decide, by decide, by simp [tabA, rt0], by simp [s0, sp0, rt0]⟩

/-- The theorem fires: the concrete call of `CountThenWrite` (the concrete writer serves the itab) returns, and its results are the ones
`correctness` describes. -/
theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    ∃ c a1 a2 a3 e1 e2, R0 0x600000 a1 a2 a3 c e1 e2 ∧
        ((c = 0 ∧ s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ s'.regs 1 = 0) ∨
         (c ≠ 0 ∧ ∃ n f1 f2, R0 0x600000 0x500000 3 3 n f1 f2 ∧ s'.regs 0 = n ∧ s'.regs 3 = f1 ∧ s'.regs 1 = f2)) :=
  correctness impl A0 A0 16 rt0 R0 R0 (BitVec.ofNat 64 tabA) 0x600000 0x500000 3 3 hc1 hc2 ret hret s0 setup
    ⟨by decide, (by unfold CodePtrOK64; decide), (by unfold CodePtrOK64; decide), by decide,
    ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, (by unfold SPAligned; decide),
    by decide, by decide, by decide, by decide, by simp [tabA, rt0], by simp [s0, sp0, rt0]⟩

end Witness

end Proof
