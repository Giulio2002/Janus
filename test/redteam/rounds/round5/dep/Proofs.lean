import Extracted
import DecLib

/-! Round 5 consumer proofs against the DecLib dependency (example.com/basic.Add). -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace R5Proofs

theorem honest (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

/-- E1h: `decide` in a hypothesis elaborates to the dependency's instance. Expected Invalid. -/
theorem decInst (x y : BitVec 64) (_h : decide (x = 0) = false) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := honest x y

/-- E1i: the dependency's class-valued def passed to `decide`. Expected Invalid. -/
theorem decDef (x y : BitVec 64) (_h : @decide (x = 0) (DecLib.myDec x) = false) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := honest x y

/-- E1j: a dependency def whose *body* uses the custom instance. Allowed (dependency bodies are
the pinned dependency's; `Decidable p` is a subsingleton, so the instance cannot change what
`isZero` means). Expected Verified, with `DecLib.isZero` listed as a dependency constant. -/
theorem decBody (x y : BitVec 64) (_h : DecLib.isZero x = false) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := honest x y

/-- E3e: a dependency structure whose field is named `regs`. Allowed; the statement prints the
dependency's names in full and lists them. Expected Verified. -/
theorem viewRegs (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (DecLib.View.ofFun s'.regs).regs 0 = x + y) := honest x y


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 0 then (3) else if i = 1 then (4) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(3 : BitVec 64), (4 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `decBody` hold together at a concrete call. -/
theorem decBody : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (DecLib.isZero x = false) ∧ (True) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.regs 0 = x + y)) := by
  refine ⟨ret, s0, (3), (4), hret, setup, (by decide), ?pre, R5Proofs.decBody (3) (4) (by decide) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `viewRegs` hold together at a concrete call. -/
theorem viewRegs : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (True) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((DecLib.View.ofFun s'.regs).regs 0 = x + y)) := by
  refine ⟨ret, s0, (3), (4), hret, setup, ?pre, R5Proofs.viewRegs (3) (4) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end R5Proofs
