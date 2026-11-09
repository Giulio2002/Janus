import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E6a (D4 residual): disclosed defs compiled from `match` (a universe-polymorphic
`match_1` auxiliary), well-founded recursion with `termination_by`/`decreasing_by`, and an
explicitly universe-polymorphic def. Records how each is disclosed; expected Verified. -/
namespace Proof
def sel (n : Nat) (a b : BitVec 64) : BitVec 64 :=
  match n with
  | 0 => a + b
  | _ + 1 => a * b
def countdown (n : Nat) (acc : BitVec 64) : BitVec 64 :=
  if h : n = 0 then acc else countdown (n - 1) acc
termination_by n
decreasing_by omega
def poly.{u} {α : Sort u} (_a : α) (x : BitVec 64) : BitVec 64 := x
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = sel 0 x y ∧ countdown 3 (s'.regs 0) = poly True (x + y)) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals simp [sel, poly, countdown]

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
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (True) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.regs 0 = sel 0 x y ∧ countdown 3 (s'.regs 0) = poly True (x + y))) := by
  refine ⟨ret, s0, (3), (4), hret, setup, ?pre, correctness (3) (4) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
