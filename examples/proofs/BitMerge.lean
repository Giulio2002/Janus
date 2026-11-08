import Extracted

/-!
# `BitMerge(x, y, m uint64) (uint64, uint64)`: two bit-merge formulas, `&^`, `&`, `|`, `^`

**Guarantee.** For all 64-bit `x`, `y`, `m` and every Go call state of
`example.com/basic.BitMerge`, the call returns (never faulting or panicking), obeys the ABI, and
both results are the merge of `x` and `y` under the mask `m`: for every bit position `i < 64`,
bit `i` of `X0` and of `X1` is bit `i` of `y` if bit `i` of `m` is set and bit `i` of `x`
otherwise. `X0` is computed as `(x &^ m) | (y & m)` (`bic`, `and`, `orr`), `X1` as
`x ^ ((x ^ y) & m)` (`eor`, `and`, `eor`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

/-- Bit `i` of the merge of `x` and `y` under `m`. -/
def mergeBit (x y m : BitVec 64) (i : Nat) : Bool := if m.getLsbD i then y.getLsbD i else x.getLsbD i

theorem correctness (x y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y, m] (fun _ => True)
      (fun _ s' => ∀ i < 64, (s'.regs 0).getLsbD i = mergeBit x y m i ∧
        (s'.regs 1).getLsbD i = mergeBit x y m i) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  intro i hi
  simp only [mergeBit, BitVec.getLsbD_eq_getElem hi, BitVec.getElem_or, BitVec.getElem_and,
    BitVec.getElem_xor, BitVec.getElem_not]
  generalize x[i] = a, y[i] = b, m[i] = c
  revert a b c; decide


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (1) else if i = 1 then (2) else if i = 2 then (3) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(1 : BitVec 64), (2 : BitVec 64), (3 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64) (m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y, m] s ∧ (True) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (∀ i < 64, (s'.regs 0).getLsbD i = mergeBit x y m i ∧
        (s'.regs 1).getLsbD i = mergeBit x y m i)) := by
  refine ⟨ret, s0, (1), (2), (3), hret, setup, ?pre, correctness (1) (2) (3) ret hret s0 setup ?pre⟩
  case pre =>
    simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp] <;> decide

end Witness

end Proof
