import Extracted

/-!
# `Get(xs []uint64, i int) uint64` returns `xs[i]` in bounds and panics out of bounds

**Guarantee.** For every slice header `(ptr, len, cap)` in `X0`–`X2`, index `i` in `X3`, every
admissible return address `ret` (`RetAddr`) and every Go call state `s` of
`example.com/basic.Get` returning to `ret` in which the stack-growth prologue falls through
(`GuardOK s 0`) and `SP` is aligned with `[SP-24, SP+16)` writable (`StackOK s 24 16`: the frame
below `SP` and the spill slot of `xs.ptr` above it):

* if `i < len` (as unsigned 64-bit numbers, which is what the compiled `cmp; b.cs` checks), the
  `8·len` bytes at `ptr` are readable and do not overlap that stack window, then the call
  returns to `ret`, obeys the ABI, and `X0` is the 64-bit little-endian word at `ptr + 8·i` in
  the memory **before** the call (so it never faults or panics);
* if `len ≤ i` (unsigned, so this includes negative `i`), the call reaches the bounds-check panic
  stub `runtime.panicBounds`, whatever the buffer.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (ptr len cap i : BitVec 64) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 16) :
    (i.toNat < len.toNat → Ptr s.mem ptr (8 * len.toNat) false →
      Disjoint ptr.toNat (8 * len.toNat) (s.sp.toNat - 24) 40 →
      Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat = s.mem.readLE (ptr.toNat + 8 * i.toNat) 8)) ∧
    (len.toNat ≤ i.toNat → Panics (Extracted.program.withExit ret) s) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  constructor
  · intro hi ⟨hp, hp'⟩ hd
    simp only [Disjoint] at hd
    janus_run
  · intro hi
    janus_run

end Proof

/-! ## Positive control (audit): a call with a readable g, a stack window and a 4-word slice. -/
namespace AuditWitness
open Janus Janus.Arm64 Janus.GoABI Janus.Spec
def ret : Nat := 0x1000
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def mkS (i : BitVec 64) : State :=
  { regs := fun r => if r = 0 then 0x3000 else if r = 1 then 4 else if r = 2 then 4
      else if r = 3 then i else if r = 28 then 0x2000 else if r = 30 then BitVec.ofNat 64 ret
      else 0,
    sp := 0x10000, pc := BitVec.ofNat 64 Extracted.entry, flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨0x10000 - 24, 40, true⟩, ⟨0x2000, 0x100, false⟩, ⟨0x3000, 32, false⟩]⟩ }
theorem setup (i : BitVec 64) :
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0x3000, 4, 4, i] (mkS i) :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | _ |  r <;> simp [mkS] at h ⊢ <;> omega⟩
theorem guard (i : BitVec 64) : GuardOK (mkS i) 0 := by
  refine ⟨by simp [mkS], by simp [mkS, Memory.accessible], ?_⟩; simp [mkS, Memory.readLE]
theorem stack (i : BitVec 64) : StackOK (mkS i) 24 16 := by
  refine ⟨by simp [mkS], by simp [mkS], by simp [mkS], by simp [mkS, Memory.accessible]⟩
-- in bounds: the theorem's Returns conclusion is reached
example : Returns (Extracted.program.withExit ret) (mkS 1) (fun s' => ABIReturn (mkS 1) s' ∧
    (s'.regs 0).toNat = (mkS 1).mem.readLE (0x3000 + 8 * 1) 8) :=
  (Proof.correctness 0x3000 4 4 1 ret hret (mkS 1) (setup 1) (guard 1) (stack 1)).1 (by decide)
    ⟨by decide, by decide⟩ (by simp [Disjoint, mkS])
-- out of bounds: the theorem's Panics conclusion is reached
example : Panics (Extracted.program.withExit ret) (mkS 5) :=
  (Proof.correctness 0x3000 4 4 5 ret hret (mkS 5) (setup 5) (guard 5) (stack 5)).2 (by decide)
end AuditWitness
