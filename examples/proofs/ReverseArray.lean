import Extracted

/-!
# `ReverseArray(out, in *[4]uint64)`: array value semantics and range over an array

**Guarantee.** For all pointers `out`, `in` to 32 bytes (`out` writable, `in` readable) that are
either the same array or disjoint, both disjoint from the function's stack window
(`[SP-88, SP)`, `StackOK s 88 0`), and every Go call state of `example.com/basic.ReverseArray`,
the call returns (never faulting or panicking), obeys the ABI (`X29` is restored arithmetically,
`add x29, sp, #72`, so this needs Go's frame-pointer invariant `X29 = SP - 8` at the call,
`FPConvention`), and afterwards
`out[i] = in[3 - i]` for every `i < 4`, with `in` read **before** the call. This holds also when
`out = in`: `a := *in` copies the array (value semantics), so the loop `for i, x := range a`
reads the copy, not the elements it has already overwritten.

The copy is two `ldp`/`stp` pairs into the frame (and a second copy for the `range` operand);
the loop has a constant trip count, so `janus_run` executes it.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (out inp : BitVec 64) :
    Ensures Extracted.program Extracted.entry [out, inp]
      (fun s => FPConvention s ∧ StackOK s 88 0 ∧ Ptr s.mem out 32 true ∧ Ptr s.mem inp 32 false ∧
        (out = inp ∨ Disjoint out.toNat 32 inp.toNat 32) ∧
        Disjoint out.toNat 32 (s.sp.toNat - 88) 88 ∧ Disjoint inp.toNat 32 (s.sp.toNat - 88) 88)
      (fun s s' => ∀ i < 4, s'.mem.readLE (out.toNat + 8 * i) 8 =
        s.mem.readLE (inp.toNat + 8 * (3 - i)) 8) := by
  intro ret hret s hs ⟨hfp, ⟨hal, hb, ha, hw⟩, ⟨ho, ho'⟩, ⟨hi, hi'⟩, hoi, hdo, hdi⟩
  janus_intro hs
  simp only [Disjoint] at hdo hdi
  simp only [FPConvention, regFP] at hfp
  rcases hoi with rfl | hoi
  all_goals try simp only [Disjoint] at hoi
  all_goals janus_run
  all_goals intro i hi4; janus_cases hi4
  all_goals janus_simp


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (0x300100) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (0x300100 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (out : BitVec 64) (inp : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [out, inp] s ∧ (FPConvention s ∧ StackOK s 88 0 ∧ Ptr s.mem out 32 true ∧ Ptr s.mem inp 32 false ∧
        (out = inp ∨ Disjoint out.toNat 32 inp.toNat 32) ∧
        Disjoint out.toNat 32 (s.sp.toNat - 88) 88 ∧ Disjoint inp.toNat 32 (s.sp.toNat - 88) 88) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (∀ i < 4, s'.mem.readLE (out.toNat + 8 * i) 8 =
        s.mem.readLE (inp.toNat + 8 * (3 - i)) 8)) := by
  refine ⟨ret, s0, (0x300000), (0x300100), hret, setup, ?pre, correctness (0x300000) (0x300100) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
