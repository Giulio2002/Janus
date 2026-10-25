import Extracted

/-!
# `TotalFeet(a, b Feet) uint64`: a generic function, through its dictionary

**Guarantee.** For all 64-bit `a`, `b` and every Go call state `s` of
`example.com/basic.TotalFeet` whose memory holds the function's read-only data
(`DataLoaded`: the dictionary of `total[Feet]`), whose stack-growth prologues fall through
(`GuardOK s 48`, the guard word outside the stack window) and whose `SP` is aligned with
`[SP-96, SP)` writable, the call returns (never faulting or panicking), obeys the ABI, and
`X0 = 30·(a + b) mod 2^64`: the length `a + b` feet in centimetres (30 cm to the foot).

**What is exercised.** The same shape body `total[go.shape.uint64]` as `TotalMeters.lean`
(the same code address), with a different dictionary: `TotalFeet` passes `..dict.total[Feet]`
in `X0`, whose first word is the code address of `Feet.Scale`. So the two theorems together
show both instantiations of one generic function, each reaching its own method through its
dictionary. (`Feet.Scale` is extracted with `--targets`, `scripts/example-targets.sh`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- `Feet.Scale` computes `30·f` as `(f << 5) - (f << 1)`; `lsl #5` is decoded as `ubfm` (a
rotation and a mask). -/
theorem lsl5 (a : BitVec 64) :
    (a.rotateRight 59).toNat &&& 18446744073709551584 = a.toNat * 32 % 2 ^ 64 := by
  have e : (a.rotateRight 59 &&& 18446744073709551584#64) = a <<< 5 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have : (18446744073709551584#64).getLsbD i = decide (5 ≤ i) := by
      rw [show (18446744073709551584#64) = BitVec.ofNat 64 ((2 ^ 59 - 1) * 2 ^ 5) from rfl,
        BitVec.getLsbD_ofNat, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
      simp [hi]; omega
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, this, hi]
    by_cases h : 5 ≤ i
    · have : ¬ i < 5 := by omega
      simp [h, this]
    · simp [h]
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_and, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at this
  exact this

theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b]
      (fun s => Extracted.program.DataLoaded s.mem ∧ GuardOK s 48 ∧ StackOK s 96 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 96) 96)
      (fun _ s' => (s'.regs 0).toNat = 30 * (a.toNat + b.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨hd, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgd⟩
  janus_intro hs
  simp only [Disjoint] at hgd
  janus_data hd [hw]
  janus_run
  rw [lsl5, lsl5]
  omega

end Proof
