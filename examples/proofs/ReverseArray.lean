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

end Proof
