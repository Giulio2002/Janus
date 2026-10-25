import Extracted

/-!
# `SwapBig(a, b *Big)`: struct assignment by value (a 64-byte struct)

**Guarantee.** For all pointers `a`, `b` to 64 writable bytes (the eight-word struct `Big`) that
are either the same struct or disjoint, both disjoint from the function's stack window
(`[SP-88, SP)`), and every Go call state of `example.com/basic.SwapBig` satisfying Go's
frame-pointer invariant (`FPConvention`: `X29` is restored arithmetically), the call returns
(never faulting or panicking), obeys the ABI, and afterwards every word `i < 8` of `*a` is word
`i` of `*b` before the call and vice versa. For `a = b` this says the struct is unchanged.

`*a, *b = *b, *a` evaluates both right-hand sides first: the compiler copies `*a` into a frame
temporary (four `ldp`/`stp` pairs), copies `*b` over `*a`, then the temporary over `*b`. No
`memmove` or `duffcopy` is involved.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b]
      (fun s => FPConvention s ∧ StackOK s 88 0 ∧ Ptr s.mem a 64 true ∧ Ptr s.mem b 64 true ∧
        (a = b ∨ Disjoint a.toNat 64 b.toNat 64) ∧
        Disjoint a.toNat 64 (s.sp.toNat - 88) 88 ∧ Disjoint b.toNat 64 (s.sp.toNat - 88) 88)
      (fun s s' => ∀ i < 8, s'.mem.readLE (a.toNat + 8 * i) 8 = s.mem.readLE (b.toNat + 8 * i) 8 ∧
        s'.mem.readLE (b.toNat + 8 * i) 8 = s.mem.readLE (a.toNat + 8 * i) 8) := by
  intro ret hret s hs ⟨hfp, ⟨hal, hsb, hsa, hw⟩, ⟨ha, ha'⟩, ⟨hb, hb'⟩, hab, hda, hdb⟩
  janus_intro hs
  simp only [Disjoint] at hda hdb
  simp only [FPConvention, regFP] at hfp
  rcases hab with rfl | hab
  all_goals try simp only [Disjoint] at hab
  all_goals janus_run
  all_goals intro i hi8; janus_cases hi8
  all_goals janus_simp

end Proof
