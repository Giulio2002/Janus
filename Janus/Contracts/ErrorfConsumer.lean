import Janus.Contracts.ErrorfRealFmt

/-!
# `ArgsOK` for a consumer's call of `fmt.Errorf("%w: have %d, want %d bytes", err, n1, n2)`

A program that makes this call hands `fmt.errorf` a format (26 bytes), a 3-element `[]any` (the `%w` operand, a
pointer to an errorString, then two pointers to `int` words). `argsOK_real` reduces the contract's `ArgsOK` to facts
about the call state's memory that a consumer's proof reads off the code it executed.
-/

namespace Janus.Contracts.ErrorfConsumer

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Errorf Janus.Contracts Janus.Contracts.Errorf Janus.Contracts.ErrorfRealFmt

theorem decBytes_length_le (v : Nat) (hv : v < 2 ^ 64) : (decBytes (toSigned v)).length ≤ 20 := by
  rw [decBytes_eq]
  have h1 := natBytes_length_le (absn v) 19 (by omega) (by have := natAbs_lt _ hv; unfold absn; omega)
  have h2 : (if sgn v = 1 then [45] else ([] : List Nat)).length ≤ 1 := by split <;> simp
  simp only [List.length_append]; omega

theorem argsOK_real (E : Env) (B : Nat) (m : Memory) (fp sp e tp tl q1 q2 : Nat) (hB : B < 2 ^ 40)
    (hfm : m.readLE fp 26 = fmtNum) (hfR : Readable m fp 26) (hsR : Readable m sp 48)
    (hT0 : m.readLE sp 8 = E.tErr) (he : m.readLE (sp + 8) 8 = e) (hne : e ≠ 0) (heR : Readable m e 16)
    (htp : m.readLE e 8 = tp) (htl : m.readLE (e + 8) 8 = tl) (htR : Readable m tp tl)
    (hT1 : m.readLE (sp + 16) 8 = E.tInt) (hq1 : m.readLE (sp + 24) 8 = q1) (hq1n : q1 ≠ 0)
    (hq1R : Readable m q1 8)
    (hT2 : m.readLE (sp + 32) 8 = E.tInt) (hq2 : m.readLE (sp + 40) 8 = q2) (hq2n : q2 ≠ 0)
    (hq2R : Readable m q2 8) (hlen : tl + 60 ≤ B) :
    ArgsOK E 26 fmtNum B m fp 26 sp 3 3 := by
  have hs := segsOf_real m fp 26 rfl hfm
  have hn : nDec (segsOf m fp 26) = 2 := by rw [hs]; decide
  have hfmS := fmt_strBytes m fp hfm
  have hlen' : (msgOf m fp 26 sp).length ≤ B := by
    rw [msgOf_real m fp 26 sp rfl hfm, he, htp, htl, hq1, hq2]
    have d1 := decBytes_length_le (m.readLE q1 8) (by simpa using Memory.readLE_lt m q1 8)
    have d2 := decBytes_length_le (m.readLE q2 8) (by simpa using Memory.readLE_lt m q2 8)
    simp only [List.length_append, strBytes, List.length_map, List.length_range, List.length_cons, List.length_nil]
    omega
  refine ⟨rfl, hfm, ?_, ?_, ?_, hfR, ?_, ?_, ?_, ?_, ?_, ?_, hlen', hB⟩
  · rw [hfmS, fmt_segs]; rfl
  · rw [hn]
  · exact Nat.le_refl _
  · exact hsR
  · unfold operandT; exact hT0
  · unfold operandD; rw [he]; exact hne
  · unfold operandD; rw [he]; exact heR
  · unfold operandD; rw [he, htp, htl]; exact htR
  · rw [hn]; intro j hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact ⟨by unfold operandT; exact hT1, by unfold operandD; rw [hq1]; exact hq1n, by unfold operandD; rw [hq1]; exact hq1R⟩
    · exact ⟨by unfold operandT; exact hT2, by unfold operandD; rw [hq2]; exact hq2n, by unfold operandD; rw [hq2]; exact hq2R⟩

end Janus.Contracts.ErrorfConsumer
