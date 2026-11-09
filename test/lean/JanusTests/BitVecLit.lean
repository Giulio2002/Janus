import Janus

/-!
# Bit-vector literals in executor states (U-BVLIT)

`janus64_intro` states `h_x15 : s.xmm 15 = 0` with the literal exactly as the elaborator writes
`(0 : BitVec 128)` (a raw numeral inside `OfNat.ofNat`; it used to apply `OfNat.ofNat` to an
`OfNat.ofNat Nat 0 _` numeral, a different term), so it is syntactically the `0` of a callee's
precondition or of a statement; and `toNat` of such a literal, in either form, reduces in the simp sets
(`bv_toNat_lit`: the core lemmas `BitVec.toNat_zero`/`toNat_ofNat` are about `0#w`/`BitVec.ofNat` and do not
fire on the `OfNat` literal).
-/

namespace JanusTests.BitVecLit

open Janus Janus.Tactic Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec

-- `toNat` of a literal, both ISAs' simp sets, canonical and numeral-wrapped forms
example : (0 : BitVec 128).toNat = 0 := by simp only [janus_post, Nat.reducePow, Nat.zero_mod]
example : (7 : BitVec 64).toNat = 7 := by simp only [janus_post, Nat.reducePow, Nat.reduceMod]
example : BitVec.toNat (OfNat.ofNat 0 : BitVec 128) = 0 := by
  simp only [janus_post, Nat.reducePow, Nat.zero_mod]
example : (0 : BitVec 128).toNat = 0 := by simp only [janus64_post, Nat.reducePow, Nat.zero_mod]
example : BitVec.toNat (OfNat.ofNat 0 : BitVec 128) = 0 := by simp only [janus64_post, Nat.reducePow, Nat.zero_mod]

def zq : Janus.Amd64.Program where
  segments := [⟨"zq", 0x1000, [0xc3]⟩]
  stubs := []
  exitAddr := 0

-- `h_x15` is the canonical literal: it closes a goal `s.xmm 15 = 0` at reducible transparency (the
-- discharger of a callee's precondition) and `toNat` of it reduces with the post simp set.
example (p : BitVec 64) :
    Ensures zq 0x1000 [p] (fun s => StackWritable s 0 8) (fun _ _ => True) := by
  intro ret hret s hs ⟨hle, hnw, hacc⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  have a : s.xmm 15 = 0 := by with_reducible assumption
  have b : s.xmm 15 = 0 := by with_reducible exact h_x15
  have c : (s.xmm 15).toNat = 0 := by simp only [h_x15, janus64_post, Nat.reducePow, Nat.zero_mod]
  have d : (s.xmm 15).toNat + (s.xmm 14).toNat = (s.xmm 14).toNat := by
    rw [h_x15]; simp only [janus64_post, Nat.reducePow, Nat.zero_mod, Nat.zero_add]
  -- the term is the elaborated literal, so omega sees one atom for every occurrence
  have e : (s.xmm 15).toNat = (0 : BitVec 128).toNat := by rw [h_x15]
  janus64_run

end JanusTests.BitVecLit
