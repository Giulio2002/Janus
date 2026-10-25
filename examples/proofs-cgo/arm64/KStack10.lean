import Extracted

/-!
# `int64_t k_stack10(a, b, c, d, e, f, g, h, int32_t i, j)` (C, arm64): stack arguments

**Guarantee.** For all 64-bit `a … h`, `j` and 32-bit `i`, every AAPCS64 call of the
gcc-compiled `k_stack10` whose arguments are where the classification of its prototype puts
them (`CCallA`: `a`–`h` in `X0`–`X7`, `i` in the low half of the first stacked slot `[SP]`, `j` in
the second `[SP + 8]`; Janus.C.AAPCS64) returns, restores `SP`, `X19`–`X29`, `D8`–`D15` and
`FPCR` (`CReturn`), and returns in `X0` the value
`a + 2b + 3c + 4d + 5e + 6f + 7g + 8h + 9i + 10j` (mod 2^64, `i` sign-extended).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.C

namespace Proof

/-- The prototype. -/
def sig : AAPCS64.Sig :=
  ⟨some (.int 8 true), List.replicate 8 (.int 8 true) ++ [.int 4 true, .int 8 true], none⟩

/-- Where Janus's classification puts the arguments. -/
theorem passing : sig.passing =
    ((List.range 8).map fun r => .direct [⟨0, 8, .gpr r⟩]) ++
      [.direct [⟨0, 4, .stack 0⟩], .direct [⟨0, 8, .stack 8⟩]] := by decide

/-- The result is `X0`. -/
theorem result : AAPCS64.result (.int 8 true) = .direct [⟨0, 8, .gpr 0⟩] := by decide

/-- The specification. -/
def spec (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) : BitVec 64 :=
  a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9 * i.signExtend 64 + 10 * j

theorem correctness (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) :
    CEnsuresR Extracted.program Extracted.entry sig
      ([a, b, c, d, e, f, g, h].map BitVec.toNat ++ [i.toNat, j.toNat]) (fun _ => True)
      (fun _ _ v => v = (spec a b c d e f g h i j).toNat) := by
  intro ret hret s hs _
  have hpc := hs.pc
  have hlr := hs.lr
  have ha := hs.args
  rw [passing] at ha
  simp only [sig, List.map, List.range, List.range.loop, List.cons_append, List.nil_append,
    ArgsAt, ArgAt, PiecesAt, and_true, List.replicate] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hi, hj⟩ := ha
  rw [pieceAt_gpr_word] at h0 h1 h2 h3 h4 h5 h6 h7
  rw [pieceAt_stack_word] at hj
  obtain ⟨hjb, hja, hj⟩ := hj
  simp only [PieceAt, bytesOf, Nat.pow_zero, Nat.div_one, Nat.add_zero] at hi hja hj hjb
  obtain ⟨hib, hia, hi⟩ := hi
  simp only [Program.withExit] at hlr
  have hal := hs.spAligned
  janus_run
  refine ⟨_, ?_, rfl⟩
  simp only [Returned, sig, result, ResultAt, PiecesAt, and_true, pieceAt_gpr_word,
    setReg_apply, ↓reduceIte, Nat.reduceEqDiff]
  have hi' : s.mem.readLE s.sp.toNat 4 = i.toNat := by
    rw [hi]; exact Nat.mod_eq_of_lt i.isLt
  rw [hi', hj]
  have hw : BitVec.setWidth 32 (BitVec.ofNat 64 i.toNat) = i := by
    apply BitVec.eq_of_toNat_eq; simp
  have hse : BitVec.ofInt 64 i.toInt = i.signExtend 64 := by
    rw [← BitVec.toInt_signExtend_of_le (x := i) (v := 64) (by decide), BitVec.ofInt_toInt]
  rw [hw, BitVec.ofInt_add, BitVec.ofInt_mul, hse, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [spec, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, BitVec.reduceToNat, Nat.add_mod_mod, Nat.mod_add_mod,
    Nat.mod_mul_mod, show (BitVec.ofInt 64 9).toNat = 9 from rfl]
  generalize (i.signExtend 64).toNat = I
  omega

end Proof
