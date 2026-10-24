import Janus
import Extracted

/-!
# `F64ToU64(x float64) uint64` on amd64

**What Go emits.** SSE2 has no unsigned conversion, so Go compares `x` with `2^63` (a `.rodata`
constant, loaded with `MOVSD`), and either converts directly (`CVTTSD2SQ`), or subtracts `2^63`
(`SUBSD`), converts, and sets bit 63 (`BTSQ $63`):

```
MOVSD $2^63, X1; UCOMISD X0, X1; JBE big
CVTTSD2SQ X0, CX; JMP done
big: SUBSD X1, X0; CVTTSD2SQ X0, CX; BTSQ $63, CX
done: MOVQ CX, AX; RET
```

**Guarantee.** For every binary64 encoding `x` whose value truncated toward zero is an
integer `i` with `0 ≤ i < 2^64` (`Janus.Float.truncInt`), and every Go call state with `x` in
the low 64 bits of `X0`, `MXCSR = 0x1F80`, the constant loaded (`DataLoaded`) and 8 writable
bytes at `RSP`, the call returns, obeys the ABI, and returns `i` in `RAX`: the same result as
arm64. The proof shows that the subtraction is exact on the second path (every binary64 in
`[2^63, 2^64)` is `2^63 + fr·2^11`).

**Out of range** (read off the model; not stated by the theorem) the two architectures differ: arm64 saturates (`Proof.saturation` there), while
here a NaN or a value at or above `2^64` goes through the second path, where `CVTTSD2SQ`
returns the integer indefinite `2^63` and `BTSQ` keeps it (`0x8000000000000000`), and a
negative value below `-1` converts to its two's complement (or the indefinite, below `-2^63`).
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP

def lit : Janus.DataSegment := Extracted.data[0]
theorem lit_mem : lit ∈ Extracted.program.data := List.mem_cons_self

/-- The controls of `MXCSR = 0x1F80`. -/
abbrev c0 : Ctl := ⟨.rne, false, false⟩
theorem hc0 : IEEEMode c0 := ⟨rfl, rfl⟩

/-- `2^63` as a binary64 encoding. -/
theorem two63 : (4890909195324358656 : Nat) = 1086 * 2 ^ 52 + 0 := rfl

/-- The value of a finite `x` with a truncation `i`: its sign, significand and exponent. -/
theorem finite_of_trunc (x : Nat) (i : Int) (hi : truncInt binary64 x = some i) :
    isNaN binary64 x = false ∧
    ((classify binary64 x = .zero ∧ i = 0 ∧ valueOf binary64 x = .num 0 0) ∨
     ((classify binary64 x = .normal ∨ classify binary64 x = .subnormal) ∧
      valueOf binary64 x = .num (if signOf binary64 x then -(mantOf binary64 x : Int) else mantOf binary64 x)
        (ulpExpOf binary64 x) ∧
      i = (roundToInt .rz (signOf binary64 x) (mantOf binary64 x) (ulpExpOf binary64 x)).1)) := by
  unfold truncInt at hi
  cases h : classify binary64 x <;> simp [h] at hi
  · exact ⟨not_isNaN_of_classify h (by simp), Or.inl ⟨rfl, hi.symm, by unfold valueOf; rw [h]⟩⟩
  · exact ⟨not_isNaN_of_classify h (by simp), Or.inr ⟨Or.inr rfl, by unfold valueOf; rw [h], hi.symm⟩⟩
  · exact ⟨not_isNaN_of_classify h (by simp), Or.inr ⟨Or.inl rfl, by unfold valueOf; rw [h], hi.symm⟩⟩

theorem mant_pos (x : Nat) (h : classify binary64 x = .normal ∨ classify binary64 x = .subnormal) :
    0 < mantOf binary64 x := by
  unfold mantOf
  by_cases he : expOf binary64 x = 0
  · have : fracOf binary64 x ≠ 0 := by
      intro hf
      have : classify binary64 x = .zero := by unfold classify; simp only [he, hf, ite_true]
      rcases h with h | h <;> simp_all
    simp only [he, ite_true]; omega
  · simp only [he, ite_false]; have := Nat.two_pow_pos binary64.fbits; omega

theorem toInt_zero (f : Fmt) (c : Ctl) (rm : RM) (iw b : Nat) (e : Int)
    (h : isNaN f b = false) (hv : valOf f c b = .num 0 e) : (toInt f c rm iw b).res = 0 := by
  have hp : (0 : Int) < 2 ^ (iw - 1) := Int.pow_pos (by decide)
  unfold toInt; simp [h, hv, check]; rw [ite_eq_right (by omega)]

theorem rti_neg (m : Nat) (e : Int) : (roundToInt .rz true m e).1 ≤ 0 := by
  have : 0 ≤ (m : Int) * 2 ^ e.toNat := Int.mul_nonneg (Int.natCast_nonneg _) (Int.pow_nonneg (by decide))
  unfold roundToInt; split <;> simp <;> omega

/-- The branch for `x < 2^63`: `CVTTSD2SIQ` gives the truncation. -/
theorem branch_small (x : Nat) (i : Int) (hi : truncInt binary64 x = some i) (h0 : 0 ≤ i)
    (hnc : ¬((comis false binary64 c0 4890909195324358656 x).res % 2 = 1 ∨
      (comis false binary64 c0 4890909195324358656 x).res / 4 % 2 = 1)) :
    (toInt binary64 c0 .rz 64 x).res = i.toNat := by
  obtain ⟨hn, hcase⟩ := finite_of_trunc x i hi
  obtain ⟨hcC, -, hvC, -, -⟩ := b64_normal 1086 0 (by omega) (by omega) (by decide)
  rw [two63] at hnc
  have hnC : isNaN binary64 (1086 * 2 ^ 52 + 0) = false := not_isNaN_of_classify hcC (by simp)
  rw [comis_res hc0 binary64 false _ x hnC hn, hvC] at hnc
  have heq : Val.eq (.num ((2 ^ 52 + 0 : Nat) : Int) ((1086 : Nat) - 1075)) (valueOf binary64 x) = false := by
    cases h : Val.eq _ _ <;> simp_all
  have hlt : Val.lt (.num ((2 ^ 52 + 0 : Nat) : Int) ((1086 : Nat) - 1075)) (valueOf binary64 x) = false := by
    cases h : Val.lt _ _ <;> simp_all
  clear hnc
  rcases hcase with ⟨hz, rfl, hvx⟩ | ⟨hcl, hvx, rfl⟩
  · rw [toInt_zero binary64 c0 .rz 64 x 0 hn (by rw [valOf_ieee hc0, hvx])]; rfl
  · have hmp := mant_pos x hcl
    generalize mantOf binary64 x = m at *
    generalize ulpExpOf binary64 x = e at *
    cases hsx : signOf binary64 x
    · simp only [hsx, Bool.false_eq_true, ite_false] at hvx
      rw [hvx] at heq hlt
      have hlt' : (roundToInt .rz false m e).1 < 2 ^ 63 := by
        apply trunc_lt_of_lt
        simp only [Val.eq, Val.lt, align, show ((1086 : Nat) : Int) - 1075 = 11 from rfl,
          Int.min_comm 11 e, Nat.add_zero, decide_eq_false_iff_not, beq_eq_false_iff_ne] at heq hlt
        generalize (m : Int) * 2 ^ (e - min e 11).toNat = A at *
        generalize ((2 ^ 52 : Nat) : Int) * 2 ^ ((11 : Int) - min e 11).toNat = B at *
        omega
      try rw [hsx] at h0
      have hv' : valOf binary64 c0 x = .num (m : Int) e := by rw [valOf_ieee hc0, hvx]
      rw [toInt_num binary64 c0 .rz 64 x m e _ (roundToInt .rz false m e).2 hn hv' (by omega)
        (by rw [hsx, Int.natAbs_natCast]) (by omega) (by omega)]
      omega
    · simp only [hsx, ite_true] at hvx
      try rw [hsx] at h0
      have hle := rti_neg m e
      have hv' : valOf binary64 c0 x = .num (-(m : Int)) e := by rw [valOf_ieee hc0, hvx]
      rw [toInt_num binary64 c0 .rz 64 x (-(m : Int)) e _ (roundToInt .rz true m e).2 hn hv' (by omega)
        (by rw [hsx, Int.natAbs_neg, Int.natAbs_natCast]) (by omega) (by omega)]
      omega

theorem b64_fields (x : Nat) (hx : x < 2 ^ 64) :
    x = (if signOf binary64 x then 2 ^ 63 else 0) + expOf binary64 x * 2 ^ 52 + fracOf binary64 x ∧
    expOf binary64 x < 2 ^ 11 ∧ fracOf binary64 x < 2 ^ 52 := by
  have h63 : signOf binary64 x = decide (x / 2 ^ 63 % 2 = 1) := rfl
  have hE : expOf binary64 x = x / 2 ^ 52 % 2 ^ 11 := rfl
  have hF : fracOf binary64 x = x % 2 ^ 52 := rfl
  rw [h63, hE, hF]
  by_cases h : x / 2 ^ 63 % 2 = 1 <;> simp only [h, decide_true, decide_false, ite_true, ite_false,
    Bool.false_eq_true] <;> omega

theorem mant_lt (x : Nat) : mantOf binary64 x < 2 ^ 53 := by
  have : fracOf binary64 x < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold mantOf; rw [b64_fbits]; split <;> omega

/-- The branch for `x ≥ 2^63`: then `x` is `2^63 + fr·2^11` for a 52-bit `fr`. -/
theorem big_shape (x : Nat) (hx : x < 2 ^ 64) (i : Int) (hi : truncInt binary64 x = some i)
    (h1 : i < 2 ^ 64)
    (hc : (comis false binary64 c0 4890909195324358656 x).res % 2 = 1 ∨
      (comis false binary64 c0 4890909195324358656 x).res / 4 % 2 = 1) :
    ∃ fr, fr < 2 ^ 52 ∧ x = 1086 * 2 ^ 52 + fr ∧ i = ((2 ^ 52 + fr) * 2 ^ 11 : Nat) := by
  obtain ⟨hn, hcase⟩ := finite_of_trunc x i hi
  obtain ⟨hcC, -, hvC, -, -⟩ := b64_normal 1086 0 (by omega) (by omega) (by decide)
  rw [two63] at hc
  have hnC : isNaN binary64 (1086 * 2 ^ 52 + 0) = false := not_isNaN_of_classify hcC (by simp)
  rw [comis_res hc0 binary64 false _ x hnC hn, hvC] at hc
  have hge : Val.eq (.num ((2 ^ 52 + 0 : Nat) : Int) ((1086 : Nat) - 1075)) (valueOf binary64 x) = true ∨
      Val.lt (.num ((2 ^ 52 + 0 : Nat) : Int) ((1086 : Nat) - 1075)) (valueOf binary64 x) = true := by
    revert hc; cases Val.eq _ _ <;> cases Val.lt _ _ <;> simp
  clear hc
  rcases hcase with ⟨hz, rfl, hvx⟩ | ⟨hcl, hvx, rfl⟩
  · rw [hvx] at hge
    simp only [Val.eq, Val.lt, align, show ((1086 : Nat) : Int) - 1075 = 11 from rfl,
      Int.zero_mul, decide_eq_true_eq, beq_iff_eq] at hge
    have hP : (0 : Int) < 2 ^ ((11 : Int) - min 11 0).toNat := Int.pow_pos (by decide)
    generalize (2 : Int) ^ ((11 : Int) - min 11 0).toNat = P at *
    rcases hge with h | h <;> omega
  · have hml := mant_lt x
    obtain ⟨hdec, hEl, hFl⟩ := b64_fields x hx
    have hulp : (classify binary64 x = .subnormal → ulpExpOf binary64 x = -1074) ∧
        (classify binary64 x = .normal → ulpExpOf binary64 x = (expOf binary64 x : Int) - 1075 ∧
          mantOf binary64 x = 2 ^ 52 + fracOf binary64 x ∧ 1 ≤ expOf binary64 x) := by
      constructor <;> intro hk
      · have he0 : expOf binary64 x = 0 := by
          apply Classical.byContradiction; intro he
          unfold classify at hk; simp only [he, ite_false] at hk
          split at hk <;> (try split at hk) <;> (try split at hk) <;> simp at hk
        unfold ulpExpOf; rw [he0, b64_emin, b64_fbits]; rfl
      · have he0 : expOf binary64 x ≠ 0 := by
          intro h; unfold classify at hk; simp [h] at hk; split at hk <;> simp at hk
        unfold ulpExpOf mantOf; rw [b64_bias, b64_fbits]
        simp only [he0, ite_false]; refine ⟨by omega, ?_, by omega⟩; simp
    cases hsx : signOf binary64 x
    · simp only [hsx, Bool.false_eq_true, ite_false] at hvx hdec
      rw [hvx] at hge
      have hnot : ¬ ((mantOf binary64 x : Int) * 2 ^ (ulpExpOf binary64 x - min (ulpExpOf binary64 x) 11).toNat <
          ((2 ^ 52 : Nat) : Int) * 2 ^ ((11 : Int) - min (ulpExpOf binary64 x) 11).toNat) := by
        simp only [Val.eq, Val.lt, align, show ((1086 : Nat) : Int) - 1075 = 11 from rfl,
          Int.min_comm 11 (ulpExpOf binary64 x), Nat.add_zero, decide_eq_true_eq, beq_iff_eq] at hge
        generalize (mantOf binary64 x : Int) * 2 ^ (ulpExpOf binary64 x - min (ulpExpOf binary64 x) 11).toNat = A at *
        generalize ((2 ^ 52 : Nat) : Int) * 2 ^ ((11 : Int) - min (ulpExpOf binary64 x) 11).toNat = B at *
        omega
      have h11 := e_ge_of_not_lt _ _ hml hnot
      rcases hcl with hk | hk
      · obtain ⟨hu, hmant, hE1⟩ := hulp.2 hk
        have hle : ulpExpOf binary64 x ≤ 11 := by
          apply Classical.byContradiction; intro hgt
          have := trunc_ge (mantOf binary64 x) (ulpExpOf binary64 x) (by omega) (by omega)
          rw [hsx] at h1; omega
        have hE : expOf binary64 x = 1086 := by omega
        refine ⟨fracOf binary64 x, hFl, by omega, ?_⟩
        rw [show ulpExpOf binary64 x = 11 by omega, hmant]
        unfold roundToInt; simp
      · have := hulp.1 hk; omega
    · simp only [hsx, ite_true] at hvx
      rw [hvx] at hge
      simp only [Val.eq, Val.lt, align, decide_eq_true_eq, beq_iff_eq] at hge
      have hp : (0 : Int) ≤ (mantOf binary64 x : Int) *
          2 ^ (ulpExpOf binary64 x - min (((1086 : Nat) : Int) - 1075) (ulpExpOf binary64 x)).toNat :=
        Int.mul_nonneg (Int.natCast_nonneg _) (Int.pow_nonneg (by decide))
      have hq : (0 : Int) < ((2 ^ 52 + 0 : Nat) : Int) *
          2 ^ (((1086 : Nat) : Int) - 1075 - min (((1086 : Nat) : Int) - 1075) (ulpExpOf binary64 x)).toNat :=
        Int.mul_pos (by omega) (Int.pow_pos (by decide))
      simp only [Int.neg_mul, decide_eq_true_eq] at hge
      generalize (mantOf binary64 x : Int) *
          2 ^ (ulpExpOf binary64 x - min (((1086 : Nat) : Int) - 1075) (ulpExpOf binary64 x)).toNat = A at *
      generalize ((2 ^ 52 + 0 : Nat) : Int) *
          2 ^ (((1086 : Nat) : Int) - 1075 - min (((1086 : Nat) : Int) - 1075) (ulpExpOf binary64 x)).toNat = B at *
      omega

theorem correctness (x : BitVec 64) (i : Int) (hi : truncInt binary64 x.toNat = some i)
    (h0 : 0 ≤ i) (h1 : i < 2 ^ 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ Extracted.program.DataLoaded s.mem ∧
        (s.xmm 0).toNat % 2 ^ 64 = x.toNat ∧ s.mxcsr = 0x1F80)
      (fun _ s' => (results 1 s').map BitVec.toNat = [i.toNat]) := by
  intro ret hret s hs ⟨hst, hdl, hx, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  have hrd := DataLoaded.accessible hdl lit_mem
  have hlen : lit.bytes.length = 8 := by decide
  have hb : lit.base = 0x4b5ef0 := rfl
  rw [hlen, hb] at hrd
  have hc := DataLoaded.readLE hdl lit_mem 0 8 (by rw [hlen]; omega)
  rw [hb, show listLE (lit.bytes.drop 0) 8 = 0x43e0000000000000 by decide] at hc
  janus64_run [hx, hm]
  all_goals first
    | (rw [branch_small x.toNat i hi h0 (by assumption)]; simp; omega)
    | skip
  all_goals
    obtain ⟨fr, hfr, hxeq, hieq⟩ := big_shape x.toNat x.isLt i hi h1 (by assumption)
    rw [hxeq, two63, binop_sub_2p63 hc0 fr hfr]
    have hlt : ∀ y : Nat, y < 2 ^ 64 → ∀ q, (q * 18446744073709551616 + y % 18446744073709551616) %
        18446744073709551616 = y := fun y hy q => by omega
    by_cases hf0 : fr = 0
    · subst hf0
      rw [hlt _ (by decide)]
      have hz : (toInt binary64 c0 .rz 64 (zero binary64 (decide (c0.rc = RM.rmi)))).res = 0 := by
        decide +kernel
      simp only [ite_true, hz, hieq]
      decide +kernel
    · simp only [hf0, ite_false]
      rw [hlt _ (round_bits_lt _ _ _ _ _), round_exact64 .rne fr (by omega) hfr,
        toInt_exact64 c0 hc0 fr (by omega) hfr, hieq]
      have hb : fr * 2 ^ 11 < 2 ^ 63 := by omega
      have : (BitVec.ofNat 64 (fr * 2 ^ 11) ||| (9223372036854775808 : BitVec 64)).toNat =
          fr * 2 ^ 11 + 2 ^ 63 := by
        rw [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact Nat.or_two_pow_eq_add_of_lt hb
      simp only [List.cons.injEq, and_true]
      rw [show ((9223372036854775808 : Nat) : BitVec 64) = 9223372036854775808 from rfl, this]
      omega

end Proof
