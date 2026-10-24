import JanusX86.Proofs.Arith

/-! # The model's ALU flag specifications against Janus' `addFlags`/`subFlags`/`logicFlags` -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- A Janus flag as a model flag bit (an undefined flag as 0; never used where it is undefined). -/
def fbit (o : Option Bool) : BitVec 1 := BitVec.ofBool (o.getD false)

/-- The output flag vector of an arithmetic spec: all six status flags written. -/
def outArith (rin : BitVec 32) (f : Janus.Amd64.Flags) : BitVec 32 :=
  _update_rflagsbits_of (_update_rflagsbits_sf (_update_rflagsbits_zf (_update_rflagsbits_af
    (_update_rflagsbits_pf (_update_rflagsbits_cf rin (fbit f.cf)) (fbit f.pf)) (fbit f.af))
    (fbit f.zf)) (fbit f.sf)) (fbit f.ovf)

/-- The output flag vector of a logical spec: `AF` not written (it is in the undefined mask). -/
def outLogic (rin : BitVec 32) (f : Janus.Amd64.Flags) : BitVec 32 :=
  _update_rflagsbits_of (_update_rflagsbits_sf (_update_rflagsbits_zf
    (_update_rflagsbits_pf (_update_rflagsbits_cf rin (fbit f.cf)) (fbit f.pf))
    (fbit f.zf)) (fbit f.sf)) (fbit f.ovf)

theorem outArith_some (rin : BitVec 32) (a b c d e f : Bool) :
    outArith rin ⟨some a, some b, some c, some d, some e, some f⟩ =
      _update_rflagsbits_of (_update_rflagsbits_sf (_update_rflagsbits_zf (_update_rflagsbits_af
        (_update_rflagsbits_pf (_update_rflagsbits_cf rin (BitVec.ofBool a)) (BitVec.ofBool b)) (BitVec.ofBool c))
        (BitVec.ofBool d)) (BitVec.ofBool e)) (BitVec.ofBool f) := rfl

theorem outLogic_some (rin : BitVec 32) (a b d e f : Bool) (c : Option Bool) :
    outLogic rin ⟨some a, some b, c, some d, some e, some f⟩ =
      _update_rflagsbits_of (_update_rflagsbits_sf (_update_rflagsbits_zf
        (_update_rflagsbits_pf (_update_rflagsbits_cf rin (BitVec.ofBool a)) (BitVec.ofBool b))
        (BitVec.ofBool d)) (BitVec.ofBool e)) (BitVec.ofBool f) := rfl

theorem bool_to_bits_eq (b : Bool) : bool_to_bits b = BitVec.ofBool b := by cases b <;> rfl

theorem bool_to_bits_of (b c : Bool) (h : b = c) : bool_to_bits b = BitVec.ofBool c := by
  subst h; cases b <;> rfl

theorem parityBits_mod : ∀ (k x : Nat), Janus.Amd64.parityBits k x = Janus.Amd64.parityBits k (x % 2 ^ k)
  | 0, _ => rfl
  | k + 1, x => by
    simp only [Janus.Amd64.parityBits]
    have h1 : x % 2 ^ (k + 1) % 2 = x % 2 := by rw [Nat.pow_succ', Nat.mod_mul_right_mod]
    have h2 : x % 2 ^ (k + 1) / 2 = x / 2 % 2 ^ k := by
      rw [Nat.pow_succ', Nat.mod_mul_right_div_self]
    rw [h1, h2, parityBits_mod k (x / 2)]

theorem parity_mod256 (x : Nat) : Janus.Amd64.parity (x % 256) = Janus.Amd64.parity x := by
  simp only [Janus.Amd64.parity]
  rw [parityBits_mod 8 x]

theorem extractLsb_one_eq_ofBool {w : Nat} (x : BitVec w) (i : Nat) :
    x.extractLsb i i = (BitVec.ofBool (x.getLsbD i)).setWidth _ := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have : k = 0 := by omega
  subst this
  simp

theorem toNatInt_extract30 {w : Nat} (x : BitVec w) :
    Sail.BitVec.toNatInt (Sail.BitVec.extractLsb x 3 0) = ((x.toNat % 16 : Nat) : Int) := by
  simp [Sail.BitVec.toNatInt, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat]

theorem af_add_gen (a b : Nat) (ha : a < 16) (hb : b < 16) :
    (15 <b Sail.BitVec.toNatInt (bits_of_int ((a : Int) + (b : Int)) 5)) = decide (a + b > 15) := by
  have e : Sail.BitVec.toNatInt (bits_of_int ((a : Int) + (b : Int)) 5) = ((a + b : Nat) : Int) := by
    rw [show ((a : Int) + (b : Int)) = ((a + b : Nat) : Int) by omega]
    simp only [Sail.BitVec.toNatInt, bits_of_int_natCast_toNat, Int.ofNat_eq_natCast]; omega
  rw [e]; simp <;> omega

theorem af_adc_gen (a b c : Nat) (ha : a < 16) (hb : b < 16) (hc : c < 2) :
    (15 <b Sail.BitVec.toNatInt (bits_of_int ((a : Int) + ((b : Int) + (c : Int))) 6)) = decide (a + b + c > 15) := by
  have e : Sail.BitVec.toNatInt (bits_of_int ((a : Int) + ((b : Int) + (c : Int))) 6) = ((a + b + c : Nat) : Int) := by
    rw [show ((a : Int) + ((b : Int) + (c : Int))) = ((a + b + c : Nat) : Int) by omega]
    simp only [Sail.BitVec.toNatInt, bits_of_int_natCast_toNat, Int.ofNat_eq_natCast]; omega
  rw [e]; simp <;> omega

theorem af_sub_gen (a b : Nat) (ha : a < 16) (hb : b < 16) :
    ((bits_of_int ((a : Int) - (b : Int)) 5).toInt <b 0) = decide (a < b) := by
  rw [bits_of_int_toInt _ _ (by omega) (by omega)]; simp <;> omega

theorem af_sbb_gen (a b c : Nat) :
    (((a : Int) - ((b : Int) + (c : Int))) <b 0) = decide (a < b + c) := by
  simp; omega

theorem zf_spec_eq {w : Nat} (r : BitVec w) :
    zf_spec (Sail.BitVec.toNatInt r).toNat = BitVec.ofBool (decide (r.toNat = 0)) := by
  simp only [zf_spec, Sail.BitVec.toNatInt, Int.toNat_natCast]
  by_cases h : r.toNat = 0 <;> simp [h]

theorem raw_add_toNat {w : Nat} (x y : BitVec w) (c : Nat) (hc : c < 2) :
    (bits_of_int (Sail.BitVec.toNatInt x + (Sail.BitVec.toNatInt y + (c : Int))) (w + 1)).toNat = x.toNat + y.toNat + c := by
  rw [show Sail.BitVec.toNatInt x + (Sail.BitVec.toNatInt y + (c : Int)) = ((x.toNat + y.toNat + c : Nat) : Int) by
    simp [Sail.BitVec.toNatInt]; omega, bits_of_int_natCast_toNat]
  have := x.isLt; have := y.isLt
  apply Nat.mod_eq_of_lt; rw [Nat.pow_succ]; omega

theorem raw_add_toNat' {w : Nat} (x y : BitVec w) :
    (bits_of_int (Sail.BitVec.toNatInt x + Sail.BitVec.toNatInt y) (w + 1)).toNat = x.toNat + y.toNat := by
  have := raw_add_toNat x y 0 (by decide)
  simpa using this

theorem trunc_raw {w : Nat} (v : BitVec (w + 1)) (n : Nat) (h : v.toNat = n) :
    Sail.BitVec.truncate v w = BitVec.ofNat w n := by
  apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate, h]

theorem sraw_toInt {w : Nat} (hw : 0 < w) (x y : BitVec w) (c : Int) (hc : 0 ≤ c ∧ c ≤ 1) :
    (bits_of_int (x.toInt + (y.toInt + c)) (w + 1)).toInt = x.toInt + y.toInt + c := by
  have h1 := BitVec.le_two_mul_toInt (x := x); have h2 := BitVec.two_mul_toInt_lt (x := x)
  have h3 := BitVec.le_two_mul_toInt (x := y); have h4 := BitVec.two_mul_toInt_lt (x := y)
  have hp : (2 : Int) ^ (w + 1) = 2 * 2 ^ w := by rw [Int.pow_succ]; omega
  have hpe : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
    rw [show w = (w - 1) + 1 by omega, Int.pow_succ]; simp; omega
  rw [bits_of_int_toInt _ _ (by push_cast; omega) (by push_cast; omega)]; omega

theorem trunc_bits_ofInt (v : Int) (w k : Nat) :
    Sail.BitVec.truncate (bits_of_int v (w + k)) w = BitVec.ofInt w v := by
  rw [bits_of_int_eq_ofInt]
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.BitVec.truncate, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have h1 : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)
  have hd : ((2 ^ w : Nat) : Int) ∣ ((2 ^ (w + k) : Nat) : Int) := by
    rw [Nat.pow_add]; exact Int.natCast_dvd_natCast.mpr (Nat.dvd_mul_right _ _)
  have ha : 0 ≤ v % ((2 ^ (w + k) : Nat) : Int) :=
    Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)))
  obtain ⟨a, ha'⟩ := Int.eq_ofNat_of_zero_le ha
  rw [ha', Int.toNat_natCast]
  have e : (a : Int) % ((2 ^ w : Nat) : Int) = v % ((2 ^ w : Nat) : Int) := by
    rw [← ha', Int.emod_emod_of_dvd _ hd]
  rw [← e, ← Int.natCast_emod, Int.toNat_natCast]

theorem toInt_bits_small (v : Int) (n : Nat) (h1 : -(2 ^ n : Int) ≤ 2 * v) (h2 : 2 * v < 2 ^ n) (k : Nat) :
    (Sail.BitVec.truncate (bits_of_int v (n + k)) n).toInt = v := by
  rw [trunc_bits_ofInt, ← bits_of_int_eq_ofInt]
  exact bits_of_int_toInt v n h1 h2

theorem toInt_bounds {w : Nat} (hw : 0 < w) (x : BitVec w) :
    -(2 ^ w : Int) ≤ 2 * x.toInt ∧ 2 * x.toInt < 2 ^ w :=
  ⟨by have := BitVec.le_two_mul_toInt (x := x); push_cast at this; omega,
   by have := BitVec.two_mul_toInt_lt (x := x); push_cast at this; omega⟩

theorem pow_succ_int (w : Nat) : (2 : Int) ^ (w + 1) = 2 * 2 ^ w := by rw [Int.pow_succ]; omega

theorem pow_pred_int {w : Nat} (hw : 0 < w) : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
  rw [show w = (w - 1) + 1 by omega, Int.pow_succ]; simp; omega

theorem toNatInt_ofBool (c : Bool) : Sail.BitVec.toNatInt (BitVec.ofBool c) = ((c.toNat : Nat) : Int) := by
  cases c <;> rfl

open Janus.Amd64 in
theorem logicFlags_eq {w : Nat} (r : BitVec w) :
    logicFlags r = (Janus.Amd64.Flags.mk (some false) (some (parity r.toNat)) none
      (some (decide (r.toNat = 0))) (some (decide (2 ^ (w - 1) ≤ r.toNat))) (some false)) := by
  simp only [logicFlags, BitVec.msb_eq_decide, Janus.Amd64.Flags.mk.injEq, Option.some.injEq, true_and, and_true]
  rw [decide_eq_decide, BitVec.toNat_eq]; simp

/-! ## Janus' flag functions as closed formulas -/

theorem toInt_ofInt_ne_iff {w : Nat} (hw : 0 < w) (v : Int) :
    ((BitVec.ofInt w v).toInt ≠ v) ↔ ¬(-(2 ^ (w - 1) : Int) ≤ v ∧ v < 2 ^ (w - 1)) := by
  have hp : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
    rw [show w = (w - 1) + 1 by omega, Int.pow_succ]; simp; omega
  have hp' : ((2 ^ w : Nat) : Int) = 2 * 2 ^ (w - 1) := by push_cast; exact hp
  rw [BitVec.toInt_ofInt]
  constructor
  · intro hne ⟨h1, h2⟩
    exact hne (Int.bmod_eq_of_le_mul_two (by omega) (by omega))
  · intro hn heq
    have h1 := @Int.le_bmod v (2 ^ w) (Nat.two_pow_pos w)
    have h2 := @Int.bmod_lt v (2 ^ w) (Nat.two_pow_pos w)
    rw [heq] at h1 h2
    apply hn
    have e1 : (((2 ^ w : Nat) : Int) / 2) = 2 ^ (w - 1) := by rw [hp']; omega
    have e2 : ((((2 ^ w : Nat) : Int) + 1) / 2) = 2 ^ (w - 1) := by rw [hp']; omega
    simp only [Int.natCast_pow] at e1 e2 h1 h2
    constructor <;> omega

theorem ofNat_add3 {w : Nat} (x y : BitVec w) (c : Nat) :
    BitVec.ofNat w (x.toNat + y.toNat + c) = BitVec.ofInt w (x.toInt + y.toInt + c) := by
  have h1 : BitVec.ofNat w (x.toNat + y.toNat + c) = x + y + BitVec.ofNat w c := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
    rw [Nat.add_mod (x.toNat + y.toNat), Nat.add_mod x.toNat]
  rw [h1, BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt, BitVec.ofInt_natCast]

theorem ofInt_sub' {w : Nat} (a b : Int) : BitVec.ofInt w (a - b) = BitVec.ofInt w a - BitVec.ofInt w b := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem ofNat_sub3 {w : Nat} (x y : BitVec w) (b : Nat) (hb : b ≤ 1) :
    BitVec.ofNat w (x.toNat + 2 ^ w - y.toNat - b) = BitVec.ofInt w (x.toInt - y.toInt - b) := by
  have hy := y.isLt
  rw [← BitVec.ofInt_natCast]
  have e : ((x.toNat + 2 ^ w - y.toNat - b : Nat) : Int) = (x.toNat : Int) + ((2 ^ w : Nat) : Int) - y.toNat - b := by
    omega
  have z : BitVec.ofInt w ((2 ^ w : Nat) : Int) = 0#w := by
    rw [BitVec.ofInt_natCast]; apply BitVec.eq_of_toNat_eq; simp
  rw [e, ofInt_sub', ofInt_sub', BitVec.ofInt_add, z, BitVec.add_zero, ofInt_sub', ofInt_sub',
    BitVec.ofInt_toInt, BitVec.ofInt_toInt, BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
    BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq]

open Janus.Amd64 in
theorem addFlags_eq {w : Nat} (hw : 5 ≤ w) (x y : BitVec w) (c : Bool) :
    addFlags x y c =
      (BitVec.ofNat w (x.toNat + y.toNat + c.toNat),
       { cf := some (decide (x.toNat + y.toNat + c.toNat ≥ 2 ^ w)),
         pf := some (parity ((x.toNat + y.toNat + c.toNat) % 2 ^ w)),
         af := some (decide (x.toNat % 16 + y.toNat % 16 + c.toNat > 15)),
         zf := some (decide ((x.toNat + y.toNat + c.toNat) % 2 ^ w = 0)),
         sf := some (decide (2 ^ (w - 1) ≤ (x.toNat + y.toNat + c.toNat) % 2 ^ w)),
         ovf := some (decide ¬(-(2 ^ (w - 1) : Int) ≤ x.toInt + y.toInt + c.toNat ∧
           x.toInt + y.toInt + c.toNat < 2 ^ (w - 1))) }) := by
  simp only [addFlags, auxCarry, Prod.mk.injEq, true_and, Janus.Amd64.Flags.mk.injEq, Option.some.injEq]
  refine ⟨by rw [BitVec.toNat_ofNat], ?_, ?_, ?_, ?_⟩
  · simp only [BitVec.toNat_xor, BitVec.toNat_ofNat]
    have := af_add_nat x.toNat y.toNat c.toNat w (by cases c <;> decide) hw
    rw [Bool.eq_iff_iff] at this ⊢
    simp only [beq_iff_eq] at this
    simp only [decide_eq_true_eq]
    exact this.trans (by simp)
  · rw [decide_eq_decide, BitVec.toNat_eq, BitVec.toNat_ofNat]; simp
  · rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
  · rw [ofNat_add3, decide_eq_decide]
    exact toInt_ofInt_ne_iff (by omega) _

open Janus.Amd64 in
theorem subFlags_eq {w : Nat} (hw : 5 ≤ w) (x y : BitVec w) (b : Bool) :
    subFlags x y b =
      (BitVec.ofNat w (x.toNat + 2 ^ w - y.toNat - b.toNat),
       { cf := some (decide (x.toNat < y.toNat + b.toNat)),
         pf := some (parity ((x.toNat + 2 ^ w - y.toNat - b.toNat) % 2 ^ w)),
         af := some (decide (x.toNat % 16 < y.toNat % 16 + b.toNat)),
         zf := some (decide ((x.toNat + 2 ^ w - y.toNat - b.toNat) % 2 ^ w = 0)),
         sf := some (decide (2 ^ (w - 1) ≤ (x.toNat + 2 ^ w - y.toNat - b.toNat) % 2 ^ w)),
         ovf := some (decide ¬(-(2 ^ (w - 1) : Int) ≤ x.toInt - y.toInt - b.toNat ∧
           x.toInt - y.toInt - b.toNat < 2 ^ (w - 1))) }) := by
  simp only [subFlags, auxCarry, Prod.mk.injEq, true_and, Janus.Amd64.Flags.mk.injEq, Option.some.injEq]
  refine ⟨by rw [BitVec.toNat_ofNat], ?_, ?_, ?_, ?_⟩
  · simp only [BitVec.toNat_xor, BitVec.toNat_ofNat]
    have := af_sub_nat x.toNat y.toNat b.toNat w (by cases b <;> decide) hw y.isLt
    rw [Bool.eq_iff_iff] at this ⊢
    simp only [beq_iff_eq] at this
    simp only [decide_eq_true_eq]
    exact this.trans (by simp)
  · rw [decide_eq_decide, BitVec.toNat_eq, BitVec.toNat_ofNat]; simp
  · rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
  · rw [ofNat_sub3 _ _ _ (by cases b <;> decide), decide_eq_decide]
    exact toInt_ofInt_ne_iff (by omega) _

theorem addFlags_fst' {w : Nat} (hw : 5 ≤ w) (x y : BitVec w) (c : Bool) :
    (Janus.Amd64.addFlags x y c).1 = BitVec.ofNat w (x.toNat + y.toNat + c.toNat) := by
  rw [addFlags_eq hw]

theorem addFlags_snd' {w : Nat} (hw : 5 ≤ w) (x y : BitVec w) (c : Bool) :
    (Janus.Amd64.addFlags x y c).2 =
       { cf := some (decide (x.toNat + y.toNat + c.toNat ≥ 2 ^ w)),
         pf := some (Janus.Amd64.parity ((x.toNat + y.toNat + c.toNat) % 2 ^ w)),
         af := some (decide (x.toNat % 16 + y.toNat % 16 + c.toNat > 15)),
         zf := some (decide ((x.toNat + y.toNat + c.toNat) % 2 ^ w = 0)),
         sf := some (decide (2 ^ (w - 1) ≤ (x.toNat + y.toNat + c.toNat) % 2 ^ w)),
         ovf := some (decide ¬(-(2 ^ (w - 1) : Int) ≤ x.toInt + y.toInt + c.toNat ∧
           x.toInt + y.toInt + c.toNat < 2 ^ (w - 1))) } := by
  rw [addFlags_eq hw]

theorem subFlags_fst' {w : Nat} (hw : 5 ≤ w) (x y : BitVec w) (b : Bool) :
    (Janus.Amd64.subFlags x y b).1 = BitVec.ofNat w (x.toNat + 2 ^ w - y.toNat - b.toNat) := by
  rw [subFlags_eq hw]

theorem subFlags_snd' {w : Nat} (hw : 5 ≤ w) (x y : BitVec w) (b : Bool) :
    (Janus.Amd64.subFlags x y b).2 =
       { cf := some (decide (x.toNat < y.toNat + b.toNat)),
         pf := some (Janus.Amd64.parity ((x.toNat + 2 ^ w - y.toNat - b.toNat) % 2 ^ w)),
         af := some (decide (x.toNat % 16 < y.toNat % 16 + b.toNat)),
         zf := some (decide ((x.toNat + 2 ^ w - y.toNat - b.toNat) % 2 ^ w = 0)),
         sf := some (decide (2 ^ (w - 1) ≤ (x.toNat + 2 ^ w - y.toNat - b.toNat) % 2 ^ w)),
         ovf := some (decide ¬(-(2 ^ (w - 1) : Int) ≤ x.toInt - y.toInt - b.toNat ∧
           x.toInt - y.toInt - b.toNat < 2 ^ (w - 1))) } := by
  rw [subFlags_eq hw]

end JanusX86.Proofs
