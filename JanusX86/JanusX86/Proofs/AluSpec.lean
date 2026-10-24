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
    simp only [Sail.BitVec.toNatInt, bits_of_int_natCast_toNat, Int.ofNat_eq_coe]; omega
  rw [e]; simp <;> omega

theorem af_adc_gen (a b c : Nat) (ha : a < 16) (hb : b < 16) (hc : c < 2) :
    (15 <b Sail.BitVec.toNatInt (bits_of_int ((a : Int) + ((b : Int) + (c : Int))) 6)) = decide (a + b + c > 15) := by
  have e : Sail.BitVec.toNatInt (bits_of_int ((a : Int) + ((b : Int) + (c : Int))) 6) = ((a + b + c : Nat) : Int) := by
    rw [show ((a : Int) + ((b : Int) + (c : Int))) = ((a + b + c : Nat) : Int) by omega]
    simp only [Sail.BitVec.toNatInt, bits_of_int_natCast_toNat, Int.ofNat_eq_coe]; omega
  rw [e]; simp <;> omega

theorem af_sub_gen (a b : Nat) (ha : a < 16) (hb : b < 16) :
    ((bits_of_int ((a : Int) - (b : Int)) 5).toInt <b 0) = decide (a < b) := by
  rw [bits_of_int_toInt _ _ (by omega) (by omega)]; simp <;> omega

theorem af_sbb_gen (a b c : Nat) :
    (((a : Int) - ((b : Int) + (c : Int))) <b 0) = decide (a < b + c) := by
  simp; omega

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

end JanusX86.Proofs
