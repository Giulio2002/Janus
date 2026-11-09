import JanusX86.Proofs.Branch

/-! # The model's shift/rotate specifications against Janus' `execShift` -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64

/-- Janus' `execShift` result and flags for a masked count `c` (a copy of its body). -/
def shRes (op : ShOp) {w : Nat} (x : BitVec w) (c : Nat) (f : Flags) : BitVec w × Flags :=
  if c = 0 then
    (x, match op with
      | .rol | .ror => { f with ovf := none }
      | _ => f)
  else
  let szp (r : BitVec w) (cf of : Option Bool) : Flags :=
    { cf := cf, pf := some (parity r.toNat), af := none, zf := some (decide (r = 0)),
      sf := some r.msb, ovf := of }
  match op with
  | .shl =>
    let r := x <<< c
    let cf := if c < w then some (x.getLsbD (w - c)) else none
    (r, szp r cf (if c = 1 then cf.map (r.msb != ·) else none))
  | .shr =>
    let r := x >>> c
    let cf := if c < w then some (x.getLsbD (c - 1)) else none
    (r, szp r cf (if c = 1 then some x.msb else none))
  | .sar =>
    let r := x.sshiftRight c
    let cf := if c < w then some (x.getLsbD (c - 1)) else none
    (r, szp r cf (if c = 1 then some false else none))
  | .rol =>
    let r := x.rotateLeft (c % w)
    let cf := r.getLsbD 0
    (r, { f with cf := some cf, ovf := if c = 1 then some (r.msb != cf) else none })
  | .ror =>
    let r := x.rotateRight (c % w)
    (r, { f with cf := some r.msb,
                 ovf := if c = 1 then some (r.msb != r.getLsbD (w - 2)) else none })

theorem toNatInt_ofNat6 (c : Nat) (hc : c < 64) : Sail.BitVec.toNatInt (BitVec.ofNat 6 c) = (c : Int) := by
  simp [Sail.BitVec.toNatInt]; omega

theorem eqb6 (c k : Nat) (hc : c < 64) : eq_bits_nat (BitVec.ofNat 6 c) k = decide (c = k) := by
  simp only [eq_bits_nat, toNatInt_ofNat6 c hc]
  by_cases h : c = k
  · simp [h]
  · simp [h]; omega

theorem run_bitslice1 {w : Nat} (x : BitVec w) (i : Int) (hi : 0 ≤ i) (hiw : i < w) (s : SState) :
    (bitslice x i 1).run s = .ok (BitVec.ofBool (x.getLsbD i.toNat)) s := by
  unfold bitslice
  rw [if_pos (by simp [Sail.BitVec.length]; omega)]
  simp only [run_bind]
  rw [run_sail_assert_of (by simp [Sail.BitVec.length]; omega)]
  simp only [run_pure, Sail.BitVec.extractLsb]
  rw [show (i + 1 - 1 : Int).toNat = i.toNat by omega, extractLsb_one_eq_ofBool]
  congr 1
  apply BitVec.eq_of_toNat_eq; simp

theorem run_b_xor (a b : Bool) (s : SState) :
    (b_xor (Sail.BitVec.toNatInt (BitVec.ofBool a)) (Sail.BitVec.toNatInt (BitVec.ofBool b))).run s =
      .ok (if a != b then (1 : Int) else 0) s := by
  cases a <;> cases b <;> rfl

theorem bits1_xor (a b : Bool) : bits_of_int (if a != b then (1 : Int) else 0) 1 = BitVec.ofBool (a != b) := by
  cases a <;> cases b <;> rfl

theorem flagEq_some (b : Bool) : FlagEq (some b) (BitVec.ofBool b) := by
  intro v hv; cases hv; rfl

theorem flagEq_none (x : BitVec 1) : FlagEq none x := by
  intro v hv; cases hv

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64

/-- The value of `shRes` (independent of the flags). -/
def shVal (op : ShOp) {w : Nat} (x : BitVec w) (c : Nat) : BitVec w :=
  if c = 0 then x else
  match op with
  | .shl => x <<< c
  | .shr => x >>> c
  | .sar => x.sshiftRight c
  | .rol => x.rotateLeft (c % w)
  | .ror => x.rotateRight (c % w)

theorem shRes_fst (op : ShOp) {w : Nat} (x : BitVec w) (c : Nat) (f : Flags) : (shRes op x c f).1 = shVal op x c := by
  unfold shRes shVal; split
  · rfl
  · cases op <;> rfl

/-- Janus' flags as the model can match them: for `ROR` with a count ≥ 2 the model takes `CF`
from bit 0 of the result (Sail-x86 defect D6), so `CF` is left unconstrained there. -/
def shFl (op : ShOp) {w : Nat} (x : BitVec w) (c : Nat) (f : Flags) : Flags :=
  if op = .ror ∧ 2 ≤ c then { (shRes op x c f).2 with cf := none } else (shRes op x c f).2

theorem iter_div2 : ∀ (n : Nat) (a : Int), Sail.Nat.iterate (fun x => x / 2) n a = a / 2 ^ n
  | 0, a => by simp [Sail.Nat.iterate]
  | k + 1, a => by
    rw [Sail.Nat.iterate, iter_div2 k, Int.ediv_ediv_of_nonneg (by decide), Int.pow_succ, Int.mul_comm]

theorem ipowI (a : Int) (c : Nat) : (HPow.hPow a (c : Int) : Int) = a ^ c := by
  show a ^ (c : Int).toNat = a ^ c
  rw [Int.toNat_natCast]

theorem shl_val {w : Nat} (x : BitVec w) (c : Nat) :
    bits_of_int (ash_left_int (Sail.BitVec.toNatInt x) c) w = x <<< c := by
  apply BitVec.eq_of_toNat_eq
  have : ash_left_int (Sail.BitVec.toNatInt x) c = ((x.toNat * 2 ^ c : Nat) : Int) := by
    simp only [ash_left_int, Sail.BitVec.toNatInt, ipowI]; push_cast; rfl
  rw [this, bits_of_int_natCast_toNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem neg6 (w c : Nat) (hc : c < 64) (hw : 8 ≤ w) :
    (bits_of_int (Neg.neg (Sail.BitVec.toNatInt (BitVec.ofNat 6 c))) (w + 1)).toInt = -(c : Int) := by
  rw [toNatInt_ofNat6 c hc]
  have : (2 : Int) ^ (w + 1) ≥ 2 ^ 9 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show 9 ≤ w + 1 by omega)
    exact_mod_cast this
  rw [bits_of_int_toInt _ _ (by omega) (by omega)]

theorem ash_neg (i : Int) (c : Nat) : ash_int i (-(c : Int)) = i / 2 ^ c := by
  unfold ash_int
  by_cases h : c = 0
  · subst h; simp
  · have h1 : ((-(c : Int)) == 0) = false := by simp; omega
    have h2 : ((-(c : Int)) >b 0) = false := by simp
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Int.neg_neg]
    rw [show (c : Int) = Int.ofNat c from rfl, Sail.Int.shiftr, iter_div2]

theorem shr_val {w : Nat} (x : BitVec w) (c : Nat) :
    bits_of_int (ash_int (Sail.BitVec.toNatInt x) (-(c : Int))) w = x >>> c := by
  apply BitVec.eq_of_toNat_eq
  rw [ash_neg]
  have : Sail.BitVec.toNatInt x / 2 ^ c = ((x.toNat / 2 ^ c : Nat) : Int) := by
    simp [Sail.BitVec.toNatInt]
  rw [this, bits_of_int_natCast_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)

theorem logbit_eq {w : Nat} (x : BitVec w) (i : Nat) (hi : i < w) :
    logbit_bits (i : Int) x = BitVec.ofBool (x.getLsbD i) := by
  unfold logbit_bits
  rw [if_pos (by simp [Sail.BitVec.length]; omega)]
  simp only [Sail.BitVec.access, Int.toNat_natCast]
  rw [getElem!_pos x i hi, BitVec.getLsbD_eq_getElem hi]


theorem logbit_eqI {w : Nat} (x : BitVec w) (i : Int) (h0 : 0 ≤ i) (hi : i < w) :
    logbit_bits i x = BitVec.ofBool (x.getLsbD i.toNat) := by
  have := logbit_eq x i.toNat (by omega)
  rwa [Int.toNat_of_nonneg h0] at this

theorem flagEq_bne (a b : Bool) : FlagEq (some (a != b)) (BitVec.ofBool (b != a)) := by
  cases a <;> cases b <;> exact flagEq_some _

theorem zf_bv {w : Nat} (r : BitVec w) : BitVec.ofBool (decide (r.toNat = 0)) = BitVec.ofBool (decide (r = 0)) := by
  congr 1; apply decide_eq_decide.mpr; constructor
  · intro h; apply BitVec.eq_of_toNat_eq; simpa using h
  · intro h; subst h; simp

theorem sf_bv {w : Nat} (r : BitVec w) : BitVec.ofBool (decide (2 ^ (w - 1) ≤ r.toNat)) = BitVec.ofBool r.msb := by
  rw [BitVec.msb_eq_decide]


theorem loghead_ofInt (w : Nat) (wi : Int) (hwi : wi = w) (hw : 0 < w) (v : Int) :
    bits_of_int (loghead_int wi v) w = BitVec.ofInt w v := by
  subst hwi
  have h0 : ((w : Int) == 0) = false := by simp; omega
  simp only [loghead_int, h0, Bool.false_eq_true, ↓reduceIte, Sail.BitVec.toNatInt, Int.toNat_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_slice0, show ∀ n : Nat, Int.ofNat n = (n : Int) from fun _ => rfl, bits_of_int_natCast_toNat,
    BitVec.toNat_ofInt]
  have hp : (0 : Int) < ((2 ^ w : Nat) : Int) := by have := Nat.two_pow_pos w; omega
  have hn : 0 ≤ v % ((2 ^ w : Nat) : Int) := Int.emod_nonneg _ (by omega)
  have : (v % ((2 ^ w : Nat) : Int)).toNat < 2 ^ w := by
    have := Int.emod_lt_of_pos v hp; omega
  rw [Nat.mod_eq_of_lt this]

theorem sar_neg {w : Nat} (x : BitVec w) (wi : Int) (hwi : wi = w) (hw : 0 < w) (c : Nat) :
    bits_of_int (loghead_int wi (x.toInt / 2 ^ c)) w = x.sshiftRight c := by
  rw [loghead_ofInt w wi hwi hw]
  have e : x.toInt / 2 ^ c = (x.sshiftRight c).toInt := by
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; norm_cast
  rw [e, BitVec.ofInt_toInt]

theorem sar_pos {w : Nat} (x : BitVec w) (hm : x.msb = false) (c : Nat) :
    bits_of_int (Sail.BitVec.toNatInt (bits_of_int (ash_int (Sail.BitVec.toNatInt x) (-(c : Int))) w)) w =
      x.sshiftRight c := by
  rw [shr_val, BitVec.sshiftRight_eq_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [show Sail.BitVec.toNatInt (x >>> c) = ((x >>> c).toNat : Int) from rfl, bits_of_int_natCast_toNat]
  exact Nat.mod_eq_of_lt (x >>> c).isLt

theorem shlI_nat {w : Nat} (x : BitVec w) (c : Nat) : (HShiftLeft.hShiftLeft x (c : Int) : BitVec w) = x <<< c := rfl

theorem shrI_nat {w : Nat} (x : BitVec w) (c : Nat) : (HShiftRight.hShiftRight x (c : Int) : BitVec w) = x >>> c := by
  show (HShiftLeft.hShiftLeft x (-(c : Int)) : BitVec w) = _
  cases c with
  | zero => show BitVec.shiftLeft x 0 = _; simp
  | succ k => show BitVec.ushiftRight x (k + 1) = _; rfl

theorem rotl_val {w : Nat} (x : BitVec w) (wi : Int) (hwi : wi = w) (c : Nat) (hc : c < w) :
    rotate_left_bits x wi (c : Int) = x.rotateLeft (c % w) := by
  subst hwi
  unfold rotate_left_bits
  simp only []
  rw [show ((w : Int) - (c : Int)) = ((w - c : Nat) : Int) by omega, shlI_nat, shrI_nat, BitVec.rotateLeft_def]
  simp only [Nat.mod_eq_of_lt hc]

theorem rotr_val {w : Nat} (x : BitVec w) (wi : Int) (hwi : wi = w) (c : Nat) (hc : c < w) :
    rotate_right_bits x wi (c : Int) = x.rotateRight (c % w) := by
  subst hwi
  unfold rotate_right_bits
  simp only []
  rw [show ((w : Int) - (c : Int)) = ((w - c : Nat) : Int) by omega, shlI_nat, shrI_nat, BitVec.rotateRight_def]
  simp only [Nat.mod_eq_of_lt hc, BitVec.or_comm]

end JanusX86.Proofs

namespace JanusX86.Proofs

theorem rotl0 {w : Nat} (x : BitVec w) : x.rotateLeft 0 = x := by
  rw [BitVec.rotateLeft_def]; simp [BitVec.ushiftRight_eq_zero (Nat.le_refl w)]

theorem rotr0 {w : Nat} (x : BitVec w) : x.rotateRight 0 = x := by
  rw [BitVec.rotateRight_def]; simp [BitVec.shiftLeft_eq_zero (Nat.le_refl w)]

end JanusX86.Proofs
