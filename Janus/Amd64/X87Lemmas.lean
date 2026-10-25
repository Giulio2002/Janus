import Janus.Float.Lemmas
import Janus.Amd64.X87

/-!
# The x87 model at extended precision is IEEE 754 (proved, not trusted)

A **supported** double-extended encoding (`Supported`: below `2^80`, not an unnormal, a
pseudo-infinity or a pseudo-NaN) denotes, through `X87.std`, an encoding of the standard IEEE
format `ext` = (15, 63) of the core. With precision control `11` (64 bits, `PC` of the
Linux default control word `0x037F`) the x87 operations compute the IEEE 754 operations of
`Janus.Float.Spec` on those values, in any rounding direction, and deliver a NaN exactly when
the specification's result is a NaN:

* `std_ofStd`, `ofStd_std`: `std` and `ofStd` are inverse bijections between the canonical
  double-extended encodings (`J` set exactly when the exponent is non-zero) and `ext`;
* `binop_add_ieee`, `binop_mul_ieee`: `FADD`/`FMUL` (every form: `X87.binop`);
* `X87.Idle`: the x87 state the System V ABI guarantees at a call (empty register stack, the
  default control word, no pending exception), which the C examples assume at entry.
-/

namespace Janus.Amd64.X87

open Janus.Float

/-! ## Encodings -/

/-- A supported double-extended encoding. -/
def Supported (x : Nat) : Prop := x < 2 ^ 80 ∧ unsupported x = false

theorem ext_width : ext.width = 79 := rfl
theorem fmtP_64 : fmtP 64 = ext := rfl

theorem std_lt (x : Nat) : std x < 2 ^ ext.width := by
  unfold std
  apply pack_lt
  · show _ < 2 ^ 15
    have : expOf80 x < 2 ^ 15 := Nat.mod_lt _ (Nat.two_pow_pos _)
    split <;> omega
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem jOf80_eq (x : Nat) : jOf80 x = (sigOf80 x / 2 ^ 63 % 2 = 1) := by
  simp [jOf80, sigOf80]; omega

theorem pack80_sign (s : Bool) (e g : Nat) (he : e < 2 ^ 15) (hg : g < 2 ^ 64) :
    signOf80 (pack80 s e g) = s := by
  cases s <;> simp [signOf80, pack80] <;> omega

theorem pack80_exp (s : Bool) (e g : Nat) (he : e < 2 ^ 15) (hg : g < 2 ^ 64) :
    expOf80 (pack80 s e g) = e := by
  cases s <;> simp [expOf80, pack80] <;> omega

theorem pack80_sig (s : Bool) (e g : Nat) (he : e < 2 ^ 15) (hg : g < 2 ^ 64) :
    sigOf80 (pack80 s e g) = g := by
  cases s <;> simp [sigOf80, pack80] <;> omega

theorem pack80_lt (s : Bool) (e g : Nat) (he : e < 2 ^ 15) (hg : g < 2 ^ 64) :
    pack80 s e g < 2 ^ 80 := by
  cases s <;> simp [pack80] <;> omega

/-- An `ext` encoding is the pack of its fields. -/
theorem ext_pack_fields (y : Nat) (hy : y < 2 ^ ext.width) :
    pack ext (signOf ext y) (expOf ext y) (fracOf ext y) = y := by
  rw [ext_width] at hy
  simp only [pack, signOf, expOf, fracOf, ext, Fmt.signBit]
  by_cases h : y / 2 ^ (15 + 63) % 2 = 1 <;> simp [h] <;> omega

theorem ext_exp_lt (y : Nat) : expOf ext y < 2 ^ 15 := Nat.mod_lt _ (Nat.two_pow_pos _)
theorem ext_frac_lt (y : Nat) : fracOf ext y < 2 ^ 63 := Nat.mod_lt _ (Nat.two_pow_pos _)

/-- An encoding is the pack of its fields. -/
theorem pack80_fields (x : Nat) (hx : x < 2 ^ 80) :
    pack80 (signOf80 x) (expOf80 x) (sigOf80 x) = x := by
  simp only [pack80, signOf80, expOf80, sigOf80]
  by_cases h : x / 2 ^ 79 % 2 = 1 <;> simp [h] <;> omega

theorem std_pack80 (s : Bool) (e g : Nat) (he : e < 2 ^ 15) (hg : g < 2 ^ 64) :
    std (pack80 s e g) = pack ext s (if e = 0 ∧ g / 2 ^ 63 % 2 = 1 then 1 else e) (g % 2 ^ 63) := by
  unfold std
  rw [pack80_sign _ _ _ he hg, pack80_exp _ _ _ he hg, pack80_sig _ _ _ he hg]
  simp [jOf80_eq, pack80_sig _ _ _ he hg]

theorem ext_pack_sign (s : Bool) (e f : Nat) (he : e < 2 ^ 15) (hf : f < 2 ^ 63) :
    signOf ext (pack ext s e f) = s := by
  cases s <;> simp [signOf, pack, ext, Fmt.signBit] <;> omega

theorem ext_pack_exp (s : Bool) (e f : Nat) (he : e < 2 ^ 15) (hf : f < 2 ^ 63) :
    expOf ext (pack ext s e f) = e := by
  cases s <;> simp [expOf, pack, ext, Fmt.signBit] <;> omega

theorem ext_pack_frac (s : Bool) (e f : Nat) (he : e < 2 ^ 15) (hf : f < 2 ^ 63) :
    fracOf ext (pack ext s e f) = f := by
  cases s <;> simp [fracOf, pack, ext, Fmt.signBit] <;> omega

/-- `std` undoes `ofStd`. -/
theorem std_ofStd (y : Nat) (hy : y < 2 ^ ext.width) : std (ofStd y) = y := by
  have he := ext_exp_lt y
  have hf := ext_frac_lt y
  generalize hg : (if expOf ext y = 0 then 0 else 2 ^ 63) + fracOf ext y * 2 ^ (64 - 64) = g
  have hof : ofStd y = pack80 (signOf ext y) (expOf ext y) g := by rw [← hg]; rfl
  have hg' : g < 2 ^ 64 := by rw [← hg]; split <;> simp <;> omega
  rw [hof, std_pack80 _ _ _ he hg']
  conv => rhs; rw [← ext_pack_fields y hy]
  by_cases h0 : expOf ext y = 0
  · have h1 : g = fracOf ext y := by rw [← hg]; simp [h0]
    have h2 : ¬ g / 2 ^ 63 % 2 = 1 := by rw [h1]; rw [Nat.div_eq_of_lt hf]; simp
    rw [if_neg (fun h => h2 h.2), h1, Nat.mod_eq_of_lt hf]
  · have h1 : g = 2 ^ 63 + fracOf ext y := by rw [← hg]; simp [h0]
    rw [if_neg (fun h => h0 h.1), h1]
    congr 1; omega

/-- The fields of `std x`. -/
theorem std_fields (x : Nat) :
    signOf ext (std x) = signOf80 x ∧
    expOf ext (std x) = (if expOf80 x = 0 ∧ jOf80 x = true then 1 else expOf80 x) ∧
    fracOf ext (std x) = sigOf80 x % 2 ^ 63 := by
  have he : (if expOf80 x = 0 ∧ jOf80 x = true then 1 else expOf80 x) < 2 ^ 15 := by
    have : expOf80 x < 2 ^ 15 := Nat.mod_lt _ (Nat.two_pow_pos _)
    split <;> omega
  have hf : sigOf80 x % 2 ^ 63 < 2 ^ 63 := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold std
  exact ⟨ext_pack_sign _ _ _ he hf, ext_pack_exp _ _ _ he hf, ext_pack_frac _ _ _ he hf⟩

theorem sign_std (x : Nat) : signOf ext (std x) = signOf80 x := (std_fields x).1

/-- `ofStd` undoes `std` on canonical encodings (`J` set exactly for a non-zero exponent). -/
theorem ofStd_std (x : Nat) (hx : x < 2 ^ 80) (hc : jOf80 x = (expOf80 x != 0)) :
    ofStd (std x) = x := by
  obtain ⟨hS, hE, hF⟩ := std_fields x
  have hj : jOf80 x = true ↔ expOf80 x ≠ 0 := by rw [hc]; simp
  have hcond : ¬ (expOf80 x = 0 ∧ jOf80 x = true) := fun ⟨h0, h1⟩ => hj.1 h1 h0
  rw [if_neg hcond] at hE
  show pack80 (signOf ext (std x)) (expOf ext (std x))
    ((if expOf ext (std x) = 0 then 0 else 2 ^ 63) + fracOf ext (std x) * 2 ^ (64 - 64)) = x
  rw [hS, hE, hF]
  conv => rhs; rw [← pack80_fields x hx]
  congr 1
  have hjd : (sigOf80 x / 2 ^ 63 % 2 = 1) ↔ expOf80 x ≠ 0 := by
    rw [← hj]; simp [jOf80, sigOf80]; omega
  have hg : sigOf80 x < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos _)
  by_cases h0 : expOf80 x = 0
  · have : ¬ sigOf80 x / 2 ^ 63 % 2 = 1 := fun h => hjd.1 h h0
    simp [h0]; omega
  · have := hjd.2 h0
    simp [h0]; omega

theorem std_zero80 (s : Bool) : std (zero80 s) = zero ext s := by
  cases s <;> decide

theorem std_inf80 (s : Bool) : std (inf80 s) = inf ext s := by
  cases s <;> decide

theorem isNaN_indefinite80 : isNaN ext (std indefinite80) = true := by decide

theorem isNaN80_eq {x : Nat} (h : unsupported x = false) : isNaN80 x = isNaN ext (std x) := by
  simp [isNaN80, h]

theorem quiet80_fields (x : Nat) :
    signOf80 (quiet80 x) = signOf80 x ∧ expOf80 (quiet80 x) = expOf80 x ∧
    sigOf80 (quiet80 x) = sigOf80 x ||| 2 ^ 62 := by
  unfold quiet80 signOf80 expOf80 sigOf80
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.or_div_two_pow, Nat.div_eq_of_lt (by decide : (2:Nat) ^ 62 < 2 ^ 79), Nat.or_zero]
  · rw [Nat.or_div_two_pow, Nat.div_eq_of_lt (by decide : (2:Nat) ^ 62 < 2 ^ 64), Nat.or_zero]
  · rw [Nat.or_mod_two_pow, Nat.mod_eq_of_lt (by decide : (2:Nat) ^ 62 < 2 ^ 64)]

/-- Setting the quiet bit of a NaN gives a NaN. -/
theorem isNaN_quiet80 {x : Nat} (h : isNaN80 x = true) : isNaN ext (std (quiet80 x)) = true := by
  simp only [isNaN80, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hu, hn⟩ := h
  rw [isNaN_iff ext (by decide)] at hn ⊢
  obtain ⟨-, hE, hF⟩ := std_fields x
  obtain ⟨-, hE', hF'⟩ := std_fields (quiet80 x)
  obtain ⟨-, qe, qs⟩ := quiet80_fields x
  rw [hE, hF] at hn
  rw [hE', hF', qe, qs]
  have hmx : (Fmt.expMax ext) = 32767 := rfl
  rw [hmx] at hn ⊢
  have hq : 2 ^ 62 ≤ (sigOf80 x ||| 2 ^ 62) % 2 ^ 63 := by
    rw [Nat.or_mod_two_pow, Nat.mod_eq_of_lt (by decide : (2:Nat) ^ 62 < 2 ^ 63)]
    exact Nat.right_le_or
  obtain ⟨he, -⟩ := hn
  refine ⟨?_, by omega⟩
  by_cases h0 : expOf80 x = 0
  · exfalso; rw [h0] at he; simp at he; split at he <;> omega
  · simp [h0] at he ⊢; exact he

theorem isNaN_nanPick (a b : Nat) (ha : unsupported a = false) (hb : unsupported b = false)
    (h : isNaN80 a = true ∨ isNaN80 b = true) : isNaN ext (std (nanPick a b).1) = true := by
  unfold nanPick
  simp only
  apply isNaN_quiet80
  rcases h with h | h <;> (repeat' split) <;> simp_all

theorem roundP64_res (rm : RM) (pre : Nat) (neg : Bool) (m : Nat) (e : Int) :
    (roundP (fmtP 64) (widen 64) rm pre neg m e).res = ofStd (round ext rm neg m e).bits := by
  unfold roundP; simp only [fmtP_64]
  by_cases h1 : (round ext rm neg m e).overflow <;> by_cases h2 : (round ext rm neg m e).tinyAfter <;>
    by_cases h3 : (round ext rm neg m e).inexact <;> simp [h1, h2, h3, ofStd]

theorem std_roundP64 (rm : RM) (pre : Nat) (neg : Bool) (m : Nat) (e : Int) :
    std (roundP (fmtP 64) (widen 64) rm pre neg m e).res = (round ext rm neg m e).bits := by
  rw [roundP64_res, std_ofStd _ (round_bits_lt _ _ _ _ _)]

theorem rmi_beq {rm : RM} : (rm == .rmi) = decide (rm = .rmi) := by cases rm <;> rfl

/-! ## IEEE 754 at extended precision -/

theorem done_res (r fl : Nat) : (done r fl).res = r := rfl

theorem kind_cases (k : Kind) :
    k = .zero ∨ k = .subnormal ∨ k = .normal ∨ k = .inf ∨ k = .qnan ∨ k = .snan := by
  cases k <;> simp

/-- The NaN case of `binop`: some operand is a NaN (and none is unsupported). -/
theorem binop_nan (op : BinOp) (p : Nat) (rm : RM) (a b : Nat) (bDen : Bool)
    (ha : unsupported a = false) (hb : unsupported b = false)
    (hn : isNaN ext (std a) = true ∨ isNaN ext (std b) = true) :
    isNaN ext (std (binop op p rm a b bDen).res) = true := by
  have hn' : (isNaN80 a || isNaN80 b) = true := by
    rw [isNaN80_eq ha, isNaN80_eq hb]; rcases hn with h | h <;> simp [h]
  have : (binop op p rm a b bDen).res = (nanPick a b).1 := by
    unfold binop; rw [if_neg (by simp [ha, hb]), if_pos hn']; rfl
  rw [this]
  exact isNaN_nanPick a b ha hb (by rw [isNaN80_eq ha, isNaN80_eq hb]; exact hn)

/-- The non-NaN case of `binop`. -/
theorem binop_num (op : BinOp) (p : Nat) (rm : RM) (a b : Nat) (bDen : Bool)
    (ha : unsupported a = false) (hb : unsupported b = false)
    (hA : isNaN ext (std a) = false) (hB : isNaN ext (std b) = false) :
    binop op p rm a b bDen = match op with
      | .add => addCore p rm (classify ext (std a)) (classify ext (std b)) (signOf ext (std a))
          (signOf ext (std b)) (valueOf ext (std a)) (valueOf ext (std b)) (deOf a b bDen)
      | .sub => addCore p rm (classify ext (std a)) (classify ext (std b)) (signOf ext (std a))
          (!signOf ext (std b)) (valueOf ext (std a)) (Val.neg (valueOf ext (std b))) (deOf a b bDen)
      | .mul => mulCore p rm (classify ext (std a)) (classify ext (std b)) (signOf ext (std a))
          (signOf ext (std b)) (valueOf ext (std a)) (valueOf ext (std b)) (deOf a b bDen)
      | .div => divCore p rm (classify ext (std a)) (classify ext (std b)) (signOf ext (std a))
          (signOf ext (std b)) (valueOf ext (std a)) (valueOf ext (std b)) (deOf a b bDen) := by
  unfold binop
  rw [if_neg (by simp [ha, hb]), if_neg (by rw [isNaN80_eq ha, isNaN80_eq hb, hA, hB]; simp),
    sign_std, sign_std]
  rfl

theorem not_nan_kind {x : Nat} (h : isNaN ext x = false) :
    classify ext x ≠ .qnan ∧ classify ext x ≠ .snan := by
  unfold isNaN at h; constructor <;> intro h' <;> rw [h'] at h <;> simp at h

/-- The sum core in IEEE terms. -/
theorem addCore_ieee (rm : RM) (A B : Nat) (de : Nat) (hA : isNaN ext A = false)
    (hB : isNaN ext B = false) :
    ResultIs ext (add ext rm A B) (std (addCore 64 rm (classify ext A) (classify ext B)
      (signOf ext A) (signOf ext B) (valueOf ext A) (valueOf ext B) de).res) := by
  have hnA := not_nan_kind hA
  have hnB := not_nan_kind hB
  unfold add addCore
  rw [hA, hB]
  rcases kind_cases (classify ext A) with h1 | h1 | h1 | h1 | h1 | h1 <;>
  rcases kind_cases (classify ext B) with h2 | h2 | h2 | h2 | h2 | h2 <;>
    rw [h1] at hnA ⊢ <;> rw [h2] at hnB ⊢ <;> (try simp at hnA) <;> (try simp at hnB) <;>
    rcases Bool.eq_false_or_eq_true (signOf ext A) with hs1 | hs1 <;>
    rcases Bool.eq_false_or_eq_true (signOf ext B) with hs2 | hs2 <;>
    rw [hs1, hs2] <;>
    rcases Option.eq_none_or_eq_some (addExact (valueOf ext A).n (valueOf ext A).e
        (valueOf ext B).n (valueOf ext B).e) with hx | ⟨⟨neg, m, e⟩, hx⟩ <;>
    simp [ResultIs, hx, std_zero80, std_inf80, isNaN_indefinite80, std_roundP64, done_res, rmi_beq] <;>
    (try (rw [valueOf_of_zero h1, valueOf_of_zero h2] at hx; simp [Val.n, Val.e, addExact_zero] at hx))

/-- The product core in IEEE terms. -/
theorem mulCore_ieee (rm : RM) (A B : Nat) (de : Nat) (hA : isNaN ext A = false)
    (hB : isNaN ext B = false) :
    ResultIs ext (mul ext rm A B) (std (mulCore 64 rm (classify ext A) (classify ext B)
      (signOf ext A) (signOf ext B) (valueOf ext A) (valueOf ext B) de).res) := by
  have hnA := not_nan_kind hA
  have hnB := not_nan_kind hB
  unfold mul mulCore
  rw [hA, hB]
  rcases kind_cases (classify ext A) with h1 | h1 | h1 | h1 | h1 | h1 <;>
  rcases kind_cases (classify ext B) with h2 | h2 | h2 | h2 | h2 | h2 <;>
    rw [h1] at hnA ⊢ <;> rw [h2] at hnB ⊢ <;> (try simp at hnA) <;> (try simp at hnB) <;>
    rcases Option.eq_none_or_eq_some (mulExact (valueOf ext A).n (valueOf ext A).e
        (valueOf ext B).n (valueOf ext B).e) with hx | ⟨⟨neg, m, e⟩, hx⟩ <;>
    simp [ResultIs, hx, std_zero80, std_inf80, isNaN_indefinite80, std_roundP64, done_res]

/-- `FADD`/`FADDP`/`FIADD` (precision 64) is IEEE 754 addition on `ext`. -/
theorem binop_add_ieee (rm : RM) (a b : Nat) (bDen : Bool) (ha : unsupported a = false)
    (hb : unsupported b = false) :
    ResultIs ext (add ext rm (std a) (std b)) (std (binop .add 64 rm a b bDen).res) := by
  by_cases hn : isNaN ext (std a) = true ∨ isNaN ext (std b) = true
  · have hm : add ext rm (std a) (std b) = none := by
      unfold add; rcases hn with h | h <;> simp [h]
    rw [hm]; exact binop_nan _ _ _ _ _ _ ha hb hn
  · have hA : isNaN ext (std a) = false := by cases h : isNaN ext (std a) <;> simp_all
    have hB : isNaN ext (std b) = false := by cases h : isNaN ext (std b) <;> simp_all
    rw [binop_num _ _ _ _ _ _ ha hb hA hB]
    exact addCore_ieee rm _ _ _ hA hB

/-- `FMUL`/`FMULP`/`FIMUL` (precision 64) is IEEE 754 multiplication on `ext`. -/
theorem binop_mul_ieee (rm : RM) (a b : Nat) (bDen : Bool) (ha : unsupported a = false)
    (hb : unsupported b = false) :
    ResultIs ext (mul ext rm (std a) (std b)) (std (binop .mul 64 rm a b bDen).res) := by
  by_cases hn : isNaN ext (std a) = true ∨ isNaN ext (std b) = true
  · have hm : mul ext rm (std a) (std b) = none := by
      unfold mul; rcases hn with h | h <;> simp [h]
    rw [hm]; exact binop_nan _ _ _ _ _ _ ha hb hn
  · have hA : isNaN ext (std a) = false := by cases h : isNaN ext (std a) <;> simp_all
    have hB : isNaN ext (std b) = false := by cases h : isNaN ext (std b) <;> simp_all
    rw [binop_num _ _ _ _ _ _ ha hb hA hB]
    exact mulCore_ieee rm _ _ _ hA hB

/-! ## The System V x87 state at a call -/

/-- The x87 state at a System V call boundary: every register empty, the Linux default control
word `0x037F` (all exceptions masked, 64-bit precision, round to nearest), no pending exception
(`ES` clear), and a 3-bit `TOP`. The sticky exception flags and the condition codes are
arbitrary. -/
def Idle (t : St) : Prop := t.cw = 0x37F ∧ t.tags = 0 ∧ t.sw / 128 % 2 = 0 ∧ t.top < 8

end Janus.Amd64.X87
