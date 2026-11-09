import JanusASL.Proofs.FP.RoundLemmas
import JanusASL.Proofs.FP.Compare
/-! # `FPRoundBase` (binary32) as a pure function

`rb32` transcribes `FPRoundBase(op, fpcr, rounding, FALSE, TRUE, 32)` as a pure function of the
normalised exponent and the scaled floors/errors the ASL computes, and `run_FPRoundBase32_rb`
proves the generated monadic definition equal to it under `LinuxEL0Config` (no streaming mode,
the raised exceptions' trap enables clear): the result, and FPSR OR-ed with the raised and the
directly set cumulative bits. -/
set_option linter.unusedSimpArgs false
namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

syntax "fp_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| fp_simp [$ls,*] $[$loc]?) => `(tactic| simp (config := { decide := true }) [cfgFeat, num_of_Feature,
      cfgFeaturesOff, run_bind, run_pure, run_map, run_sail_assert_true, run_undefined_bool, run_undefined_bitvector,
      run_undefined_int, HaveEL, orM, andM, toBool, $ls,*] $[$loc]?)

/-- The rounding decision of `FPRoundBase` for the error `er` of the floor `a` (`round_up`). -/
def rbRU (rm : Janus.Float.RM) (neg : Bool) (er : Rat) (a : Int) : Bool :=
  let sign : BitVec 1 := if neg then 1#1 else 0#1
  match rm with
  | .rne => gt_real er (1 / 2) || eq_real er (1 / 2) && integer_access a 0 == 1#1
  | .rpi => er != 0 && sign == 0#1
  | .rmi => er != 0 && sign == 1#1
  | _ => false

/-- `overflow_to_inf` of `FPRoundBase`. -/
def rbOTI (rm : Janus.Float.RM) (neg : Bool) : Bool :=
  let sign : BitVec 1 := if neg then 1#1 else 0#1
  match rm with
  | .rne => true
  | .rpi => sign == 0#1
  | .rmi => sign == 1#1
  | _ => false

/-- The alternative-FP tininess-after-rounding test of `FPRoundBase` (`AH = 1`):
`biased_exp_unconstrained < 1 && int_mant_unconstrained != 0`. -/
def rbTiny (ah : Bool) (rm : Janus.Float.RM) (neg : Bool) (E Au : Int) (Eu : Rat) : Bool :=
  let bu : Int := E + 126 + 1
  let (bu', imu) : Int × Int :=
    if rbRU rm neg Eu Au then (if Au + 1 = 2 ^ 24 then (bu + 1, fdiv_int (Au + 1) 2) else (bu, Au + 1)) else (bu, Au)
  ah && decide (bu' < 1) && decide (imu ≠ 0)

/-- The biased exponent and integer mantissa of `FPRoundBase` after the rounding increment
(`round_up`) of the floor `A` at the normalised exponent `E` (binary32). -/
def rbBE2 (ru : Bool) (E A : Int) : Int × Int :=
  let be : Int := max (E + 126 + 1) 0
  if ru then
    (let b : Int := if A + 1 = 2 ^ 23 then 1 else be
     if A + 1 = 2 ^ 24 then (b + 1, fdiv_int (A + 1) 2) else (b, A + 1))
  else (be, A)

/-- `FPRoundBase(op, fpcr, rounding, FALSE, TRUE, 32)` as a pure function of the normalised
exponent `E`, the scaled floors `A` (constrained) and `Au` (unconstrained) and their errors `Er`,
`Eu`: the result, the FPSR bits raised through `FPProcessException` and the bits set directly. -/
def rb32 (ah fz ufe : Bool) (rm : Janus.Float.RM) (neg : Bool) (E A Au : Int) (Er Eu : Rat) :
    BitVec 32 × Nat × Nat :=
  if !ah && fz && decide (E < -126) then (BitVec.ofNat 32 (Janus.Float.zero Janus.Float.binary32 neg), 0, 8) else
  let be : Int := max (E + 126 + 1) 0
  let uf1 : Bool := !ah && decide (be = 0) && (Er != 0 || ufe)
  let tinyA := rbTiny ah rm neg E Au Eu
  if tinyA && fz then (BitVec.ofNat 32 (Janus.Float.zero Janus.Float.binary32 neg), 16, 8) else
  let uf : Nat := if uf1 || (tinyA && (Er != 0 || ufe)) then 8 else 0
  let (be2, im2) : Int × Int := rbBE2 (rbRU rm neg Er A) E A
  let ovf : Prop := 2 ^ 8 - 1 ≤ be2
  let err : Rat := if ovf then 1 else Er
  (if ovf then BitVec.ofNat 32 (if rbOTI rm neg then Janus.Float.inf Janus.Float.binary32 neg
      else Janus.Float.maxNormal Janus.Float.binary32 neg)
    else BitVec.ofNat 32 ((if neg then 2 ^ 31 else 0) + be2.toNat % 2 ^ 8 * 2 ^ 23 + im2.toNat % 2 ^ 23),
    uf ||| (if ovf then 4 else 0) ||| (if err != 0 then 16 else 0), 0)

/-- `rb32` at the floors and errors `FPRoundBase` computes for `(-1)^neg * m * 2^e`. -/
def rb32Of (fpcr : Nat) (rm : Janus.Float.RM) (neg : Bool) (m : Nat) (e : Int) : BitVec 32 × Nat × Nat :=
  let dc : Int := e - (max ((Nat.log2 m : Int) + e) (-126) - 23)
  let du : Int := 23 - (Nat.log2 m : Int)
  rb32 (Janus.Arm64.FP.ah fpcr) (Janus.Arm64.FP.fz fpcr) (Janus.Arm64.FP.ufe fpcr) rm neg ((Nat.log2 m : Int) + e)
    (round_down ((m : Rat) * 2 ^ dc)) (round_down ((m : Rat) * 2 ^ du))
    (sub_real ((m : Rat) * 2 ^ dc) (to_real (round_down ((m : Rat) * 2 ^ dc))))
    (sub_real ((m : Rat) * 2 ^ du) (to_real (round_down ((m : Rat) * 2 ^ du))))

theorem rd_nonneg (m : Nat) (d : Int) : 0 ≤ round_down ((m : Rat) * 2 ^ d) := by
  by_cases h : 0 ≤ d
  · rw [((rd_split m d).1 h).1]; exact Int.natCast_nonneg _
  · rw [((rd_split m d).2 (by omega)).1]; exact Int.natCast_nonneg _

theorem run_PE_set {s : SState} (hc : LinuxEL0Config s) (e : FPExc) (fpcr : BitVec 64)
    (hen : fpcr.getLsbD (fpExcBit e + 8) = false) (v : BitVec 64) :
    (FPProcessException e fpcr).run (s.set .FPSR v) = .ok () (s.set .FPSR (v ||| BitVec.ofNat 64 (2 ^ fpExcBit e))) := by
  rw [run_FPProcessException (hc.set_FPSR v) e fpcr hen (get?_set_FPSR s v), set_set_FPSR,
    update_one_or _ _ (by cases e <;> decide)]

theorem run_ME_ifPE {β : Type} {s : SState} (hc : LinuxEL0Config s) (e : FPExc) (fpcr : BitVec 64) (c : Prop)
    [Decidable c] (hen : c → fpcr.getLsbD (fpExcBit e + 8) = false) (v : BitVec 64) :
    (ExceptT.run (if c then liftM (FPProcessException e fpcr) else pure () : SailME β Unit)).run (s.set .FPSR v) =
      .ok (.ok ()) (s.set .FPSR (v ||| BitVec.ofNat 64 (if c then 2 ^ fpExcBit e else 0))) := by
  by_cases h : c
  · simp only [h, ite_true, run_ME_lift, run_PE_set hc e fpcr (hen h)]
  · simp only [h, ite_false, run_ME_pure, BitVec.ofNat_eq_ofNat, BitVec.or_zero]

theorem run_ME_ifPE' {β : Type} {s : SState} (hc : LinuxEL0Config s) (e : FPExc) (fpcr : BitVec 64) (c : Prop)
    [Decidable c] (hen : ¬c → fpcr.getLsbD (fpExcBit e + 8) = false) (v : BitVec 64) :
    (ExceptT.run (if c then pure () else liftM (FPProcessException e fpcr) : SailME β Unit)).run (s.set .FPSR v) =
      .ok (.ok ()) (s.set .FPSR (v ||| BitVec.ofNat 64 (if c then 0 else 2 ^ fpExcBit e))) := by
  by_cases h : c
  · simp only [h, ite_true, run_ME_pure, BitVec.ofNat_eq_ofNat, BitVec.or_zero]
  · simp only [h, ite_false, run_ME_lift, run_PE_set hc e fpcr (hen h)]

theorem run_ME_ovf {β : Type} {w : Nat} {s : SState} (hc : LinuxEL0Config s) (fpcr : BitVec 64) (c : Prop)
    [Decidable c] (X : SailME β (BitVec w)) (r : BitVec w)
    (hX : ∀ v, (ExceptT.run X).run (s.set .FPSR v) = .ok (.ok r) (s.set .FPSR v)) (y : real × BitVec w) (msg : String)
    (hen : c → fpcr.getLsbD (fpExcBit .FPExc_Overflow + 8) = false) (v : BitVec 64) :
    (ExceptT.run (if c then (X >>= fun result => (fun _ => ((1 : real), result)) <$>
        liftM (FPProcessException .FPExc_Overflow fpcr)) else (fun _ => y) <$> liftM (sail_assert true msg) :
        SailME β (real × BitVec w))).run (s.set .FPSR v) =
      .ok (.ok (if c then (1, r) else y)) (s.set .FPSR (v ||| BitVec.ofNat 64 (if c then 4 else 0))) := by
  by_cases h : c
  · simp only [h, ite_true, run_ME_bind, hX, run_ME_map, run_ME_lift, run_PE_set hc _ fpcr (hen h)]; rfl
  · simp only [h, ite_false, run_ME_map, run_ME_lift, run_sail_assert_true, BitVec.ofNat_eq_ofNat, BitVec.or_zero]

theorem run_ME_FPInfinity32 {β : Type} (s : SState) (neg : Bool) :
    (ExceptT.run (liftM (FPInfinity (if neg then 1#1 else 0#1) 32) : SailME β (BitVec 32))).run s =
      .ok (.ok (BitVec.ofNat 32 (Janus.Float.inf Janus.Float.binary32 neg))) s := by
  simp only [run_ME_lift, run_FPInfinity32]

theorem run_ME_FPMaxNormal32 {β : Type} (s : SState) (neg : Bool) :
    (ExceptT.run (liftM (FPMaxNormal (if neg then 1#1 else 0#1) 32) : SailME β (BitVec 32))).run s =
      .ok (.ok (BitVec.ofNat 32 (Janus.Float.maxNormal Janus.Float.binary32 neg))) s := by
  simp only [run_ME_lift, run_FPMaxNormal32]

theorem fdiv16 : fdiv_int 16777216 2 = 8388608 := by decide
theorem fdiv_nonneg (k : Int) (hk : 0 ≤ k) : 0 ≤ fdiv_int k 2 := by rw [fdiv_two k hk]; omega

theorem bits_ite (c : Prop) [Decidable c] (a X : BitVec 32) (N : Nat) (h : X.toNat = N % 2 ^ 32) :
    (if c then a else X) = (if c then a else BitVec.ofNat 32 N) := by
  have : X = BitVec.ofNat 32 N := BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat])
  rw [this]

theorem isub7 (i : Int) (h : 0 ≤ i) : (integer_subrange i 7 0).toNat = i.toNat % 256 :=
  integer_subrange_toNat i 7 h
theorem isub22 (i : Int) (h : 0 ≤ i) : (integer_subrange i 22 0).toNat = i.toNat % 8388608 :=
  integer_subrange_toNat i 22 h

theorem enc_fin (neg : Bool) (be k : Int) (w1 w2 : Nat) (hw1 : w1 = 8) (hw2 : w2 = 23) (x : BitVec 1)
    (hx : x = if neg then 1#1 else 0#1) (y z : Nat) (hy : y = be.toNat % 256) (hz : z = k.toNat % 8388608) :
    (x.toNat <<< w1 ||| y) <<< w2 ||| z =
      ((if neg then 2147483648 else 0) + be.toNat % 256 * 8388608 + k.toNat % 8388608) % 2 ^ 32 := by
  subst hw1 hw2 hx hy hz
  have b1 : be.toNat % 256 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have b2 : k.toNat % 8388608 < 2 ^ 23 := Nat.mod_lt _ (by decide)
  rw [← Nat.shiftLeft_add_eq_or_of_lt b1, ← Nat.shiftLeft_add_eq_or_of_lt b2, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have : (if neg then 2147483648 else 0) + be.toNat % 256 * 8388608 + k.toNat % 8388608 < 2 ^ 32 := by
    cases neg <;> simp <;> omega
  rw [Nat.mod_eq_of_lt this]
  cases neg <;> simp <;> omega

theorem run_ME_infmax32 {β : Type} (s : SState) (neg : Bool) (c : Prop) [Decidable c] :
    (ExceptT.run (if c then liftM (FPInfinity (if neg then 1#1 else 0#1) 32)
        else liftM (FPMaxNormal (if neg then 1#1 else 0#1) 32) : SailME β (BitVec 32))).run s =
      .ok (.ok (if c then BitVec.ofNat 32 (Janus.Float.inf Janus.Float.binary32 neg)
        else BitVec.ofNat 32 (Janus.Float.maxNormal Janus.Float.binary32 neg))) s := by
  by_cases h : c <;> simp only [h, ite_true, ite_false, run_ME_FPInfinity32, run_ME_FPMaxNormal32]

theorem FPInf32_pure (neg : Bool) :
    FPInfinity (if neg then 1#1 else 0#1) 32 = pure (BitVec.ofNat 32 (Janus.Float.inf Janus.Float.binary32 neg)) :=
  funext fun s => run_FPInfinity32 s neg
theorem FPMax32_pure (neg : Bool) :
    FPMaxNormal (if neg then 1#1 else 0#1) 32 = pure (BitVec.ofNat 32 (Janus.Float.maxNormal Janus.Float.binary32 neg)) :=
  funext fun s => run_FPMaxNormal32 s neg
theorem FPZero32_pure (neg : Bool) :
    FPZero (if neg then 1#1 else 0#1) 32 = pure (BitVec.ofNat 32 (Janus.Float.zero Janus.Float.binary32 neg)) :=
  funext fun s => run_FPZero32 s neg
theorem FPInf32_0 : FPInfinity 0#1 32 = pure (BitVec.ofNat 32 (Janus.Float.inf Janus.Float.binary32 false)) :=
  FPInf32_pure false
theorem FPInf32_1 : FPInfinity 1#1 32 = pure (BitVec.ofNat 32 (Janus.Float.inf Janus.Float.binary32 true)) :=
  FPInf32_pure true
theorem FPMax32_0 : FPMaxNormal 0#1 32 = pure (BitVec.ofNat 32 (Janus.Float.maxNormal Janus.Float.binary32 false)) :=
  FPMax32_pure false
theorem FPMax32_1 : FPMaxNormal 1#1 32 = pure (BitVec.ofNat 32 (Janus.Float.maxNormal Janus.Float.binary32 true)) :=
  FPMax32_pure true
theorem FPZero32_0 : FPZero 0#1 32 = pure (BitVec.ofNat 32 (Janus.Float.zero Janus.Float.binary32 false)) :=
  FPZero32_pure false
theorem FPZero32_1 : FPZero 1#1 32 = pure (BitVec.ofNat 32 (Janus.Float.zero Janus.Float.binary32 true)) :=
  FPZero32_pure true

theorem liftM_pure_ME {β α : Type} (x : α) : (liftM (pure x : SailM α) : SailME β α) = pure x := rfl

theorem ite_pure_ME {β α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then (pure a : SailME β α) else pure b) = pure (if c then a else b) := by split <;> rfl

theorem run_ME_ovf2 {β : Type} {w : Nat} {s : SState} (hc : LinuxEL0Config s) (fpcr : BitVec 64) (c : Prop)
    [Decidable c] (r : BitVec w) (y : real × BitVec w) (msg : String)
    (hen : c → fpcr.getLsbD (fpExcBit .FPExc_Overflow + 8) = false) (v : BitVec 64) :
    (ExceptT.run (if c then (fun _ => ((1 : real), r)) <$> liftM (FPProcessException .FPExc_Overflow fpcr)
        else (fun _ => y) <$> liftM (sail_assert true msg) : SailME β (real × BitVec w))).run (s.set .FPSR v) =
      .ok (.ok (if c then (1, r) else y)) (s.set .FPSR (v ||| BitVec.ofNat 64 (if c then 4 else 0))) := by
  by_cases h : c
  · simp only [h, ite_true, run_ME_map, run_ME_lift, run_PE_set hc _ fpcr (hen h)]; rfl
  · simp only [h, ite_false, run_ME_map, run_ME_lift, run_sail_assert_true, BitVec.ofNat_eq_ofNat, BitVec.or_zero]

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by simp [h]
theorem ite_f {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) (a b : α) : (if c then a else b) = b := by simp [h]

theorem ofNat_ite (w : Nat) (c : Prop) [Decidable c] (a b : Nat) :
    BitVec.ofNat w (if c then a else b) = if c then BitVec.ofNat w a else BitVec.ofNat w b := by split <;> rfl

theorem run_UsingAArch32_set {s : SState} (hc : LinuxEL0Config s) (v : BitVec 64) :
    (UsingAArch32 ()).run (s.set .FPSR v) = .ok false (s.set .FPSR v) := run_UsingAArch32 (hc.set_FPSR v)

theorem run_readReg_FPSR_set (s : SState) (v : RegisterType .FPSR) :
    (readReg .FPSR).run (s.set .FPSR v) = .ok v (s.set .FPSR v) := run_readReg (get?_set_FPSR s v)

theorem upd_bit3 (x : BitVec 64) : Sail.BitVec.updateSubrange x 3 3 1#1 = x ||| BitVec.ofNat 64 8 :=
  update_one_or x 3 (by decide)

theorem ipow8 : (2 : Int) ^ (8 : Int) = 256 := by decide
theorem ipow23 : (2 : Int) ^ (23 : Int) = 8388608 := by decide
theorem ipow24 : (2 : Int) ^ (24 : Int) = 16777216 := by decide
theorem fst_ite {α β : Type} (c : Prop) [Decidable c] (a b : α × β) :
    (if c then a else b).1 = if c then a.1 else b.1 := by split <;> rfl
theorem snd_ite {α β : Type} (c : Prop) [Decidable c] (a b : α × β) :
    (if c then a else b).2 = if c then a.2 else b.2 := by split <;> rfl

theorem testBit_ite (c : Prop) [Decidable c] (a b i : Nat) :
    Nat.testBit (if c then a else b) i = if c then Nat.testBit a i else Nat.testBit b i := by
  split <;> rfl

set_option hygiene false in
macro "rb_leaf_simp" : tactic => `(tactic|
    simp (config := { contextual := true }) [run_ME_ifPE hc, run_ME_ifPE' hc, fpExcBit, hOF, hUF, hIX, hT,
      run_ME_ovf2 hc fpcr, run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, ofNat_ite,
      run_PE_set hc, run_FPZero32, run_readReg, fst_ite, snd_ite, Except.map, fdiv16, run_map, run_bind, run_pure,
      run_UsingAArch32_set hc])

set_option maxHeartbeats 20000000 in
theorem run_FPRoundBase32_rb {s : SState} (hc : LinuxEL0Config s) (hism : (InStreamingMode ()).run s = .ok false s)
    (fpcr : BitVec 64) (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (m : Nat) (hm : m ≠ 0) (e : Int)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs)
    (hOF : Nat.testBit (rb32Of fpcr.toNat rm neg m e).2.1 2 = true → fpcr.getLsbD 10 = false)
    (hUF : Nat.testBit (rb32Of fpcr.toNat rm neg m e).2.1 3 = true → fpcr.getLsbD 11 = false)
    (hIX : Nat.testBit (rb32Of fpcr.toNat rm neg m e).2.1 4 = true → fpcr.getLsbD 12 = false) :
    (FPRoundBase__1 (sval neg m e) fpcr (aslRM rm) false true 32).run s =
      let o := rb32Of fpcr.toNat rm neg m e
      .ok o.1 (s.set .FPSR (xs ||| BitVec.ofNat 64 (o.2.1 ||| o.2.2))) := by
  have hp := mag_pos m hm e
  have hne0 : sval neg m e ≠ 0 := by
    cases neg
    · simp only [sval, Bool.false_eq_true, ite_false]; exact fun h => Rat.lt_irrefl (h ▸ hp)
    · simp only [sval, ite_true]; intro h
      have : (m : Rat) * 2 ^ e = 0 := by rw [← Rat.neg_neg ((m : Rat) * 2 ^ e), h, Rat.neg_zero]
      exact Rat.lt_irrefl (this ▸ hp)
  have hne : ((sval neg m e) != 0) = true := by simpa using hne0
  have hr' : (aslRM rm != .FPRounding_TIEAWAY) = true := by cases rm <;> first | decide | exact absurd rfl hrm
  have hA0 := rd_nonneg m (e - (max ((Nat.log2 m : Int) + e) (-126) - 23))
  have hAu0 := rd_nonneg m (23 - (Nat.log2 m : Int))
  have e0 : s = s.set .FPSR xs := (SState.set_same s .FPSR xs hx).symm
  rw [e0] at hism
  conv => lhs; rw [e0]
  simp only [rb32Of] at hOF hUF hIX ⊢
  unfold FPRoundBase__1
  rw [run_SailME_run]
  cfg_simp [run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, undefined_real, undefined_FPRounding,
    hne, hr', sval_sign neg m hm e, fpr_loop1 m hm e, fpr_loop2 m hm e,
    HaveAltFP, run_IsFeatureImplemented hc, run_IsFeatureImplemented (hc.set_FPSR xs), run_UsingAArch32 (hc.set_FPSR xs), sc32, su32,
    ipow8, ipow23, ipow24, fst_ite, snd_ite]
  simp only [get_AH, get_FZ, get_UFE, ofBool_eq_one] at *
  generalize sub_real ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23)))
    (to_real (round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23))))) = Er at *
  generalize sub_real ((m : Rat) * 2 ^ (23 - (Nat.log2 m : Int)))
    (to_real (round_down ((m : Rat) * 2 ^ (23 - (Nat.log2 m : Int))))) = Eu at *
  generalize round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23))) = A at *
  generalize round_down ((m : Rat) * 2 ^ (23 - (Nat.log2 m : Int))) = Au at *
  generalize (Nat.log2 m : Int) + e = E at *
  simp only [Janus.Arm64.FP.ah, Janus.Arm64.FP.fz, Janus.Arm64.FP.ufe, Janus.Arm64.FP.fpcrBit] at *
  have hT0 : ∀ rm, rbTiny false rm neg E Au Eu = false := fun rm => by simp [rbTiny]
  by_cases hT : rbTiny true rm neg E Au Eu = true
  all_goals cases rm
  all_goals try exact absurd rfl hrm
  all_goals
    by_cases hAH : fpcr.toNat / 2 ^ 1 % 2 = 1 <;> by_cases hFZ : fpcr.toNat / 2 ^ 24 % 2 = 1 <;>
      by_cases hUFE : fpcr.toNat / 2 ^ 11 % 2 = 1 <;> by_cases hE : E < -126
  all_goals
    fp_simp [aslRM, rbRU, rbOTI, rbTiny, rbBE2, hAH, hFZ, hUFE, hism, hE, hT0, testBit_ite, Nat.testBit_or, upd_bit3,
      fst_ite, snd_ite, ipow8, ipow23, ipow24] at hT
  all_goals
    fp_simp [aslRM, rb32, rbRU, rbOTI, rbTiny, rbBE2, hAH, hFZ, hUFE, hism, hE, hT0, run_ME_bind, run_ME_lift, run_ME_pure,
        run_ME_map, run_ME_throw, testBit_ite, Nat.testBit_or, upd_bit3, fst_ite, snd_ite, ipow8, ipow23, ipow24,
        FPInf32_pure, FPMax32_pure, FPZero32_pure, FPInf32_0, FPInf32_1, FPMax32_0, FPMax32_1, FPZero32_0, FPZero32_1,
        liftM_pure_ME, ite_pure_ME]
      at hOF hUF hIX ⊢
  all_goals try simp only [ite_t hT, hT, true_implies, false_implies, imp_false, not_true_eq_false,
    not_false_eq_true, Classical.not_not, and_true, true_and, and_false, false_and] at hOF hUF hIX ⊢
  all_goals try (have hT' := fun (h : _ ∧ ¬ _) => h.2 (hT h.1)
                 simp only [ite_f hT', eq_true hT, eq_false hT', true_implies, false_and, and_false, false_or,
                   or_false, ↓reduceIte] at hOF hUF hIX ⊢)
  all_goals
    rb_leaf_simp
  all_goals try (rw [run_readReg_FPSR_set]; rb_leaf_simp)
  all_goals try refine ⟨?_, ?_⟩
  all_goals try (first
         | rfl
         | (apply bits_ite
            erw [BitVec.toNat_append, BitVec.toNat_append]
            refine enc_fin neg _ _ _ _ (by decide) (by decide) _ rfl _ _ (isub7 _ ?_) (isub22 _ ?_)
            all_goals (repeat' split) <;> first | omega | (apply fdiv_nonneg; omega) | decide)
         | (congr 1
            simp only [ofNat_or, ofNat_ite, BitVec.or_assoc, Nat.or_zero, BitVec.ofNat_eq_ofNat, BitVec.or_zero]
            try ac_rfl))

end JanusASL.Proofs
