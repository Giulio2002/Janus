import JanusASL.Proofs.Step

/-! # Proved: RBIT, CLZ, CLS (data-processing, 1 source)

The ASL bodies are loops (`for i = 0 to N-1`, and `HighestSetBit`'s descending loop with an early
`return`); `run_forIn_pure` and `hsb_loop` turn the generated `IntRange` loops into folds, and
the folds are related to Janus' `rbitNat`/`clzNat` bit by bit. -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- `for i in [start:stop]i` (step 1) with a pure body, as a fold. -/
def intFold {β : Type} (g : Int → β → β) (i stop : Int) (b : β) : β :=
  if i ≤ stop then intFold g (i + 1) stop (g i b) else b
termination_by (stop - i + 1).toNat

theorem run_forIn_pure {β : Type} (start stop : Int) (hsp : (1 : Int) ≠ 0) (init : β) (g : Int → β → β) (s : SState) :
    (forIn ({ start := start, stop := stop, step_pos := hsp } : IntRange) init
      (fun i b => (pure (ForInStep.yield (g i b)) : SailM (ForInStep β)))).run s =
      .ok (intFold g start stop init) s := by
  rw [show forIn ({ start := start, stop := stop, step_pos := hsp } : IntRange) init
      (fun i b => (pure (ForInStep.yield (g i b)) : SailM (ForInStep β))) =
    IntRange.forIn' ({ start := start, stop := stop, step_pos := hsp } : IntRange) init
      (fun a _ b => (pure (ForInStep.yield (g a b)) : SailM (ForInStep β))) from rfl]
  unfold IntRange.forIn'
  simp only
  suffices H : ∀ (n : Nat) (i : Int) (hs) (b : β), start ≤ i → (stop - i + 1).toNat = n →
      (IntRange.forIn'.loop ({ start := start, stop := stop, step_pos := hsp } : IntRange)
        (fun a _ b => (pure (ForInStep.yield (g a b)) : SailM (ForInStep β))) b i hs).run s =
        .ok (intFold g i stop b) s from H _ start _ init (Int.le_refl _) rfl
  intro n
  induction n with
  | zero =>
    intro i hs b hi hn
    rw [IntRange.forIn'.loop, intFold]
    have : ¬ i ≤ stop := by omega
    simp [Membership.mem, this]
  | succ n ih =>
    intro i hs b hi hn
    rw [IntRange.forIn'.loop, intFold]
    have : i ≤ stop := by omega
    have hm : i ∈ ({ start := start, stop := stop, step_pos := hsp } : IntRange) := by
      simp only [Membership.mem]; simp; omega
    simp only [hm, dite_true, this, ite_true, run_bind, run_pure]
    exact ih (i + 1) _ (g i b) (by omega) (by omega)

theorem getLsbD_update {N : Nat} (r : BitVec N) (p : Nat) (b : BitVec 1) (k : Nat) (hp : p < N) :
    (Sail.BitVec.update r p b).getLsbD k = if k = p then b.getLsbD 0 else r.getLsbD k := by
  simp only [Sail.BitVec.update, Sail.BitVec.updateSubrange']
  by_cases hk : k = p
  · subst hk; simp [BitVec.getLsbD_shiftLeft, hp]
  · simp only [hk, ite_false]
    by_cases hkN : k < N
    · by_cases hkp : k < p
      · simp [BitVec.getLsbD_shiftLeft, hkN, hkp]
      · have hb : b.getLsbD (k - p) = false := BitVec.getLsbD_of_ge b (k - p) (by omega)
        simp [BitVec.getLsbD_shiftLeft, hkN, hb, hkp]
        intro _; omega
    · simp [BitVec.getLsbD_of_ge r k (by omega), BitVec.getLsbD_shiftLeft, hkN]

theorem rbitNat_lt (n v : Nat) : Janus.Arm64.rbitNat n v < 2 ^ n := by
  induction n generalizing v with
  | zero => simp [Janus.Arm64.rbitNat]
  | succ n ih =>
    simp only [Janus.Arm64.rbitNat]
    have := ih (v / 2); have : v % 2 ≤ 1 := by omega
    rw [Nat.pow_succ]
    have : v % 2 * 2 ^ n ≤ 2 ^ n := by
      calc v % 2 * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ n := Nat.one_mul _
    omega

theorem rbitNat_testBit (n v i : Nat) :
    (Janus.Arm64.rbitNat n v).testBit i = (decide (i < n) && v.testBit (n - 1 - i)) := by
  induction n generalizing v i with
  | zero => simp [Janus.Arm64.rbitNat]
  | succ n ih =>
    simp only [Janus.Arm64.rbitNat]
    rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (rbitNat_lt n (v / 2))]
    split
    · rw [ih]; simp [*, Nat.testBit_div_two]
      rw [show n - 1 - i + 1 = n - i by omega]
      simp; omega
    · by_cases hi : i = n
      · subst hi; simp
      · have : i - n ≥ 1 := by omega
        have h2 : (v % 2).testBit (i - n) = false := Nat.testBit_lt_two_pow (by
          calc v % 2 < 2 := Nat.mod_lt _ (by decide)
            _ = 2 ^ 1 := rfl
            _ ≤ 2 ^ (i - n) := Nat.pow_le_pow_right (by decide) this)
        simp [h2]; omega

theorem getLsbD_Bit_access {N : Nat} (x : BitVec N) (i : Nat) (hi : i < N) :
    (Bit (Sail.BitVec.access x i)).getLsbD 0 = x.getLsbD i := by
  simp [Bit, Sail.BitVec.access, BitVec.getLsbD_eq_getElem hi, getElem!_pos x i hi]

/-- The RBIT loop body. -/
def rbitStep {N : Nat} (x : BitVec N) (i : Int) (r : BitVec N) : BitVec N :=
  Sail.BitVec.update r ((N : Int) - 1 - i).toNat (Bit (Sail.BitVec.access x i.toNat))

theorem rbit_fold {N : Nat} (x : BitVec N) (hN : 0 < N) :
    ∀ (n j : Nat) (b : BitVec N), N - j = n → j ≤ N → ∀ k,
      (intFold (rbitStep x) j ((N : Int) - 1) b).getLsbD k =
        if k < N ∧ N - 1 - k ≥ j then x.getLsbD (N - 1 - k) else b.getLsbD k := by
  intro n
  induction n with
  | zero =>
    intro j b hj hjN k
    rw [intFold]
    simp only [show ¬ ((j : Int) ≤ (N : Int) - 1) by omega, ite_false]
    rw [if_neg (by omega)]
  | succ n ih =>
    intro j b hj hjN k
    rw [intFold]
    simp only [show ((j : Int) ≤ (N : Int) - 1) by omega, ite_true]
    have := ih (j + 1) (rbitStep x j b) (by omega) (by omega) k
    rw [show (j : Int) + 1 = ((j + 1 : Nat) : Int) by omega, this]
    simp only [rbitStep]
    rw [getLsbD_update _ _ _ _ (by omega)]
    by_cases h1 : k < N ∧ N - 1 - k ≥ j + 1
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1]
      by_cases h2 : k = ((N : Int) - 1 - (j : Int)).toNat
      · rw [if_pos h2, if_pos (by omega), show (j : Int).toNat = j by omega, getLsbD_Bit_access x j (by omega)]
        congr 1; omega
      · rw [if_neg h2, if_neg (by omega)]

theorem rbit_eq {N : Nat} (x : BitVec N) (hN : 0 < N) :
    intFold (rbitStep x) 0 ((N : Int) - 1) 0#N = BitVec.ofNat N (Janus.Arm64.rbitNat N x.toNat) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  have := rbit_fold x hN N 0 0#N (by omega) (by omega) k
  simp only [Int.natCast_zero] at this
  rw [this, if_pos (by omega)]
  simp [BitVec.getLsbD_ofNat, rbitNat_testBit, hk, BitVec.getLsbD]

/-- `HighestSetBit` of the bits `i..0` of `x`, as `ExceptT` computes it. -/
def hsbRes {N : Nat} (x : BitVec N) (i : Int) : Except Int Int :=
  if 0 ≤ i then (if (Sail.BitVec.access x i.toNat == 1#1) = true then .error i else hsbRes x (i - 1)) else .ok (-1)
termination_by (i + 1).toNat

theorem hsb_loop {N : Nat} (x : BitVec N) (start : Int) (hsp : (-1 : Int) ≠ 0) :
    ∀ (n : Nat) (i : Int) (hs), i ≤ start → (i + 1).toNat = n →
      ((IntRange.forIn'.loop ({ start := start, stop := 0, step := -1, step_pos := hsp } : IntRange)
        (fun i _ (_ : Unit) => (do
          let loop_vars ← (if (Sail.BitVec.access x i.toNat == 1#1) = true then throw i else pure () : ExceptT Int Id Unit)
          pure (ForInStep.yield loop_vars) : ExceptT Int Id (ForInStep Unit))) () i hs) >>= fun _ =>
            (pure (-1) : ExceptT Int Id Int)).run = hsbRes x i := by
  intro n
  induction n with
  | zero =>
    intro i hs hi hn
    rw [IntRange.forIn'.loop, hsbRes]
    have h1 : ¬ i ∈ ({ start := start, stop := 0, step := -1, step_pos := hsp } : IntRange) := by
      simp [Membership.mem]; omega
    simp only [h1, dite_false, show ¬ (0 ≤ i) by omega, ite_false]
    rfl
  | succ n ih =>
    intro i hs hi hn
    rw [IntRange.forIn'.loop, hsbRes]
    have h1 : i ∈ ({ start := start, stop := 0, step := -1, step_pos := hsp } : IntRange) := by
      simp [Membership.mem]; omega
    simp only [h1, dite_true, show (0 ≤ i) by omega, ite_true]
    by_cases hb : (Sail.BitVec.access x i.toNat == 1#1) = true
    · simp only [hb, ite_true]; rfl
    · simp only [hb, ite_false, Bool.false_eq_true]
      have := ih (i + -1) (by rw [Int.emod_neg]; exact Int.emod_one _) (by omega) (by omega)
      rw [show i - 1 = i + -1 by omega]
      rw [← this]
      rfl

def exVal : Except Int Int → Int
  | .error e => e
  | .ok e => e

theorem access_eq_one {N : Nat} (x : BitVec N) (i : Nat) (hi : i < N) :
    (Sail.BitVec.access x i == 1#1) = x.toNat.testBit i := by
  have : x.toNat.testBit i = x.getLsbD i := rfl
  rw [this]
  simp only [Sail.BitVec.access, BitVec.getLsbD_eq_getElem hi, getElem!_pos x i hi]
  cases x[i] <;> rfl

theorem hsbRes_val {N : Nat} (x : BitVec N) :
    ∀ (i : Nat), i < N → exVal (hsbRes x i) = (i : Int) - Janus.Arm64.clzNat (i + 1) x.toNat := by
  intro i
  induction i with
  | zero =>
    intro h0
    rw [hsbRes]
    simp only [show (0 : Int) ≤ ((0 : Nat) : Int) by omega, ite_true, show ((0 : Nat) : Int).toNat = 0 from rfl,
      access_eq_one x _ h0]
    simp only [Janus.Arm64.clzNat]
    by_cases hb : x.toNat.testBit 0 = true
    · simp [hb, exVal]
    · rw [hsbRes]; simp [hb, exVal]
  | succ i ih =>
    intro hi
    rw [hsbRes]
    simp only [show (0 : Int) ≤ ((i + 1 : Nat) : Int) by omega, ite_true,
      show ((i + 1 : Nat) : Int).toNat = i + 1 by omega, access_eq_one x _ hi]
    rw [Janus.Arm64.clzNat]
    by_cases hb : x.toNat.testBit (i + 1) = true
    · simp [hb, exVal]
    · simp only [hb, ite_false, Bool.false_eq_true]
      rw [show ((i + 1 : Nat) : Int) - 1 = ((i : Nat) : Int) by omega, ih (by omega)]
      omega

theorem HighestSetBit_eq {N : Nat} (x : BitVec N) (hN : 0 < N) :
    HighestSetBit x = ((N : Int) - 1) - Janus.Arm64.clzNat N x.toNat := by
  unfold HighestSetBit
  simp only
  have hrun : ∀ m : ExceptM Int Int, ExceptM.run m = exVal (ExceptT.run m) := by
    intro m; unfold ExceptM.run exVal; split <;> simp_all
  rw [hrun]
  have hl : (Sail.BitVec.length x : Int) - 1 = ((N - 1 : Nat) : Int) := by simp [Sail.BitVec.length]; omega
  simp only [hl]
  have := hsb_loop x ((N - 1 : Nat) : Int) (by decide) (N - 1 + 1) ((N - 1 : Nat) : Int) (by simp) (Int.le_refl _)
    (by omega)
  rw [show (forIn ({ start := ((N - 1 : Nat) : Int), stop := 0, step := -1, step_pos := _ } : IntRange) () _) =
    IntRange.forIn' ({ start := ((N - 1 : Nat) : Int), stop := 0, step := -1, step_pos := (by decide) } : IntRange) ()
      (fun i _ (_ : Unit) => (do
          let loop_vars ← (if (Sail.BitVec.access x i.toNat == 1#1) = true then throw i else pure () : ExceptT Int Id Unit)
          pure (ForInStep.yield loop_vars) : ExceptT Int Id (ForInStep Unit))) from rfl]
  unfold IntRange.forIn'
  simp only
  rw [this, hsbRes_val x (N - 1) (by omega)]
  rw [show N - 1 + 1 = N by omega]

theorem clz_eq {N : Nat} (x : BitVec N) (hN : 0 < N) :
    CountLeadingZeroBits x = (Janus.Arm64.clzNat N x.toNat : Int) := by
  unfold CountLeadingZeroBits
  rw [HighestSetBit_eq x hN]
  simp [Sail.BitVec.length]; omega

theorem cls_eq64 (x : BitVec 64) :
    CountLeadingSignBits x = (Janus.Arm64.clzNat 63 ((x.toNat / 2) ^^^ (x.toNat % 2 ^ 63)) : Int) := by
  unfold CountLeadingSignBits
  rw [clz_eq _ (by simp [Sail.BitVec.length])]
  congr 2
  have e1 : (Sail.BitVec.extractLsb x ((((64 : Nat) : Int) - 1).toNat) 1).toNat = x.toNat / 2 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]; omega
  have e2 : (Sail.BitVec.extractLsb x ((((64 : Nat) : Int) - 2).toNat) 0).toNat = x.toNat % 2 ^ 63 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
  rw [BitVec.toNat_xor]
  simp only [BitVec.toNat_setWidth, Sail.BitVec.length]
  rw [e1, e2]
  simp

theorem cls_eq32 (x : BitVec 32) :
    CountLeadingSignBits x = (Janus.Arm64.clzNat 31 ((x.toNat / 2) ^^^ (x.toNat % 2 ^ 31)) : Int) := by
  unfold CountLeadingSignBits
  rw [clz_eq _ (by simp [Sail.BitVec.length])]
  congr 2
  have e1 : (Sail.BitVec.extractLsb x ((((32 : Nat) : Int) - 1).toNat) 1).toNat = x.toNat / 2 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]; omega
  have e2 : (Sail.BitVec.extractLsb x ((((32 : Nat) : Int) - 2).toNat) 0).toNat = x.toNat % 2 ^ 31 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
  rw [BitVec.toNat_xor]
  simp only [BitVec.toNat_setWidth, Sail.BitVec.length]
  rw [e1, e2]
  simp


set_option maxHeartbeats 4000000 in
theorem run_execute_rbit {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d n : Nat} (hd : d < 32) (hn : n < 32) :
    ∃ s', (execute_aarch64_instrs_integer_arithmetic_rbit d N n).run s = .ok () s' ∧
      Rel (Janus.Arm64.execRbit N js n d) s' ∧ Frame s s' := by
  have hN0 : 0 < N := by omega
  obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd hN (BitVec.ofNat N (Janus.Arm64.rbitNat N (js.getX N n).toNat))
  refine ⟨s', ?_, by simpa [Janus.Arm64.execRbit] using hr, hf⟩
  simp only [execute_aarch64_instrs_integer_arithmetic_rbit, run_bind, run_X_read_rel h hn hN,
    run_undefined_bitvector]
  rw [run_forIn_pure 0 ((N : Int) - 1) _ 0#N
    (fun i r => Sail.BitVec.update r (((N : Int) - 1 - i).toNat) (Bit (Sail.BitVec.access (js.getX N n) i.toNat)))]
  have e : intFold (fun i r => Sail.BitVec.update r (((N : Int) - 1 - i).toNat)
      (Bit (Sail.BitVec.access (js.getX N n) i.toNat))) 0 ((N : Int) - 1) 0#N = _ := rbit_eq (js.getX N n) hN0
  simp only [run_pure, e]
  exact hs'

theorem run_decode_rbit (Rd Rn : BitVec 5) (sf : BitVec 1) (s : SState) :
    (decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit Rd Rn sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_rbit Rd.toNat (if sf == 1#1 then 64 else 32) Rn.toNat).run s := rfl

theorem cnt_eq {N : Nat} (hN : N = 32 ∨ N = 64) (x : BitVec N) (cls : Bool) :
    BitVec.setWidth N (integer_subrange (if cls then CountLeadingSignBits x else CountLeadingZeroBits x)
      ((N : Int) - 1) 0) =
    BitVec.ofNat N (if cls then Janus.Arm64.clzNat (N - 1) ((x.toNat / 2) ^^^ (x.toNat % 2 ^ (N - 1)))
      else Janus.Arm64.clzNat N x.toNat) := by
  rw [integer_subrange_eq N (by omega)]
  cases cls
  · simp [clz_eq x (by omega)]
  · rcases hN with rfl | rfl
    · simp [cls_eq32]
    · simp [cls_eq64]

set_option maxHeartbeats 4000000 in
theorem run_execute_cnt {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d n : Nat} (hd : d < 32) (hn : n < 32) (cls : Bool) :
    ∃ s', (execute_aarch64_instrs_integer_arithmetic_cnt d N n (if cls then .CountOp_CLS else .CountOp_CLZ)).run s =
        .ok () s' ∧
      Rel (if cls then Janus.Arm64.execCls N js n d else Janus.Arm64.execClz N js n d) s' ∧ Frame s s' := by
  have hN0 : 0 < N := by omega
  obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd hN
    (BitVec.ofNat N (if cls then Janus.Arm64.clzNat (N - 1) (((js.getX N n).toNat / 2) ^^^ ((js.getX N n).toNat % 2 ^ (N - 1)))
      else Janus.Arm64.clzNat N (js.getX N n).toNat))
  refine ⟨s', ?_, by cases cls <;> simpa [Janus.Arm64.execCls, Janus.Arm64.execClz] using hr, hf⟩
  simp only [execute_aarch64_instrs_integer_arithmetic_cnt, run_bind, run_X_read_rel h hn hN, run_undefined_int,
    run_pure]
  rw [← cnt_eq hN _ cls] at hs'
  cases cls <;> exact hs'

theorem run_decode_clz (Rd Rn : BitVec 5) (op sf : BitVec 1) (hop : op = 0#1) (s : SState) :
    (decode_clz_int_aarch64_instrs_integer_arithmetic_cnt Rd Rn op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_cnt Rd.toNat (if sf == 1#1 then 64 else 32) Rn.toNat
        (if false then .CountOp_CLS else .CountOp_CLZ)).run s := by
  subst hop; rfl

theorem run_decode_cls (Rd Rn : BitVec 5) (op sf : BitVec 1) (hop : op = 1#1) (s : SState) :
    (decode_cls_int_aarch64_instrs_integer_arithmetic_cnt Rd Rn op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_cnt Rd.toNat (if sf == 1#1 then 64 else 32) Rn.toNat
        (if true then .CountOp_CLS else .CountOp_CLZ)).run s := by
  subst hop; rfl

theorem run_execute_clz' {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d n : Nat} (hd : d < 32) (hn : n < 32) :
    ∃ s', (execute_aarch64_instrs_integer_arithmetic_cnt d N n (if false then .CountOp_CLS else .CountOp_CLZ)).run s =
        .ok () s' ∧ Rel (Janus.Arm64.execClz N js n d) s' ∧ Frame s s' :=
  run_execute_cnt h hN hd hn false

theorem run_execute_cls' {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d n : Nat} (hd : d < 32) (hn : n < 32) :
    ∃ s', (execute_aarch64_instrs_integer_arithmetic_cnt d N n (if true then .CountOp_CLS else .CountOp_CLZ)).run s =
        .ok () s' ∧ Rel (Janus.Arm64.execCls N js n d) s' ∧ Frame s s' :=
  run_execute_cnt h hN hd hn true

theorem fld10_1 {w : Nat} (hw : w < 2 ^ 32) (h3 : (w / 2 ^ 10) % 64 = 5) : fld w 10 1 = 1#1 :=
  BitVec.eq_of_toNat_eq (by rw [fld_toNat w 10 1 hw]; simp; omega)
theorem fld10_0 {w : Nat} (hw : w < 2 ^ 32) (h3 : (w / 2 ^ 10) % 64 = 4) : fld w 10 1 = 0#1 :=
  BitVec.eq_of_toNat_eq (by rw [fld_toNat w 10 1 hw]; simp; omega)
set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 719 (`decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit`). -/
theorem run_DataProcReg_dp1_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 1024 = 726) (h1 : (w / 2 ^ 16) % 32 = 0) (h2 : (w / 2 ^ 10) % 64 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit (fld w 0 5) (fld w 5 5) (fld w 31 1)).run (s.set .SEE 719) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f33 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486853#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486852#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486855#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f39 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f40 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f41 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f42 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486854#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f43 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f44 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f45 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f46 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f47 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f48 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f49 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f50 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f51 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t52_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486848#21 : BitVec 21)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, t52_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 719) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 128 (`decode_clz_int_aarch64_instrs_integer_arithmetic_cnt`). -/
theorem run_DataProcReg_dp1_4 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 1024 = 726) (h1 : (w / 2 ^ 16) % 32 = 0) (h2 : (w / 2 ^ 10) % 64 = 4) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_clz_int_aarch64_instrs_integer_arithmetic_cnt (fld w 0 5) (fld w 5 5) (fld w 10 1) (fld w 31 1)).run (s.set .SEE 128) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f33 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486853#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t34_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486852#21 : BitVec 21)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, t34_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 128) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 127 (`decode_cls_int_aarch64_instrs_integer_arithmetic_cnt`). -/
theorem run_DataProcReg_dp1_5 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 1024 = 726) (h1 : (w / 2 ^ 16) % 32 = 0) (h2 : (w / 2 ^ 10) % 64 = 5) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_cls_int_aarch64_instrs_integer_arithmetic_cnt (fld w 0 5) (fld w 5 5) (fld w 10 1) (fld w 31 1)).run (s.set .SEE 127) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t33_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486853#21 : BitVec 21)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, t33_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 127) = True from by decide]
  all_goals rfl


theorem decode_rbit_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 0) :
    Janus.Arm64.decode w = some (.rbit (Janus.Arm64.bit w 31) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (Janus.Arm64.bits w 28 25 % 2 = 0 && Janus.Arm64.bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : Janus.Arm64.bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : Janus.Arm64.bit w 28 = true := by simp only [bit_def]; simp; omega
  have a7 : Janus.Arm64.bits w 24 21 = 0b0110 := by simp only [bits_def]; omega
  have a8 : Janus.Arm64.bit w 29 = false := by simp only [bit_def]; simp; omega
  have a9 : Janus.Arm64.bit w 30 = true := by simp only [bit_def]; simp; omega
  have a10 : ¬ Janus.Arm64.bits w 20 16 ≠ 0 := by simp only [bits_def]; omega
  have a11 : Janus.Arm64.bits w 15 10 = 0 := by simp only [bits_def]; omega
  simp only [Janus.Arm64.decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true,
    Janus.Arm64.decodeDPReg, a6, a7, a8, a9, a10, a11, Bool.not_true, Bool.not_false]
  all_goals simp

theorem decode_clz_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 4) :
    Janus.Arm64.decode w = some (.clz (Janus.Arm64.bit w 31) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (Janus.Arm64.bits w 28 25 % 2 = 0 && Janus.Arm64.bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : Janus.Arm64.bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : Janus.Arm64.bit w 28 = true := by simp only [bit_def]; simp; omega
  have a7 : Janus.Arm64.bits w 24 21 = 0b0110 := by simp only [bits_def]; omega
  have a8 : Janus.Arm64.bit w 29 = false := by simp only [bit_def]; simp; omega
  have a9 : Janus.Arm64.bit w 30 = true := by simp only [bit_def]; simp; omega
  have a10 : ¬ Janus.Arm64.bits w 20 16 ≠ 0 := by simp only [bits_def]; omega
  have a11 : Janus.Arm64.bits w 15 10 = 4 := by simp only [bits_def]; omega
  simp only [Janus.Arm64.decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true,
    Janus.Arm64.decodeDPReg, a6, a7, a8, a9, a10, a11, Bool.not_true, Bool.not_false]
  all_goals simp

theorem decode_cls_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 5) :
    Janus.Arm64.decode w = some (.cls (Janus.Arm64.bit w 31) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (Janus.Arm64.bits w 28 25 % 2 = 0 && Janus.Arm64.bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : Janus.Arm64.bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : Janus.Arm64.bit w 28 = true := by simp only [bit_def]; simp; omega
  have a7 : Janus.Arm64.bits w 24 21 = 0b0110 := by simp only [bits_def]; omega
  have a8 : Janus.Arm64.bit w 29 = false := by simp only [bit_def]; simp; omega
  have a9 : Janus.Arm64.bit w 30 = true := by simp only [bit_def]; simp; omega
  have a10 : ¬ Janus.Arm64.bits w 20 16 ≠ 0 := by simp only [bits_def]; omega
  have a11 : Janus.Arm64.bits w 15 10 = 5 := by simp only [bits_def]; omega
  simp only [Janus.Arm64.decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true,
    Janus.Arm64.decodeDPReg, a6, a7, a8, a9, a10, a11, Bool.not_true, Bool.not_false]
  all_goals simp

set_option maxHeartbeats 8000000 in
theorem asl_rbit {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 0)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execRbit (if fld w 31 1 == 1#1 then 64 else 32) js (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      s2.regs.get? .__BranchTaken = some false := by
  rw [run_DecodeA64_DPReg hw (by omega), run_DataProcReg_dp1_0 hw h1 h2 h3 (see_entry _ _), run_decode_rbit]
  obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_rbit (h.entry (BitVec.ofNat 32 w) 719) (width_cases w)
    (fld_lt w 0 5) (fld_lt w 5 5)
  exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩

theorem rbit_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 0)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' := by
  let F : Nat → Janus.Arm64.State := fun N => Janus.Arm64.execRbit N js (fld w 5 5).toNat (fld w 0 5).toNat
  have hspec : ∀ N, (F N).pc = js.pc := by
    intro N; simp [F, Janus.Arm64.execRbit, Janus.Arm64.State.setX, Janus.Arm64.State.writeZR]; split <;> rfl
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_rbit hw h1 h2 h3 h (js.pc.toNat : Int)
  have e : F (if fld w 31 1 == 1#1 then 64 else 32) = if fld w 31 1 == 1#1 then F 64 else F 32 := by
    split <;> rfl
  have hrel' : Rel (if fld w 31 1 == 1#1 then F 64 else F 32) s2 := e ▸ hrel
  refine step_agree h ⟨s2, hrun, hrel', hbt⟩ (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_rbit_class hw h1 h2 h3)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  split <;> simp_all [Janus.Arm64.State.next, F]

set_option maxHeartbeats 8000000 in
theorem asl_clz {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 4)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execClz (if fld w 31 1 == 1#1 then 64 else 32) js (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      s2.regs.get? .__BranchTaken = some false := by
  rw [run_DecodeA64_DPReg hw (by omega), run_DataProcReg_dp1_4 hw h1 h2 h3 (see_entry _ _), run_decode_clz _ _ _ _ (fld10_0 hw h3)]
  obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_clz' (h.entry (BitVec.ofNat 32 w) 128) (width_cases w)
    (fld_lt w 0 5) (fld_lt w 5 5)
  exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩

theorem clz_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 4)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' := by
  let F : Nat → Janus.Arm64.State := fun N => Janus.Arm64.execClz N js (fld w 5 5).toNat (fld w 0 5).toNat
  have hspec : ∀ N, (F N).pc = js.pc := by
    intro N; simp [F, Janus.Arm64.execClz, Janus.Arm64.State.setX, Janus.Arm64.State.writeZR]; split <;> rfl
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_clz hw h1 h2 h3 h (js.pc.toNat : Int)
  have e : F (if fld w 31 1 == 1#1 then 64 else 32) = if fld w 31 1 == 1#1 then F 64 else F 32 := by
    split <;> rfl
  have hrel' : Rel (if fld w 31 1 == 1#1 then F 64 else F 32) s2 := e ▸ hrel
  refine step_agree h ⟨s2, hrun, hrel', hbt⟩ (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_clz_class hw h1 h2 h3)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  split <;> simp_all [Janus.Arm64.State.next, F]

set_option maxHeartbeats 8000000 in
theorem asl_cls {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 5)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execCls (if fld w 31 1 == 1#1 then 64 else 32) js (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      s2.regs.get? .__BranchTaken = some false := by
  rw [run_DecodeA64_DPReg hw (by omega), run_DataProcReg_dp1_5 hw h1 h2 h3 (see_entry _ _), run_decode_cls _ _ _ _ (fld10_1 hw h3)]
  obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_cls' (h.entry (BitVec.ofNat 32 w) 127) (width_cases w)
    (fld_lt w 0 5) (fld_lt w 5 5)
  exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩

theorem cls_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 5)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' := by
  let F : Nat → Janus.Arm64.State := fun N => Janus.Arm64.execCls N js (fld w 5 5).toNat (fld w 0 5).toNat
  have hspec : ∀ N, (F N).pc = js.pc := by
    intro N; simp [F, Janus.Arm64.execCls, Janus.Arm64.State.setX, Janus.Arm64.State.writeZR]; split <;> rfl
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_cls hw h1 h2 h3 h (js.pc.toNat : Int)
  have e : F (if fld w 31 1 == 1#1 then 64 else 32) = if fld w 31 1 == 1#1 then F 64 else F 32 := by
    split <;> rfl
  have hrel' : Rel (if fld w 31 1 == 1#1 then F 64 else F 32) s2 := e ▸ hrel
  refine step_agree h ⟨s2, hrun, hrel', hbt⟩ (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_cls_class hw h1 h2 h3)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  split <;> simp_all [Janus.Arm64.State.next, F]

end JanusASL.Proofs
