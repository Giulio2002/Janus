import JanusASL.Proofs.FP.Prim3

/-! # `V[n, 128] = result`: the vector-length computations of `V_set` under the Linux EL0 configuration -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem iter_succ_int (n : Nat) (a : Int) : iter (fun r : Int => r + 1) n a = a + n := by
  induction n generalizing a with
  | zero => simp [iter]
  | succ n ih => simp only [iter]; rw [ih]; omega

theorem ipow_int (r : Int) : (2 : Int) ^ r = (2 : Int) ^ r.toNat := rfl

theorem run_FloorPow2 (x : Nat) (hx : 1 ≤ x) (s : SState) : (FloorPow2 (x : Int)).run s = .ok (2 ^ Nat.log2 x) s := by
  unfold FloorPow2
  cfg_simp [run_sail_assert_true]
  have hx0 : x ≠ 0 := by omega
  have hl : forIn (m := SailM) Lean.Loop.mk (1 : Int) (fun _ (r : Int) =>
        if 2 ^ r ≤ (x : Int) then pure (ForInStep.yield (r + 1)) else pure (ForInStep.done r)) =
      pure ((1 : Int) + (Nat.log2 x : Nat)) := by
    have := forIn_loop_pure (m := SailM) (fun r : Int => decide (2 ^ r ≤ (x : Int))) (fun r => r + 1)
      (fun _ (r : Int) => if 2 ^ r ≤ (x : Int) then pure (ForInStep.yield (r + 1)) else pure (ForInStep.done r))
      (fun r => by by_cases h : 2 ^ r ≤ (x : Int) <;> simp [h]) (Nat.log2 x) 1 ?_ ?_
    · rw [this, iter_succ_int]
    · intro i hi
      rw [iter_succ_int]
      simp only [decide_eq_true_eq, ipow_int]
      have h1 : 2 ^ (i + 1) ≤ x := by
        calc 2 ^ (i + 1) ≤ 2 ^ Nat.log2 x := Nat.pow_le_pow_right (by decide) hi
          _ ≤ x := Nat.log2_self_le hx0
      have e : ((1 : Int) + (i : Int)).toNat = i + 1 := by omega
      rw [e]; exact_mod_cast h1
    · rw [iter_succ_int]
      simp only [decide_eq_false_iff_not, ipow_int, Int.not_le]
      have h1 : x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
      have e : ((1 : Int) + (Nat.log2 x : Int)).toNat = Nat.log2 x + 1 := by omega
      rw [e]; exact_mod_cast h1
  simp only [hx0, ite_false, hl, pure_bind]
  cfg_simp [run_sail_assert_true, ipow_int]
  have e : ((1 : Int) + (Nat.log2 x : Int)).toNat - 1 = Nat.log2 x := by omega
  rw [e]
  have hp : (0 ≤b ((2 : Int) ^ Nat.log2 x)) = true := by
    exact decide_eq_true (by exact_mod_cast Nat.zero_le (2 ^ Nat.log2 x))
  simp only [hp, run_sail_assert_true]
  congr 1

theorem run_CeilPow2 (x : Nat) (hx : 2 ≤ x) (s : SState) :
    (CeilPow2 (x : Int)).run s = .ok (2 ^ Nat.log2 (x - 1) * 2) s := by
  unfold CeilPow2
  have h1 : (x : Int) ≠ 0 := by omega
  have h2 : (x : Int) ≠ 1 := by omega
  have h3 : ((x : Int) - 1) = ((x - 1 : Nat) : Int) := by omega
  have h0 : x ≠ 0 := by omega
  simp only [h1, h2, h3, h0, beq_iff_eq, ite_false]
  show EStateM.bind (FloorPow2 ((x - 1 : Nat) : Int)) _ s = _
  have h : FloorPow2 ((x - 1 : Nat) : Int) s = .ok (2 ^ Nat.log2 (x - 1)) s := run_FloorPow2 (x - 1) (by omega) s
  simp only [EStateM.bind, h, pure, EStateM.pure]
  congr 1

theorem FloorPow2_512 : FloorPow2 512 = pure 512 := funext fun s => run_FloorPow2 512 (by decide) s
theorem FloorPow2_2048 : FloorPow2 2048 = pure 2048 := funext fun s => run_FloorPow2 2048 (by decide) s
theorem CeilPow2_512 : CeilPow2 512 = pure 512 := funext fun s => run_CeilPow2 512 (by decide) s
theorem CeilPow2_2048 : CeilPow2 2048 = pure 2048 := funext fun s => run_CeilPow2 2048 (by decide) s
theorem IsPow2_512 : IsPow2 512 = pure true := by
  funext s; unfold IsPow2; simp [FloorPow2_512, CeilPow2_512]
theorem IsPow2_2048 : IsPow2 2048 = pure true := by
  funext s; unfold IsPow2; simp [FloorPow2_2048, CeilPow2_2048]

theorem forIn_loop_step {m : Type → Type} [Monad m] [LawfulMonad m] [Lean.Order.MonadTail m] {β : Type}
    (f : Unit → β → m (ForInStep β)) (b : β) :
    forIn (m := m) Lean.Loop.mk b f = (do
      let r ← f () b
      match r with
      | ForInStep.done val => pure val
      | ForInStep.yield val => forIn (m := m) Lean.Loop.mk val f) := by
  show Lean.Loop.forIn _ _ _ = _
  rw [Lean.Loop.forIn_eq_of_monadTail]; rfl

theorem run_ImplSVE_512 (s : SState) : (ImplementedSVEVectorLength 512).run s = .ok 512 s := by
  unfold ImplementedSVEVectorLength
  rw [run_SailME_run]
  have hm : MaxImplementedVL () = 2048 := rfl
  have h1 : min (512 : Int) 2048 = 512 := by decide
  have h2 : (fdiv_int 512 128 * 128 == (512 : Int)) = true := by decide
  cfg_simp [run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, hm, Align_int, IsPow2_2048, IsPow2_512,
    h1, h2]
  rw [forIn_loop_step]
  cfg_simp [run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, IsPow2_512]

theorem run_ImplSME_128 {s : SState} (hs : s.regs.get? .__max_implemented_smeveclen = some 512) :
    (ImplementedSMEVectorLength 128).run s = .ok 128 s := by
  unfold ImplementedSMEVectorLength
  rw [run_SailME_run]
  have h1 : min (128 : Int) 512 = 128 := by decide
  have h2 : (fdiv_int 128 128 * 128 == (128 : Int)) = true := by decide
  cfg_simp [run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, MaxImplementedSVL, run_readReg hs, Align_int,
    h1, h2, SupportedPowerTwoSVL]
  rw [forIn_loop_step]
  rw [forIn_loop_step]
  cfg_simp [run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw]
  rfl

theorem run_CurrentSVL_read {s : SState} (hc : LinuxEL0Config s) (hfc : FPConfig s) :
    (CurrentSVL_read ()).run s = .ok 128 s := by
  obtain ⟨p, hp, hpe, hpn, hps⟩ := hc.pstate
  have h0 : (Sail.BitVec.extractLsb (0#64) 3 0).toNat = 0 := by decide
  unfold CurrentSVL_read
  cfg_simp [run_readReg hp, hpe, run_IsInHost hc, run_EL2Enabled hc, run_readReg hfc.smcr1, run_readReg hfc.smcr2,
    run_readReg hfc.smcr3, run_ImplSME_128 hfc.smevl, run_undefined_int, _get_SMCR_EL1_Type_LEN, _get_SMCR_EL2_Type_LEN,
    _get_SMCR_EL3_Type_LEN, EL0, EL1, EL2, EL3, HaveEL, h0]

theorem run_CurrentNSVL_read {s : SState} (hc : LinuxEL0Config s) (hfc : FPConfig s) :
    (CurrentNSVL_read ()).run s = .ok 512 s := by
  obtain ⟨p, hp, hpe, hpn, hps⟩ := hc.pstate
  have h3 : (Sail.BitVec.extractLsb (0x3#64) 3 0).toNat = 3 := by decide
  have h15 : (Sail.BitVec.extractLsb (0xf#64) 3 0).toNat = 15 := by decide
  have hm : ((min (3 : Int) 15 + 1) * 128) = 512 := by decide
  unfold CurrentNSVL_read
  cfg_simp [run_readReg hp, hpe, run_IsInHost hc, run_EL2Enabled hc, run_readReg hfc.zcr1, run_readReg hfc.zcr2,
    run_readReg hfc.zcr3, run_undefined_int, _get_ZCR_EL1_Type_LEN, _get_ZCR_EL2_Type_LEN,
    _get_ZCR_EL3_Type_LEN, EL0, EL1, EL2, EL3, HaveEL, h3, h15, hm, run_ImplSVE_512]

theorem run_CurrentVL_read {s : SState} (hc : LinuxEL0Config s) (hfc : FPConfig s) :
    (CurrentVL_read ()).run s = .ok 512 s := by
  obtain ⟨p, hp, hpe, hpn, hps⟩ := hc.pstate
  obtain ⟨p', hp', hsm⟩ := hfc.sm
  rw [hp] at hp'; cases hp'
  unfold CurrentVL_read
  cfg_simp [run_CurrentSVL_read hc hfc, run_CurrentNSVL_read hc hfc, HaveSME, run_IsFeatureImplemented hc, run_readReg hp, hsm]

theorem run_IsOriginalSVEEnabled0 {s : SState} (hc : LinuxEL0Config s) (hfc : FPConfig s) :
    (IsOriginalSVEEnabled 0#2).run s = .ok true s := by
  unfold IsOriginalSVEEnabled
  rw [run_SailME_run]
  have e1 : Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (0x3330000#64) 17 16) 0 0 = 1#1 := by decide
  have e2 : Sail.BitVec.extractLsb (0x3330000#64) 17 16 = 3#2 := by decide
  have e3 : Sail.BitVec.extractLsb (0x22ff#64) 8 8 = 0#1 := by decide
  have e4 : Sail.BitVec.extractLsb (0x1100#64) 8 8 = 1#1 := by decide
  have e5 : Sail.BitVec.extractLsb (0x30080000000#64) 34 34 = 0#1 := by decide
  cfg_simp [EL0, EL1, EL2, EL3, run_undefined_bool, run_ELUsingAArch32 hc, run_IsInHost hc, run_readReg hfc.cpacr1,
    run_EL2Enabled hc, HaveVirtHostExt, run_IsFeatureImplemented hc, run_readReg hc.hcr2, run_readReg hfc.cptr2,
    run_readReg hfc.cptr3, run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, _get_CPACR_EL1_Type_ZEN,
    _get_HCR_EL2_Type_E2H, _get_CPTR_EL2_Type_TZ, _get_CPTR_EL3_Type_EZ, e1, e2, e3, e4, e5]

theorem run_IsSVEEnabled0 {s : SState} (hc : LinuxEL0Config s) (hfc : FPConfig s) :
    (IsSVEEnabled 0#2).run s = .ok true s := by
  obtain ⟨p, hp, hpe, hpn, hps⟩ := hc.pstate
  obtain ⟨p', hp', hsm⟩ := hfc.sm
  rw [hp] at hp'; cases hp'
  unfold IsSVEEnabled
  cfg_simp [HaveSME, run_IsFeatureImplemented hc, run_readReg hp, hsm, HaveSVE, run_IsOriginalSVEEnabled0 hc hfc]

theorem vec_get_set {α : Type} [Inhabited α] (v : Vector α 32) (n i : Nat) (hn : n < 32) (hi : i < 32) (a : α) :
    (Sail.vectorUpdate v n a)[i]! = if i = n then a else v[i]! := by
  unfold Sail.vectorUpdate
  simp [Vector.set!, getElem!_def, hn, hi, Array.getElem_setIfInBounds]
  by_cases h : i = n
  · simp [h]
  · simp [h, Ne.symm h]

theorem upd_low128 (x : BitVec 2048) (v : BitVec 128) :
    (Sail.BitVec.updateSubrange x 511 0 (Sail.BitVec.zeroExtend v 512)).toNat % 2 ^ 128 = v.toNat := by
  have h : (Sail.BitVec.updateSubrange x 511 0 (Sail.BitVec.zeroExtend v 512)).setWidth 128 = v := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, Sail.BitVec.zeroExtend, BitVec.getLsbD_allOnes]
    have h1 : j < 2048 := by omega
    have h2 : j < 512 := by omega
    simp [hj, h1, h2]
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth] at this
  exact this

theorem run_V_set128 {s : SState} (hc : LinuxEL0Config s) (hfc : FPConfig s) (n : Nat) (hn : n < 32) (value : BitVec 128)
    {z0 : Vector (BitVec 2048) 32} (hz : s.regs.get? ._Z = some z0) :
    ∃ z', (V_set (n : Int) 128 value).run s = .ok () (s.set ._Z z') ∧
      ∀ i < 32, (z'[i]!).toNat % 2 ^ 128 = if i = n then value.toNat else (z0[i]!).toNat % 2 ^ 128 := by
  obtain ⟨p, hp, hpe, hpn, hps⟩ := hc.pstate
  obtain ⟨p', hp', hsm⟩ := hfc.sm
  rw [hp] at hp'; cases hp'
  have hn31 : decide ((n : Int) ≤ 31) = true := by simp; omega
  unfold V_set
  refine ⟨Sail.vectorUpdate z0 n (Sail.BitVec.updateSubrange (z0[(n : Int)]!) 511 0 (Sail.BitVec.zeroExtend value 512)), ?_, ?_⟩
  · cfg_simp [hn31, run_CurrentVL_read hc hfc, run_readReg hp, hpe, run_IsSVEEnabled0 hc hfc, EL0, EL1, EL2, EL3,
      ConstrainUnpredictableBool, __UNKNOWN_boolean, run_undefined_bool, run_readReg hz]
  · intro i hi
    rw [vec_get_set z0 n i hn hi]
    by_cases h : i = n
    · subst h; simp only [if_true]; exact upd_low128 _ _
    · simp [h]

end JanusASL.Proofs
