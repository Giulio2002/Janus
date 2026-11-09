import JanusASL.Proofs.Ops

/-! # ADD/ADDS/SUB/SUBS (immediate): ASL `execute` against Janus `execAddSubImm` -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem nzcv_n (f : Janus.Arm64.Flags) : Sail.BitVec.extractLsb (nzcvBits f) 3 3 = BitVec.ofBool f.n := by
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;> decide
theorem nzcv_z (f : Janus.Arm64.Flags) : Sail.BitVec.extractLsb (nzcvBits f) 2 2 = BitVec.ofBool f.z := by
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;> decide
theorem nzcv_c (f : Janus.Arm64.Flags) : Sail.BitVec.extractLsb (nzcvBits f) 1 1 = BitVec.ofBool f.c := by
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;> decide
theorem nzcv_v (f : Janus.Arm64.Flags) : Sail.BitVec.extractLsb (nzcvBits f) 0 0 = BitVec.ofBool f.v := by
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;> decide

theorem addSub_eq {N : Nat} (x y : BitVec N) (sub : Bool) :
    Janus.Arm64.addSub x y sub = Janus.Arm64.addWithCarry x (if sub then ~~~y else y) sub := by
  cases sub <;> rfl

set_option maxHeartbeats 4000000 in
theorem run_execute_addsub_imm {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d n : Nat} (hd : d < 32) (hn : n < 32) (imm : BitVec N) (S sub : Bool) :
    ∃ s', (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate d N imm n S sub).run s = .ok () s' ∧
      Rel (let res := Janus.Arm64.addSub (js.getXSP N n) imm sub
           if S then (js.setX d res.1).setFlags res.2 else js.setXSP d res.1) s' ∧ Frame s s' := by
  obtain ⟨p, hp, hps⟩ := h.pstate
  have hN0 : 0 < N := by omega
  by_cases hn31 : n = 31
  · subst hn31
    simp only [execute_aarch64_instrs_integer_arithmetic_add_sub_immediate, run_bind, beq_self_eq_true,
      run_undefined_bitvector, ite_true, run_pure, run_SP_read hp hps.sp h.sp]
    have hpair : (if sub = true then (1#1, ~~~imm) else (0#1, imm)) =
        (BitVec.ofBool sub, if sub then ~~~imm else imm) := by cases sub <;> rfl
    simp only [extract_setWidth hN, hpair, AddWithCarry_eq hN0, ← addSub_eq]
    have hx : js.getXSP N 31 = BitVec.setWidth N js.sp := by
      simp [Janus.Arm64.State.getXSP, Janus.Arm64.State.readSP]
    rw [hx]
    generalize Janus.Arm64.addSub (BitVec.setWidth N js.sp) imm sub = r
    cases S
    · simp only [Bool.false_eq_true, ite_false, run_pure, Bool.not_false, Bool.and_true]
      by_cases hd31 : d = 31
      · subst hd31
        simp only [beq_self_eq_true, ite_true, run_SP_set hp hps.sp]
        refine ⟨_, rfl, ?_, ?_⟩
        · simpa [Janus.Arm64.State.setXSP, Sail.BitVec.zeroExtend] using h.writeSP31 (r.1.setWidth 64)
        · intro x _ hx _; exact get?_set_ne s _ (Ne.symm hx)
      · have hd' : d < 31 := by omega
        have hdb : ((d : Nat) == 31) = false := by simp; omega
        simp only [hdb, Bool.false_eq_true, ite_false, run_X_set hd' hN]
        refine ⟨_, rfl, ?_, ?_⟩
        · have := h.writeZR hd' (Sail.BitVec.zeroExtend r.1 64)
          simpa [Janus.Arm64.State.setXSP, Janus.Arm64.State.writeSP, Janus.Arm64.State.writeZR, hd31,
            Sail.BitVec.zeroExtend] using this
        · intro x hx _ _; exact get?_setGpr s _ hd' x hx
    · simp only [ite_true, run_bind, run_readReg hp, run_writeReg, run_readReg (get?_set_PSTATE _ _),
        nzcv_n, nzcv_z, nzcv_c, nzcv_v, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false,
        SState.set_set]
      have hf := h.setFlags hp r.2
      have hfr : Frame s (s.set Register.PSTATE
          { p with N := BitVec.ofBool r.2.n, Z := BitVec.ofBool r.2.z, C := BitVec.ofBool r.2.c,
                   V := BitVec.ofBool r.2.v }) := by
        intro x _ _ hx; exact get?_set_ne s _ (Ne.symm hx)
      by_cases hd31 : d = 31
      · subst hd31
        refine ⟨_, run_X_set_zr _ hN _, ?_, hfr⟩
        simpa [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR] using hf
      · have hd' : d < 31 := by omega
        refine ⟨_, run_X_set hd' hN _, ?_, ?_⟩
        · have := hf.writeZR hd' (Sail.BitVec.zeroExtend r.1 64)
          have e : (js.setX d r.1).setFlags r.2 = (js.setFlags r.2).writeZR d (r.1.setWidth 64) := by
            simp [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR, Janus.Arm64.State.setFlags, hd31]
          rw [e]; simpa [Sail.BitVec.zeroExtend] using this
        · intro x hx h1 h2; rw [get?_setGpr _ _ hd' x hx]; exact hfr x hx h1 h2

  · have hn' : n < 31 := by omega
    have hnb : ((n : Nat) == 31) = false := by simp; omega
    simp only [execute_aarch64_instrs_integer_arithmetic_add_sub_immediate, run_bind, hnb,
      run_undefined_bitvector, Bool.false_eq_true, ite_false, run_pure,
      run_X_read hn' (h.gpr n hn') (Or.symm hN |>.elim Or.inr Or.inl)]
    have hpair : (if sub = true then (1#1, ~~~imm) else (0#1, imm)) =
        (BitVec.ofBool sub, if sub then ~~~imm else imm) := by cases sub <;> rfl
    simp only [extract_setWidth hN, hpair, AddWithCarry_eq hN0, ← addSub_eq]
    have hx : js.getXSP N n = BitVec.setWidth N (js.regs n) := by
      simp [Janus.Arm64.State.getXSP, Janus.Arm64.State.readSP, hn31]
    rw [hx]
    generalize Janus.Arm64.addSub (BitVec.setWidth N (js.regs n)) imm sub = r
    cases S
    · simp only [Bool.false_eq_true, ite_false, run_pure, Bool.not_false, Bool.and_true]
      by_cases hd31 : d = 31
      · subst hd31
        simp only [beq_self_eq_true, ite_true, run_SP_set hp hps.sp]
        refine ⟨_, rfl, ?_, ?_⟩
        · simpa [Janus.Arm64.State.setXSP, Sail.BitVec.zeroExtend] using h.writeSP31 (r.1.setWidth 64)
        · intro x _ hx _; exact get?_set_ne s _ (Ne.symm hx)
      · have hd' : d < 31 := by omega
        have hdb : ((d : Nat) == 31) = false := by simp; omega
        simp only [hdb, Bool.false_eq_true, ite_false, run_X_set hd' hN]
        refine ⟨_, rfl, ?_, ?_⟩
        · have := h.writeZR hd' (Sail.BitVec.zeroExtend r.1 64)
          simpa [Janus.Arm64.State.setXSP, Janus.Arm64.State.writeSP, Janus.Arm64.State.writeZR, hd31,
            Sail.BitVec.zeroExtend] using this
        · intro x hx _ _; exact get?_setGpr s _ hd' x hx
    · simp only [ite_true, run_bind, run_readReg hp, run_writeReg, run_readReg (get?_set_PSTATE _ _),
        nzcv_n, nzcv_z, nzcv_c, nzcv_v, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false,
        SState.set_set]
      have hf := h.setFlags hp r.2
      have hfr : Frame s (s.set Register.PSTATE
          { p with N := BitVec.ofBool r.2.n, Z := BitVec.ofBool r.2.z, C := BitVec.ofBool r.2.c,
                   V := BitVec.ofBool r.2.v }) := by
        intro x _ _ hx; exact get?_set_ne s _ (Ne.symm hx)
      by_cases hd31 : d = 31
      · subst hd31
        refine ⟨_, run_X_set_zr _ hN _, ?_, hfr⟩
        simpa [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR] using hf
      · have hd' : d < 31 := by omega
        refine ⟨_, run_X_set hd' hN _, ?_, ?_⟩
        · have := hf.writeZR hd' (Sail.BitVec.zeroExtend r.1 64)
          have e : (js.setX d r.1).setFlags r.2 = (js.setFlags r.2).writeZR d (r.1.setWidth 64) := by
            simp [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR, Janus.Arm64.State.setFlags, hd31]
          rw [e]; simpa [Sail.BitVec.zeroExtend] using this
        · intro x hx h1 h2; rw [get?_setGpr _ _ hd' x hx]; exact hfr x hx h1 h2

end JanusASL.Proofs
