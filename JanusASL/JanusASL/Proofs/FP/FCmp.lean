import JanusASL.Proofs.FP.Rel

/-! # FCMP / FCMPE: the execute function -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- A raised exception bit `k` that does not trap has its enable bit `FPCR<k+8>` clear. -/
theorem trap_bit {p f : Nat} (h : p &&& Janus.Arm64.FP.trapEnables f = 0) {k : Nat} (hk : k = 0 ∨ k = 7)
    (hp : Nat.testBit p k = true) : Nat.testBit f (k + 8) = false := by
  have h1 : Nat.testBit (p &&& Janus.Arm64.FP.trapEnables f) k = false := by rw [h]; simp
  rw [Nat.testBit_and, hp, Bool.true_and] at h1
  simp only [Janus.Arm64.FP.trapEnables, Nat.testBit_and] at h1
  rcases hk with rfl | rfl
  · have : Nat.testBit 0x9F 0 = true := by decide
    rw [this, Bool.and_true, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow] at h1
    simpa using h1
  · have : Nat.testBit 0x9F 7 = true := by decide
    rw [this, Bool.and_true, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow] at h1
    simpa using h1

theorem getLsbD_setWidth64 (x : BitVec 32) (i : Nat) : (x.setWidth 64).getLsbD i = Nat.testBit x.toNat i := by
  simp [BitVec.getLsbD_setWidth, BitVec.getLsbD]
  have : x.toNat < 18446744073709551616 := by have := x.isLt; omega
  rw [Nat.mod_eq_of_lt this]

theorem nzcv_bit3 (k : Nat) :
    (Sail.BitVec.extractLsb (BitVec.ofNat 4 k) 3 3 : BitVec 1) = BitVec.ofBool (k / 8 % 2 = 1) := by
  apply BitVec.eq_of_toNat_eq
  show (Sail.BitVec.extractLsb (BitVec.ofNat 4 k) 3 3).toNat = _
  rw [extractLsb_toNat', BitVec.toNat_ofNat]
  rcases (by omega : k / 8 % 2 = 0 ∨ k / 8 % 2 = 1) with h | h
  · rw [show k % 2 ^ 4 / 2 ^ 3 % 2 ^ (3 - 3 + 1) = 0 by omega, h]; decide
  · rw [show k % 2 ^ 4 / 2 ^ 3 % 2 ^ (3 - 3 + 1) = 1 by omega, h]; decide

theorem nzcv_bit2 (k : Nat) :
    (Sail.BitVec.extractLsb (BitVec.ofNat 4 k) 2 2 : BitVec 1) = BitVec.ofBool (k / 4 % 2 = 1) := by
  apply BitVec.eq_of_toNat_eq
  show (Sail.BitVec.extractLsb (BitVec.ofNat 4 k) 2 2).toNat = _
  rw [extractLsb_toNat', BitVec.toNat_ofNat]
  rcases (by omega : k / 4 % 2 = 0 ∨ k / 4 % 2 = 1) with h | h
  · rw [show k % 2 ^ 4 / 2 ^ 2 % 2 ^ (2 - 2 + 1) = 0 by omega, h]; decide
  · rw [show k % 2 ^ 4 / 2 ^ 2 % 2 ^ (2 - 2 + 1) = 1 by omega, h]; decide

theorem nzcv_bit1 (k : Nat) :
    (Sail.BitVec.extractLsb (BitVec.ofNat 4 k) 1 1 : BitVec 1) = BitVec.ofBool (k / 2 % 2 = 1) := by
  apply BitVec.eq_of_toNat_eq
  show (Sail.BitVec.extractLsb (BitVec.ofNat 4 k) 1 1).toNat = _
  rw [extractLsb_toNat', BitVec.toNat_ofNat]
  rcases (by omega : k / 2 % 2 = 0 ∨ k / 2 % 2 = 1) with h | h
  · rw [show k % 2 ^ 4 / 2 ^ 1 % 2 ^ (1 - 1 + 1) = 0 by omega, h]; decide
  · rw [show k % 2 ^ 4 / 2 ^ 1 % 2 ^ (1 - 1 + 1) = 1 by omega, h]; decide

theorem nzcv_bit0 (k : Nat) :
    (Sail.BitVec.extractLsb (BitVec.ofNat 4 k) 0 0 : BitVec 1) = BitVec.ofBool (k / 1 % 2 = 1) := by
  apply BitVec.eq_of_toNat_eq
  show (Sail.BitVec.extractLsb (BitVec.ofNat 4 k) 0 0).toNat = _
  rw [extractLsb_toNat', BitVec.toNat_ofNat]
  rcases (by omega : k / 1 % 2 = 0 ∨ k / 1 % 2 = 1) with h | h
  · rw [show k % 2 ^ 4 / 2 ^ 0 % 2 ^ (0 - 0 + 1) = 0 by omega, h]; decide
  · rw [show k % 2 ^ 4 / 2 ^ 0 % 2 ^ (0 - 0 + 1) = 1 by omega, h]; decide

theorem unpack_direct (f : Janus.Float.Fmt) (fpcr : Nat) (e : Bool) (x : Nat) :
    (Janus.Arm64.FP.unpack f fpcr e x).2.direct = 0 := by
  unfold Janus.Arm64.FP.unpack
  split <;> (try simp) <;>
  cases Janus.Arm64.FP.fz fpcr <;> cases Janus.Arm64.FP.ah fpcr <;> cases Janus.Arm64.FP.fiz fpcr <;> cases e <;>
    simp [Janus.Arm64.FP.raise]

theorem fpCompare_direct (f : Janus.Float.Fmt) (fpcr : Nat) (sig : Bool) (a b : Nat) :
    (Janus.Arm64.FP.fpCompare f fpcr sig a b).2.direct = 0 := by
  have h1 := unpack_direct f fpcr true a
  have h2 := unpack_direct f fpcr true b
  unfold Janus.Arm64.FP.fpCompare
  generalize Janus.Arm64.FP.unpack f fpcr true a = u1 at *
  generalize Janus.Arm64.FP.unpack f fpcr true b = u2 at *
  rcases u1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases u2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at h1 h2 ⊢
  split <;> simp [h1, h2, Janus.Arm64.FP.raise, Janus.Arm64.FP.processDenorms] <;> split <;> simp

theorem fpCompare_proc_lt (f : Janus.Float.Fmt) (fpcr : Nat) (sig : Bool) (a b : Nat) :
    (Janus.Arm64.FP.fpCompare f fpcr sig a b).2.proc < 256 := by
  have h1 := unpack_proc f fpcr true a
  have h2 := unpack_proc f fpcr true b
  unfold Janus.Arm64.FP.fpCompare
  generalize Janus.Arm64.FP.unpack f fpcr true a = u1 at *
  generalize Janus.Arm64.FP.unpack f fpcr true b = u2 at *
  rcases u1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases u2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at h1 h2 ⊢
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
  split <;> simp [h1, h2, Janus.Arm64.FP.raise, Janus.Arm64.FP.processDenorms, Janus.Arm64.FP.IOC,
    Janus.Arm64.FP.IDC] <;> (try split) <;> decide

theorem Rel.of_same {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hr : js'.regs = js.regs)
    (hs : js'.sp = js.sp) (hp : js'.pc = js.pc) (hf : js'.flags = js.flags) : Rel js' s where
  gpr i hi := by rw [hr]; exact h.gpr i hi
  sp := by rw [hs]; exact h.sp
  pc := by rw [hp]; exact h.pc
  pstate := by rw [hf]; exact h.pstate

/-- PSTATE with `NZCV` from the 4-bit value `k`. -/
def psNZCV (p : ProcState) (k : Nat) : ProcState := { p with N := BitVec.ofBool (k / 8 % 2 = 1), Z := BitVec.ofBool (k / 4 % 2 = 1), C := BitVec.ofBool (k / 2 % 2 = 1), V := BitVec.ofBool (k / 1 % 2 = 1) }

theorem psNZCV_eq (p : ProcState) (k : Nat) :
    psNZCV p k = { p with N := BitVec.ofBool (Janus.Arm64.flagsOfNzcv k).n, Z := BitVec.ofBool (Janus.Arm64.flagsOfNzcv k).z, C := BitVec.ofBool (Janus.Arm64.flagsOfNzcv k).c, V := BitVec.ofBool (Janus.Arm64.flagsOfNzcv k).v } := by
  simp [psNZCV, Janus.Arm64.flagsOfNzcv]

theorem run_FPZero (s : SState) (N : Nat) (hN : N = 32 ∨ N = 64) : (FPZero 0#1 N).run s = .ok 0#N s := by
  rcases hN with rfl | rfl <;> cfg_simp [FPZero] <;> rfl

set_option maxHeartbeats 4000000 in
theorem run_exec_fcmp32 {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s)
    (hc : LinuxEL0Config s) (hfc : FPConfig s) {rm opc rn : Nat} (hm : rm < 32) (hn : rn < 32)
    (hj : Janus.Arm64.execFpCmp js 0 rm opc rn = .ok js1) :
    ∃ s', (execute_aarch64_instrs_float_compare_uncond (decide (opc % 2 = 1)) 32 rm rn (decide (opc / 2 % 2 = 1))).run s =
        .ok () s' ∧ Rel js1 s' ∧ FPRel js1 s' ∧
      (∀ r, r ≠ .PSTATE → r ≠ .FPSR → s'.regs.get? r = s.regs.get? r) := by
  obtain ⟨p, hp, hpp⟩ := h.pstate
  unfold Janus.Arm64.execFpCmp Janus.Arm64.fpCommit at hj
  simp only [Janus.Arm64.ftypeFmt, Janus.Arm64.ftypeSize, ite_true] at hj
  generalize hop2 : (if opc % 2 = 1 then Janus.Float.zero Janus.Float.binary32 false else js.getV rm 32) = op2 at hj
  generalize ho : Janus.Arm64.FP.fpCompare Janus.Float.binary32 js.fpcr.toNat (decide (opc / 2 % 2 = 1))
    (js.getV rn 32) op2 = o at hj
  by_cases ht : o.2.proc &&& Janus.Arm64.FP.trapEnables js.fpcr.toNat ≠ 0
  · simp [ht] at hj
  · simp only [ht, if_false, Except.ok.injEq] at hj
    subst hj
    have ht' : o.2.proc &&& Janus.Arm64.FP.trapEnables js.fpcr.toNat = 0 := by simpa using ht
    have hv1 : (BitVec.ofNat 32 (js.getV rn 32)).toNat = js.getV rn 32 := by
      simp only [BitVec.toNat_ofNat, Janus.Arm64.State.getV, Nat.mod_mod]
    have hfn : (js.fpcr.setWidth 64).toNat = js.fpcr.toNat := by
      simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := js.fpcr.isLt; omega)
    unfold execute_aarch64_instrs_float_compare_uncond
    by_cases hz : opc % 2 = 1
    · simp only [hz, ite_true] at hop2
      subst hop2; subst ho
      have h0 : (0#32).toNat = Janus.Float.zero Janus.Float.binary32 false := by decide
      have hcmp := run_FPCompare32 hc (BitVec.ofNat 32 (js.getV rn 32)) 0#32 (decide (opc / 2 % 2 = 1))
        (js.fpcr.setWidth 64) hf.fpsr
        (fun hb => by rw [getLsbD_setWidth64]; exact trap_bit ht' (.inl rfl) (by rwa [hv1, hfn, h0] at hb))
        (fun hb => by rw [getLsbD_setWidth64]; exact trap_bit ht' (.inr rfl) (by rwa [hv1, hfn, h0] at hb))
      rw [hv1, hfn, h0] at hcmp
      generalize hr : Janus.Arm64.FP.fpCompare Janus.Float.binary32 js.fpcr.toNat (decide (opc / 2 % 2 = 1))
        (js.getV rn 32) (Janus.Float.zero Janus.Float.binary32 false) = r at hcmp ⊢
      have hrd : r.2.direct = 0 := hr ▸ fpCompare_direct _ _ _ _ _
      have hrp : r.2.proc < 256 := hr ▸ fpCompare_proc_lt _ _ _ _ _
      refine ⟨(s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 r.2.proc)).set .PSTATE (psNZCV p r.1),
        ?_, ?_, ?_, ?_⟩
      · have hpv : ∀ v, (s.set .FPSR v).regs.get? .PSTATE = some p := fun v => (get?_set_ne s v (by decide)).trans hp
        cfg_simp [run_CheckFPEnabled64 hc hfc, run_V_read hf hn (w := 32) (by decide), run_FPZero s 32 (.inl rfl),
          run_FPCR_read hf, hcmp, hz, fun v => run_readReg (hpv v), nzcv_bit3, nzcv_bit2, nzcv_bit1, nzcv_bit0,
          fun t (q : ProcState) => run_readReg (get?_set_self t .PSTATE q), set_set_PSTATE, psNZCV]
      · have h1 := (h.set_other .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 r.2.proc) rfl (by decide) (by decide)
          (by decide)).setFlags ((get?_set_ne s _ (by decide)).trans hp) (Janus.Arm64.flagsOfNzcv r.1)
        refine Rel.of_same (js := js.setFlags (Janus.Arm64.flagsOfNzcv r.1)) ?_ rfl rfl rfl rfl
        rw [psNZCV_eq]; exact h1
      · obtain ⟨z, hz0, hzv⟩ := hf.z
        refine { z := ⟨z, ?_, hzv⟩, fpcr := ?_, fpcrRes0 := hf.fpcrRes0, fpsr := ?_ }
        · rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; exact hz0
        · rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; exact hf.fpcr
        · rw [get?_set_ne _ _ (by decide), get?_set_FPSR, hrd, Nat.or_zero]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
          have h32 := js.fpsr.isLt
          rw [Nat.mod_eq_of_lt (show js.fpsr.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show r.2.proc < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show r.2.proc < 2 ^ 32 by omega)]
          have := Nat.or_lt_two_pow h32 (show r.2.proc < 2 ^ 32 by omega)
          rw [Nat.mod_eq_of_lt (show (js.fpsr.toNat ||| r.2.proc) < 2 ^ 64 by omega)]
      · intro x hx1 hx2
        rw [get?_set_ne _ _ (Ne.symm hx1), get?_set_ne _ _ (Ne.symm hx2)]
    · simp only [hz, ite_false] at hop2
      subst hop2; subst ho
      have h0 : (BitVec.ofNat 32 (js.getV rm 32)).toNat = js.getV rm 32 := by
        simp only [BitVec.toNat_ofNat, Janus.Arm64.State.getV, Nat.mod_mod]
      have hcmp := run_FPCompare32 hc (BitVec.ofNat 32 (js.getV rn 32)) (BitVec.ofNat 32 (js.getV rm 32)) (decide (opc / 2 % 2 = 1))
        (js.fpcr.setWidth 64) hf.fpsr
        (fun hb => by rw [getLsbD_setWidth64]; exact trap_bit ht' (.inl rfl) (by rwa [hv1, hfn, h0] at hb))
        (fun hb => by rw [getLsbD_setWidth64]; exact trap_bit ht' (.inr rfl) (by rwa [hv1, hfn, h0] at hb))
      rw [hv1, hfn, h0] at hcmp
      generalize hr : Janus.Arm64.FP.fpCompare Janus.Float.binary32 js.fpcr.toNat (decide (opc / 2 % 2 = 1))
        (js.getV rn 32) (js.getV rm 32) = r at hcmp ⊢
      have hrd : r.2.direct = 0 := hr ▸ fpCompare_direct _ _ _ _ _
      have hrp : r.2.proc < 256 := hr ▸ fpCompare_proc_lt _ _ _ _ _
      refine ⟨(s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 r.2.proc)).set .PSTATE (psNZCV p r.1),
        ?_, ?_, ?_, ?_⟩
      · have hpv : ∀ v, (s.set .FPSR v).regs.get? .PSTATE = some p := fun v => (get?_set_ne s v (by decide)).trans hp
        cfg_simp [run_CheckFPEnabled64 hc hfc, run_V_read hf hn (w := 32) (by decide), run_V_read hf hm (w := 32) (by decide),
          run_FPCR_read hf, hcmp, hz, fun v => run_readReg (hpv v), nzcv_bit3, nzcv_bit2, nzcv_bit1, nzcv_bit0,
          fun t (q : ProcState) => run_readReg (get?_set_self t .PSTATE q), set_set_PSTATE, psNZCV]
      · have h1 := (h.set_other .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 r.2.proc) rfl (by decide) (by decide)
          (by decide)).setFlags ((get?_set_ne s _ (by decide)).trans hp) (Janus.Arm64.flagsOfNzcv r.1)
        refine Rel.of_same (js := js.setFlags (Janus.Arm64.flagsOfNzcv r.1)) ?_ rfl rfl rfl rfl
        rw [psNZCV_eq]; exact h1
      · obtain ⟨z, hz0, hzv⟩ := hf.z
        refine { z := ⟨z, ?_, hzv⟩, fpcr := ?_, fpcrRes0 := hf.fpcrRes0, fpsr := ?_ }
        · rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; exact hz0
        · rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; exact hf.fpcr
        · rw [get?_set_ne _ _ (by decide), get?_set_FPSR, hrd, Nat.or_zero]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
          have h32 := js.fpsr.isLt
          rw [Nat.mod_eq_of_lt (show js.fpsr.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show r.2.proc < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show r.2.proc < 2 ^ 32 by omega)]
          have := Nat.or_lt_two_pow h32 (show r.2.proc < 2 ^ 32 by omega)
          rw [Nat.mod_eq_of_lt (show (js.fpsr.toNat ||| r.2.proc) < 2 ^ 64 by omega)]
      · intro x hx1 hx2
        rw [get?_set_ne _ _ (Ne.symm hx1), get?_set_ne _ _ (Ne.symm hx2)]


set_option maxHeartbeats 4000000 in
theorem run_exec_fcmp64 {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s)
    (hc : LinuxEL0Config s) (hfc : FPConfig s) {rm opc rn : Nat} (hm : rm < 32) (hn : rn < 32)
    (hj : Janus.Arm64.execFpCmp js 1 rm opc rn = .ok js1) :
    ∃ s', (execute_aarch64_instrs_float_compare_uncond (decide (opc % 2 = 1)) 64 rm rn (decide (opc / 2 % 2 = 1))).run s =
        .ok () s' ∧ Rel js1 s' ∧ FPRel js1 s' ∧
      (∀ r, r ≠ .PSTATE → r ≠ .FPSR → s'.regs.get? r = s.regs.get? r) := by
  obtain ⟨p, hp, hpp⟩ := h.pstate
  unfold Janus.Arm64.execFpCmp Janus.Arm64.fpCommit at hj
  simp only [Janus.Arm64.ftypeFmt, Janus.Arm64.ftypeSize, Nat.one_ne_zero, ite_false] at hj
  generalize hop2 : (if opc % 2 = 1 then Janus.Float.zero Janus.Float.binary64 false else js.getV rm 64) = op2 at hj
  generalize ho : Janus.Arm64.FP.fpCompare Janus.Float.binary64 js.fpcr.toNat (decide (opc / 2 % 2 = 1))
    (js.getV rn 64) op2 = o at hj
  by_cases ht : o.2.proc &&& Janus.Arm64.FP.trapEnables js.fpcr.toNat ≠ 0
  · simp [ht] at hj
  · simp only [ht, if_false, Except.ok.injEq] at hj
    subst hj
    have ht' : o.2.proc &&& Janus.Arm64.FP.trapEnables js.fpcr.toNat = 0 := by simpa using ht
    have hv1 : (BitVec.ofNat 64 (js.getV rn 64)).toNat = js.getV rn 64 := by
      simp only [BitVec.toNat_ofNat, Janus.Arm64.State.getV, Nat.mod_mod]
    have hfn : (js.fpcr.setWidth 64).toNat = js.fpcr.toNat := by
      simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := js.fpcr.isLt; omega)
    unfold execute_aarch64_instrs_float_compare_uncond
    by_cases hz : opc % 2 = 1
    · simp only [hz, ite_true] at hop2
      subst hop2; subst ho
      have h0 : (0#64).toNat = Janus.Float.zero Janus.Float.binary64 false := by decide
      have hcmp := run_FPCompare64 hc (BitVec.ofNat 64 (js.getV rn 64)) 0#64 (decide (opc / 2 % 2 = 1))
        (js.fpcr.setWidth 64) hf.fpsr
        (fun hb => by rw [getLsbD_setWidth64]; exact trap_bit ht' (.inl rfl) (by rwa [hv1, hfn, h0] at hb))
        (fun hb => by rw [getLsbD_setWidth64]; exact trap_bit ht' (.inr rfl) (by rwa [hv1, hfn, h0] at hb))
      rw [hv1, hfn, h0] at hcmp
      generalize hr : Janus.Arm64.FP.fpCompare Janus.Float.binary64 js.fpcr.toNat (decide (opc / 2 % 2 = 1))
        (js.getV rn 64) (Janus.Float.zero Janus.Float.binary64 false) = r at hcmp ⊢
      have hrd : r.2.direct = 0 := hr ▸ fpCompare_direct _ _ _ _ _
      have hrp : r.2.proc < 256 := hr ▸ fpCompare_proc_lt _ _ _ _ _
      refine ⟨(s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 r.2.proc)).set .PSTATE (psNZCV p r.1),
        ?_, ?_, ?_, ?_⟩
      · have hpv : ∀ v, (s.set .FPSR v).regs.get? .PSTATE = some p := fun v => (get?_set_ne s v (by decide)).trans hp
        cfg_simp [run_CheckFPEnabled64 hc hfc, run_V_read hf hn (w := 64) (by decide), run_FPZero s 64 (.inr rfl),
          run_FPCR_read hf, hcmp, hz, fun v => run_readReg (hpv v), nzcv_bit3, nzcv_bit2, nzcv_bit1, nzcv_bit0,
          fun t (q : ProcState) => run_readReg (get?_set_self t .PSTATE q), set_set_PSTATE, psNZCV]
      · have h1 := (h.set_other .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 r.2.proc) rfl (by decide) (by decide)
          (by decide)).setFlags ((get?_set_ne s _ (by decide)).trans hp) (Janus.Arm64.flagsOfNzcv r.1)
        refine Rel.of_same (js := js.setFlags (Janus.Arm64.flagsOfNzcv r.1)) ?_ rfl rfl rfl rfl
        rw [psNZCV_eq]; exact h1
      · obtain ⟨z, hz0, hzv⟩ := hf.z
        refine { z := ⟨z, ?_, hzv⟩, fpcr := ?_, fpcrRes0 := hf.fpcrRes0, fpsr := ?_ }
        · rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; exact hz0
        · rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; exact hf.fpcr
        · rw [get?_set_ne _ _ (by decide), get?_set_FPSR, hrd, Nat.or_zero]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
          have h32 := js.fpsr.isLt
          rw [Nat.mod_eq_of_lt (show js.fpsr.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show r.2.proc < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show r.2.proc < 2 ^ 32 by omega)]
          have := Nat.or_lt_two_pow h32 (show r.2.proc < 2 ^ 32 by omega)
          rw [Nat.mod_eq_of_lt (show (js.fpsr.toNat ||| r.2.proc) < 2 ^ 64 by omega)]
      · intro x hx1 hx2
        rw [get?_set_ne _ _ (Ne.symm hx1), get?_set_ne _ _ (Ne.symm hx2)]
    · simp only [hz, ite_false] at hop2
      subst hop2; subst ho
      have h0 : (BitVec.ofNat 64 (js.getV rm 64)).toNat = js.getV rm 64 := by
        simp only [BitVec.toNat_ofNat, Janus.Arm64.State.getV, Nat.mod_mod]
      have hcmp := run_FPCompare64 hc (BitVec.ofNat 64 (js.getV rn 64)) (BitVec.ofNat 64 (js.getV rm 64)) (decide (opc / 2 % 2 = 1))
        (js.fpcr.setWidth 64) hf.fpsr
        (fun hb => by rw [getLsbD_setWidth64]; exact trap_bit ht' (.inl rfl) (by rwa [hv1, hfn, h0] at hb))
        (fun hb => by rw [getLsbD_setWidth64]; exact trap_bit ht' (.inr rfl) (by rwa [hv1, hfn, h0] at hb))
      rw [hv1, hfn, h0] at hcmp
      generalize hr : Janus.Arm64.FP.fpCompare Janus.Float.binary64 js.fpcr.toNat (decide (opc / 2 % 2 = 1))
        (js.getV rn 64) (js.getV rm 64) = r at hcmp ⊢
      have hrd : r.2.direct = 0 := hr ▸ fpCompare_direct _ _ _ _ _
      have hrp : r.2.proc < 256 := hr ▸ fpCompare_proc_lt _ _ _ _ _
      refine ⟨(s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 r.2.proc)).set .PSTATE (psNZCV p r.1),
        ?_, ?_, ?_, ?_⟩
      · have hpv : ∀ v, (s.set .FPSR v).regs.get? .PSTATE = some p := fun v => (get?_set_ne s v (by decide)).trans hp
        cfg_simp [run_CheckFPEnabled64 hc hfc, run_V_read hf hn (w := 64) (by decide), run_V_read hf hm (w := 64) (by decide),
          run_FPCR_read hf, hcmp, hz, fun v => run_readReg (hpv v), nzcv_bit3, nzcv_bit2, nzcv_bit1, nzcv_bit0,
          fun t (q : ProcState) => run_readReg (get?_set_self t .PSTATE q), set_set_PSTATE, psNZCV]
      · have h1 := (h.set_other .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 r.2.proc) rfl (by decide) (by decide)
          (by decide)).setFlags ((get?_set_ne s _ (by decide)).trans hp) (Janus.Arm64.flagsOfNzcv r.1)
        refine Rel.of_same (js := js.setFlags (Janus.Arm64.flagsOfNzcv r.1)) ?_ rfl rfl rfl rfl
        rw [psNZCV_eq]; exact h1
      · obtain ⟨z, hz0, hzv⟩ := hf.z
        refine { z := ⟨z, ?_, hzv⟩, fpcr := ?_, fpcrRes0 := hf.fpcrRes0, fpsr := ?_ }
        · rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; exact hz0
        · rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; exact hf.fpcr
        · rw [get?_set_ne _ _ (by decide), get?_set_FPSR, hrd, Nat.or_zero]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
          have h32 := js.fpsr.isLt
          rw [Nat.mod_eq_of_lt (show js.fpsr.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show r.2.proc < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show r.2.proc < 2 ^ 32 by omega)]
          have := Nat.or_lt_two_pow h32 (show r.2.proc < 2 ^ 32 by omega)
          rw [Nat.mod_eq_of_lt (show (js.fpsr.toNat ||| r.2.proc) < 2 ^ 64 by omega)]
      · intro x hx1 hx2
        rw [get?_set_ne _ _ (Ne.symm hx1), get?_set_ne _ _ (Ne.symm hx2)]


end JanusASL.Proofs
