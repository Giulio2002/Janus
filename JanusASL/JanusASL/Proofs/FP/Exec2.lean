import JanusASL.Proofs.FP.Sqrt
import JanusASL.Proofs.FP.Div
import JanusASL.Proofs.FP.Exec
import JanusASL.Proofs.FP.Unpack2

/-! # Scalar FMUL, FDIV, FMADD/FMSUB/FNMADD/FNMSUB and FSQRT: execute functions against Janus -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_FPNegN {N : Nat} (hN : N = 32 ∨ N = 64) {js : Janus.Arm64.State} {s : SState} (hc : LinuxEL0Config s)
    (hf : FPRel js s) (op : BitVec N) :
    (FPNeg op).run s = .ok (BitVec.ofNat N (Janus.Arm64.FP.fpNeg (fmtN N) js.fpcr.toNat op.toNat)) s := by
  rcases hN with rfl | rfl
  · exact run_FPNeg32 hc hf.fpcr hf.fpcrRes0 op
  · exact run_FPNeg64 hc hf.fpcr hf.fpcrRes0 op

theorem ofNat_toNat' {N x : Nat} (h : x < 2 ^ N) : (BitVec.ofNat N x).toNat = x := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem lt_getV (js : Janus.Arm64.State) (n N : Nat) (hN : 0 < N) : js.getV n N < 2 ^ N := by
  unfold Janus.Arm64.State.getV; exact Nat.mod_lt _ (Nat.two_pow_pos N)

theorem fpNeg_lt (N : Nat) (hN : N = 32 ∨ N = 64) (fpcr op : Nat) (h : op < 2 ^ N) :
    Janus.Arm64.FP.fpNeg (fmtN N) fpcr op < 2 ^ N := by
  unfold Janus.Arm64.FP.fpNeg Janus.Float.flipSign
  have hs : (fmtN N).signBit * 2 = 2 ^ N := by
    rcases hN with rfl | rfl <;> decide
  have h1 : op % (fmtN N).signBit < (fmtN N).signBit := Nat.mod_lt _ (by rcases hN with rfl | rfl <;> decide)
  split
  · exact h
  · split <;> omega

theorem processDenorm_lt (fpcr : Nat) (t : Janus.Arm64.FP.FPType) :
    ExcLt (Janus.Arm64.FP.processDenorm fpcr t) := by
  rcases processDenorm_cases fpcr t with h | h <;> rw [h]
  · exact ExcLt.raise (by decide)
  · exact ExcLt.empty

theorem fpDiv_lt (f : Janus.Float.Fmt) (fpcr a b : Nat) : ExcLt (Janus.Arm64.FP.fpDiv f fpcr a b).2 := by
  unfold Janus.Arm64.FP.fpDiv
  dsimp only
  exc_lt

theorem fpSqrt_lt (f : Janus.Float.Fmt) (fpcr a : Nat) : ExcLt (Janus.Arm64.FP.fpSqrt f fpcr a).2 := by
  unfold Janus.Arm64.FP.fpSqrt
  dsimp only
  exc_lt
  all_goals exact processDenorm_lt _ _


/-- The scalar execute tail with Janus' commit: the result of `opm` is `o.1` and its exceptions are `o.2`. -/
theorem run_exec_generic {N : Nat} (hN : N = 32 ∨ N = 64) {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s)
    (hf : FPRel js s) (hc : LinuxEL0Config s) (hfc : FPConfig s) {rd src : Nat} (hrd : rd < 32) (hsrc : src < 32)
    (o : Nat × Janus.Arm64.FP.Exc) (hlt : ExcLt o.2)
    (hj : Janus.Arm64.fpCommit js o.2 (js.setScalar rd N (js.mergeBase src) o.1) = .ok js1)
    (opm : SailM (BitVec N))
    (hop : ∀ v, NT (js.fpcr.setWidth 64).toNat o.2 → opm.run (s.set .FPSR v) =
      .ok (BitVec.ofNat N o.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (o.2.proc ||| o.2.direct)))) :
    ∃ s', (scalarTail src rd (js.fpcr.setWidth 64) opm).run s = .ok () s' ∧ Rel js1 s' ∧ FPRel js1 s' ∧
      (∀ r, r ≠ ._Z → r ≠ .FPSR → s'.regs.get? r = s.regs.get? r) ∧ SMZero s' := by
  obtain ⟨hnt, hj1⟩ := fpCommit_ok hj
  have hop' := hop (js.fpsr.setWidth 64) (fpcr_bit_of_nt hnt)
  rw [set_fpsr_self hf] at hop'
  exact run_scalarTail hN h hf hc hfc hrd hsrc o hlt (by rw [hj1]; rfl) opm hop'

theorem run_exec_fmul {N ftype : Nat} (hft : (ftype = 0 ∧ N = 32) ∨ (ftype = 1 ∧ N = 64))
    {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) {rm rn rd : Nat} (hm : rm < 32) (hn : rn < 32) (hd : rd < 32)
    (hj : Janus.Arm64.execFpDP2 js ftype rm 0 rn rd = .ok js1) :
    ∃ s', (execute_aarch64_instrs_float_arithmetic_mul_product rd N rm rn false).run s = .ok () s' ∧ Rel js1 s' ∧
      FPRel js1 s' ∧ (∀ r, r ≠ ._Z → r ≠ .FPSR → s'.regs.get? r = s.regs.get? r) ∧ SMZero s' := by
  obtain ⟨hfmt, hsz⟩ := ftype_fmt hft
  have hN : N = 32 ∨ N = 64 := by rcases hft with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have e : execute_aarch64_instrs_float_arithmetic_mul_product rd N rm rn false =
      (do CheckFPEnabled64 ()
          let a ← V_read (rn : Int) N
          let b ← V_read (rm : Int) N
          let fpcr ← FPCR_read ()
          scalarTail rn rd fpcr (FPMul a b fpcr)) := by
    simp only [execute_aarch64_instrs_float_arithmetic_mul_product, scalarTail]
    simp
  unfold Janus.Arm64.execFpDP2 at hj
  have hv1 := run_V_read hf hn (w := N) (by omega)
  have hv2 := run_V_read hf hm (w := N) (by omega)
  have hfcr := run_FPCR_read hf
  have hchk := run_CheckFPEnabled64 hc hfc
  simp (config := { decide := true }) only [hfmt, hsz, ite_true] at hj
  have hlt := fpMul_lt (fmtN N) js.fpcr.toNat (js.getV rn N) (js.getV rm N)
  obtain ⟨s', hs', p1, p2, p3, p4⟩ := run_exec_generic hN h hf hc hfc hd hn _ hlt hj
    (FPMul (BitVec.ofNat N (js.getV rn N)) (BitVec.ofNat N (js.getV rm N)) (js.fpcr.setWidth 64))
    (fun v hnt => by
      have := run_FPMul hN hc hfc.sm (BitVec.ofNat N (js.getV rn N)) (BitVec.ofNat N (js.getV rm N))
        (js.fpcr.setWidth 64) v (by rw [getV_ofNat, getV_ofNat, hfn_fpcr]; rw [hfn_fpcr] at hnt; exact hnt)
      rw [getV_ofNat, getV_ofNat, hfn_fpcr] at this; exact this)
  refine ⟨s', ?_, p1, p2, p3, p4⟩
  rw [e]
  simp only [run_bind, hchk, hv1, hv2, hfcr, hs']


theorem run_FPCR_read_set {js : Janus.Arm64.State} {s : SState} (hf : FPRel js s) (v : BitVec 64) :
    (FPCR_read ()).run (s.set .FPSR v) = .ok (js.fpcr.setWidth 64) (s.set .FPSR v) :=
  run_FPCR_read_of (by rw [get?_set_ne _ _ (by decide)]; exact hf.fpcr) hf.fpcrRes0

theorem run_V_read_set {js : Janus.Arm64.State} {s : SState} (h : FPRel js s) (v : BitVec 64) {n : Nat} (hn : n < 32)
    {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) :
    (V_read (n : Int) w).run (s.set .FPSR v) = .ok (BitVec.ofNat w (js.getV n w)) (s.set .FPSR v) := by
  obtain ⟨z, hz, hzv⟩ := h.z
  have hz2 : (s.set .FPSR v).regs.get? ._Z = some z := by rw [get?_set_ne _ _ (by decide)]; exact hz
  have hw' : (w == 8 || (w == 16 || (w == 32 || (w == 64 || w == 128)))) = true := by
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> rfl
  cfg_simp [V_read, run_readReg hz2, hw', show (0 : Int) ≤ n from Int.natCast_nonneg n, show (n : Int) ≤ 31 by omega]
  rw [vget_int]
  have hw1 : 1 ≤ w := by omega
  have hw128 : w ≤ 128 := by omega
  apply BitVec.eq_of_toNat_eq
  have hk : ((w : Int) - 1).toNat - 0 + 1 = w := by omega
  rw [BitVec.toNat_setWidth, extractLsb_toNat', hk, Janus.Arm64.State.getV, ← hzv n hn, BitVec.toNat_ofNat]
  have hd : 2 ^ w ∣ 2 ^ 128 := Nat.pow_dvd_pow 2 hw128
  rw [Nat.mod_mod_of_dvd _ hd, Nat.pow_zero, Nat.div_one, Nat.mod_mod]

theorem run_exec_fdiv {N ftype : Nat} (hft : (ftype = 0 ∧ N = 32) ∨ (ftype = 1 ∧ N = 64))
    {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) {rm rn rd : Nat} (hm : rm < 32) (hn : rn < 32) (hd : rd < 32)
    (hj : Janus.Arm64.execFpDP2 js ftype rm 1 rn rd = .ok js1) :
    ∃ s', (execute_aarch64_instrs_float_arithmetic_div rd N rm rn).run s = .ok () s' ∧ Rel js1 s' ∧
      FPRel js1 s' ∧ (∀ r, r ≠ ._Z → r ≠ .FPSR → s'.regs.get? r = s.regs.get? r) ∧ SMZero s' := by
  obtain ⟨hfmt, hsz⟩ := ftype_fmt hft
  have hN : N = 32 ∨ N = 64 := by rcases hft with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have e : execute_aarch64_instrs_float_arithmetic_div rd N rm rn =
      (do CheckFPEnabled64 ()
          let a ← V_read (rn : Int) N
          let b ← V_read (rm : Int) N
          let fpcr ← FPCR_read ()
          scalarTail rn rd fpcr (do let f ← FPCR_read (); FPDiv a b f)) := by
    simp only [execute_aarch64_instrs_float_arithmetic_div, scalarTail]
    simp
  unfold Janus.Arm64.execFpDP2 at hj
  have hv1 := run_V_read hf hn (w := N) (by omega)
  have hv2 := run_V_read hf hm (w := N) (by omega)
  have hfcr := run_FPCR_read hf
  have hchk := run_CheckFPEnabled64 hc hfc
  simp (config := { decide := true }) only [hfmt, hsz, ite_true, Nat.reduceEqDiff, if_false] at hj
  have hlt := fpDiv_lt (fmtN N) js.fpcr.toNat (js.getV rn N) (js.getV rm N)
  obtain ⟨s', hs', p1, p2, p3, p4⟩ := run_exec_generic hN h hf hc hfc hd hn _ hlt hj
    (do let f ← FPCR_read (); FPDiv (BitVec.ofNat N (js.getV rn N)) (BitVec.ofNat N (js.getV rm N)) f)
    (fun v hnt => by
      have := run_FPDiv hN hc hfc.sm (BitVec.ofNat N (js.getV rn N)) (BitVec.ofNat N (js.getV rm N))
        (js.fpcr.setWidth 64) v (by rw [getV_ofNat, getV_ofNat, hfn_fpcr]; rw [hfn_fpcr] at hnt; exact hnt)
      rw [getV_ofNat, getV_ofNat, hfn_fpcr] at this
      simp only [run_bind, run_FPCR_read_set hf, this])
  refine ⟨s', ?_, p1, p2, p3, p4⟩
  rw [e]
  simp only [run_bind, hchk, hv1, hv2, hfcr, hs']

theorem run_exec_fsqrt {N ftype : Nat} (hft : (ftype = 0 ∧ N = 32) ∨ (ftype = 1 ∧ N = 64))
    {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) {rn rd : Nat} (hn : rn < 32) (hd : rd < 32)
    (hj : Janus.Arm64.execFpDP1 js ftype 3 rn rd = .ok js1) :
    ∃ s', (execute_aarch64_instrs_float_arithmetic_unary rd N FPUnaryOp.FPUnaryOp_SQRT rn).run s = .ok () s' ∧
      Rel js1 s' ∧ FPRel js1 s' ∧ (∀ r, r ≠ ._Z → r ≠ .FPSR → s'.regs.get? r = s.regs.get? r) ∧ SMZero s' := by
  obtain ⟨hfmt, hsz⟩ := ftype_fmt hft
  have hN : N = 32 ∨ N = 64 := by rcases hft with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have e : execute_aarch64_instrs_float_arithmetic_unary rd N FPUnaryOp.FPUnaryOp_SQRT rn =
      (do CheckFPEnabled64 ()
          let fpcr ← FPCR_read ()
          scalarTail rd rd fpcr (do let a ← V_read (rn : Int) N; FPSqrt a fpcr)) := by
    have hb : (FPUnaryOp.FPUnaryOp_SQRT != FPUnaryOp.FPUnaryOp_MOV) = true := by decide
    have hz : (integer_subrange 0 127 0 : BitVec 128) = Zeros := by decide
    simp only [execute_aarch64_instrs_float_arithmetic_unary, scalarTail, hb, hz]
    simp [andM, toBool]
  unfold Janus.Arm64.execFpDP1 at hj
  have hv1 := run_V_read hf hn (w := N) (by omega)
  have hfcr := run_FPCR_read hf
  have hchk := run_CheckFPEnabled64 hc hfc
  simp (config := { decide := true }) only [hfmt, hsz, ite_true, if_false] at hj
  have hlt := fpSqrt_lt (fmtN N) js.fpcr.toNat (js.getV rn N)
  obtain ⟨s', hs', p1, p2, p3, p4⟩ := run_exec_generic hN h hf hc hfc hd hd _ hlt hj
    (do let a ← V_read (rn : Int) N; FPSqrt a (js.fpcr.setWidth 64))
    (fun v hnt => by
      have := run_FPSqrt hN hc hfc.sm (BitVec.ofNat N (js.getV rn N))
        (js.fpcr.setWidth 64) v (by rw [getV_ofNat, hfn_fpcr]; rw [hfn_fpcr] at hnt; exact hnt)
      rw [getV_ofNat, hfn_fpcr] at this
      simp only [run_bind, run_V_read_set hf v hn (w := N) (by omega), this])
  refine ⟨s', ?_, p1, p2, p3, p4⟩
  rw [e]
  simp only [run_bind, hchk, hfcr, hs']


theorem run_condNeg {N : Nat} (hN : N = 32 ∨ N = 64) {js : Janus.Arm64.State} {s : SState} (hc : LinuxEL0Config s)
    (hf : FPRel js s) (v : BitVec 64) (neg : Bool) (x : BitVec N) :
    (if neg = true then FPNeg x else pure x : SailM (BitVec N)).run (s.set .FPSR v) =
      .ok (BitVec.ofNat N (if neg then Janus.Arm64.FP.fpNeg (fmtN N) js.fpcr.toNat x.toNat else x.toNat)) (s.set .FPSR v) := by
  have hfp : (s.set .FPSR v).regs.get? .FPCR = some (js.fpcr.setWidth 64) := by
    rw [get?_set_ne _ _ (by decide)]; exact hf.fpcr
  cases neg
  · simp only [Bool.false_eq_true, ite_false, run_pure, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [ite_true]
    rcases hN with rfl | rfl
    · exact run_FPNeg32 (hc.set_FPSR v) hfp hf.fpcrRes0 x
    · exact run_FPNeg64 (hc.set_FPSR v) hfp hf.fpcrRes0 x

theorem run_exec_fmadd {N ftype : Nat} (hft : (ftype = 0 ∧ N = 32) ∨ (ftype = 1 ∧ N = 64)) (o1 o0 : Bool)
    {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) {rm ra rn rd : Nat} (hm : rm < 32) (ha : ra < 32) (hn : rn < 32) (hd : rd < 32)
    (hj : Janus.Arm64.execFpDP3 js ftype o1 rm o0 ra rn rd = .ok js1) :
    ∃ s', (execute_aarch64_instrs_float_arithmetic_mul_add_sub ra rd N rm rn (o0 != o1) o1).run s = .ok () s' ∧
      Rel js1 s' ∧ FPRel js1 s' ∧ (∀ r, r ≠ ._Z → r ≠ .FPSR → s'.regs.get? r = s.regs.get? r) ∧ SMZero s' := by
  obtain ⟨hfmt, hsz⟩ := ftype_fmt hft
  have hN : N = 32 ∨ N = 64 := by rcases hft with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have e : execute_aarch64_instrs_float_arithmetic_mul_add_sub ra rd N rm rn (o0 != o1) o1 =
      (do CheckFPEnabled64 ()
          let a ← V_read (ra : Int) N
          let n ← V_read (rn : Int) N
          let m ← V_read (rm : Int) N
          let fpcr ← FPCR_read ()
          scalarTail ra rd fpcr (do
            let a' ← (if o1 = true then FPNeg a else pure a)
            let n' ← (if (o0 != o1) = true then FPNeg n else pure n)
            FPMulAdd a' n' m fpcr)) := by
    simp only [execute_aarch64_instrs_float_arithmetic_mul_add_sub, scalarTail]
    simp
  unfold Janus.Arm64.execFpDP3 at hj
  have hv1 := run_V_read hf ha (w := N) (by omega)
  have hv2 := run_V_read hf hn (w := N) (by omega)
  have hv3 := run_V_read hf hm (w := N) (by omega)
  have hfcr := run_FPCR_read hf
  have hchk := run_CheckFPEnabled64 hc hfc
  simp only [hfmt, hsz] at hj
  have hlt := fpMulAdd_lt (fmtN N) js.fpcr.toNat
    (if o1 then Janus.Arm64.FP.fpNeg (fmtN N) js.fpcr.toNat (js.getV ra N) else js.getV ra N)
    (if (o0 != o1) = true then Janus.Arm64.FP.fpNeg (fmtN N) js.fpcr.toNat (js.getV rn N) else js.getV rn N)
    (js.getV rm N)
  obtain ⟨s', hs', p1, p2, p3, p4⟩ := run_exec_generic hN h hf hc hfc hd ha _ hlt hj
    (do
      let a' ← (if o1 = true then FPNeg (BitVec.ofNat N (js.getV ra N)) else pure (BitVec.ofNat N (js.getV ra N)))
      let n' ← (if (o0 != o1) = true then FPNeg (BitVec.ofNat N (js.getV rn N)) else pure (BitVec.ofNat N (js.getV rn N)))
      FPMulAdd a' n' (BitVec.ofNat N (js.getV rm N)) (js.fpcr.setWidth 64))
    (fun v hnt => by
      have hA : (if o1 then Janus.Arm64.FP.fpNeg (fmtN N) js.fpcr.toNat (js.getV ra N) else js.getV ra N) < 2 ^ N := by
        cases o1
        · simp only [Bool.false_eq_true, ite_false]; exact lt_getV js ra N (by omega)
        · simp only [ite_true]; exact fpNeg_lt N hN _ _ (lt_getV js ra N (by omega))
      have hB : (if (o0 != o1) = true then Janus.Arm64.FP.fpNeg (fmtN N) js.fpcr.toNat (js.getV rn N) else js.getV rn N) < 2 ^ N := by
        by_cases hb : (o0 != o1) = true
        · simp only [hb, ite_true]; exact fpNeg_lt N hN _ _ (lt_getV js rn N (by omega))
        · simp only [hb, ite_false]; exact lt_getV js rn N (by omega)
      have := run_FPMulAdd hN hc hfc.sm (BitVec.ofNat N (if o1 then Janus.Arm64.FP.fpNeg (fmtN N) js.fpcr.toNat (js.getV ra N) else js.getV ra N))
        (BitVec.ofNat N (if (o0 != o1) = true then Janus.Arm64.FP.fpNeg (fmtN N) js.fpcr.toNat (js.getV rn N) else js.getV rn N))
        (BitVec.ofNat N (js.getV rm N)) (js.fpcr.setWidth 64) v (by
          rw [getV_ofNat, hfn_fpcr, ofNat_toNat' hA, ofNat_toNat' hB]
          rw [hfn_fpcr] at hnt; exact hnt)
      rw [ofNat_toNat' hA, ofNat_toNat' hB, getV_ofNat, hfn_fpcr] at this
      simp only [run_bind, run_condNeg hN hc hf v, getV_ofNat, this])
  refine ⟨s', ?_, p1, p2, p3, p4⟩
  rw [e]
  simp only [run_bind, hchk, hv1, hv2, hv3, hfcr, hs']

end JanusASL.Proofs
