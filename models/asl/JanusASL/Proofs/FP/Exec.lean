import JanusASL.Proofs.FP.VSet

/-! # Scalar floating-point execute functions: the shared parts

`IsMerging`, the merge base, `Elem_set` followed by `V_set`, and the FPSR/`FPRel` bookkeeping. -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem upd_elem0 {N : Nat} (x : BitVec 128) (r : BitVec N) :
    Sail.BitVec.updateSubrange' x 0 N r = BitVec.ofNat 128 (x.toNat / 2 ^ N * 2 ^ N + r.toNat) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Sail.BitVec.updateSubrange', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_ofNat]
  have hr : r.toNat < 2 ^ N := r.isLt
  have e : x.toNat / 2 ^ N * 2 ^ N + r.toNat = 2 ^ N * (x.toNat / 2 ^ N) + r.toNat := by rw [Nat.mul_comm]
  rw [e, Nat.testBit_two_pow_mul_add _ hr]
  by_cases hjN : j < N
  · have hj0 : ¬ j < 0 := by omega
    simp [hj, hjN, hj0]
    exact BitVec.getLsbD_eq_getElem hjN ▸ rfl
  · simp [hj, hjN, Nat.testBit_div_two_pow, BitVec.getLsbD_of_ge r j (by omega)]
    have : j - N + N = j := by omega
    rw [this]; exact BitVec.getLsbD_eq_getElem hj ▸ rfl

theorem get_NEP (v : BitVec 64) : _get_FPCRType_NEP v = BitVec.ofBool (v.toNat / 2 ^ 2 % 2 = 1) := by
  apply BitVec.eq_of_toNat_eq
  show (Sail.BitVec.extractLsb v 2 2).toNat = _
  rw [extractLsb_toNat']
  rcases (by omega : v.toNat / 2 ^ 2 % 2 = 0 ∨ v.toNat / 2 ^ 2 % 2 = 1) with h | h <;> rw [h] <;> decide

theorem ofBool_beq_one (b : Bool) : (BitVec.ofBool b == 1#1) = b := by cases b <;> rfl

theorem run_IsMerging {s : SState} (hc : LinuxEL0Config s) (hfc : FPConfig s) (fpcr : BitVec 64) :
    (IsMerging fpcr).run s = .ok (Janus.Arm64.FP.isMerging fpcr.toNat) s := by
  obtain ⟨p, hp, hsm⟩ := hfc.sm
  unfold IsMerging
  cfg_simp [HaveSME, run_IsFeatureImplemented hc, run_readReg hp, hsm, HaveAltFP, run_UsingAArch32 hc, get_NEP,
    Janus.Arm64.FP.isMerging, Janus.Arm64.FP.nep, Janus.Arm64.FP.fpcrBit, ofBool_eq_one, ofBool_beq_one]

theorem elem_set_val {N : Nat} (hN : N = 32 ∨ N = 64) (base : BitVec 128) (r : BitVec N) :
    Sail.BitVec.updateSubrange base ((((0 : Int) + 1) * (N : Int) - 1).toNat) (((0 : Int) * (N : Int)).toNat)
      (BitVec.setWidth ((((0 : Int) + 1) * (N : Int) - 1).toNat - ((0 : Int) * (N : Int)).toNat + 1) r) =
      BitVec.ofNat 128 (base.toNat / 2 ^ N * 2 ^ N + r.toNat) := by
  rcases hN with rfl | rfl
  · have := upd_elem0 base r
    simpa [Sail.BitVec.updateSubrange] using this
  · have := upd_elem0 base r
    simpa [Sail.BitVec.updateSubrange] using this

theorem run_elem_vset {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (hfc : FPConfig s)
    {d : Nat} (hd : d < 32) {z0 : Vector (BitVec 2048) 32} (hz : s.regs.get? ._Z = some z0) (base : BitVec 128)
    (r : BitVec N) :
    ∃ z', (do let res ← Elem_set base 0 N r; V_set (d : Int) 128 res : SailM Unit).run s = .ok () (s.set ._Z z') ∧
      ∀ i < 32, (z'[i]!).toNat % 2 ^ 128 = if i = d then base.toNat / 2 ^ N * 2 ^ N + r.toNat else (z0[i]!).toNat % 2 ^ 128 := by
  have hN128 : N ≤ 128 := by omega
  have hlt : base.toNat / 2 ^ N * 2 ^ N + r.toNat < 2 ^ 128 := by
    have h1 : base.toNat / 2 ^ N * 2 ^ N ≤ base.toNat := Nat.div_mul_le_self _ _
    have h2 : r.toNat < 2 ^ N := r.isLt
    have h3 : base.toNat < 2 ^ 128 := base.isLt
    have h128 : 2 ^ 128 = 2 ^ (128 - N) * 2 ^ N := by rw [← Nat.pow_add]; congr 1; omega
    have hq : base.toNat / 2 ^ N < 2 ^ (128 - N) :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos N)).mpr (by rw [← h128]; exact h3)
    calc base.toNat / 2 ^ N * 2 ^ N + r.toNat < base.toNat / 2 ^ N * 2 ^ N + 2 ^ N := by omega
      _ = (base.toNat / 2 ^ N + 1) * 2 ^ N := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 2 ^ (128 - N) * 2 ^ N := Nat.mul_le_mul_right _ hq
      _ = 2 ^ 128 := h128.symm
  obtain ⟨z', hrun, hz'⟩ := run_V_set128 hc hfc d hd (BitVec.ofNat 128 (base.toNat / 2 ^ N * 2 ^ N + r.toNat)) hz
  refine ⟨z', ?_, ?_⟩
  · unfold Elem_set
    have hs : (decide ((0 : Int) ≥ 0) && decide (((0 : Int) + 1) * (N : Int) ≤ (Sail.BitVec.length base : Int))) = true := by
      simp [Sail.BitVec.length]; omega
    simp only [run_bind, run_sail_assert_of hs, run_pure, elem_set_val hN, hrun]
  · intro i hi
    rw [hz' i hi]
    by_cases h : i = d
    · simp [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    · simp [h]

/-- The raised and direct bits of an operation fit in 8 bits. -/
def ExcLt (e : Janus.Arm64.FP.Exc) : Prop := e.proc < 256 ∧ e.direct < 256

theorem ExcLt.append {a b : Janus.Arm64.FP.Exc} (ha : ExcLt a) (hb : ExcLt b) : ExcLt (a ++ b) := by
  refine ⟨?_, ?_⟩ <;> simp only [exc_append_proc, exc_append_direct]
  · exact Nat.or_lt_two_pow (n := 8) ha.1 hb.1
  · exact Nat.or_lt_two_pow (n := 8) ha.2 hb.2

theorem ExcLt.empty : ExcLt ({ } : Janus.Arm64.FP.Exc) := ⟨by decide, by decide⟩
theorem ExcLt.raise {e : Nat} (h : e < 256) : ExcLt (Janus.Arm64.FP.raise e) := ⟨h, by show 0 < 256; decide⟩

theorem fpsr_or_cast (x : BitVec 32) (e : Nat) (he : e < 2 ^ 32) :
    (x ||| BitVec.ofNat 32 e).setWidth 64 = x.setWidth 64 ||| BitVec.ofNat 64 e := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_ofNat]
  have h1 := x.isLt
  have h3 := Nat.or_lt_two_pow h1 he
  rw [Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt (show (x.toNat ||| e) < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show e < 2 ^ 64 by omega)]

theorem run_elem_vset_lt {N : Nat} (hN : N = 32 ∨ N = 64) (base : BitVec 128) (r : BitVec N) :
    base.toNat / 2 ^ N * 2 ^ N + r.toNat < 2 ^ 128 := by
  have hN128 : N ≤ 128 := by omega
  have h2 : r.toNat < 2 ^ N := r.isLt
  have h3 : base.toNat < 2 ^ 128 := base.isLt
  have h128 : 2 ^ 128 = 2 ^ (128 - N) * 2 ^ N := by rw [← Nat.pow_add]; congr 1; omega
  have hq : base.toNat / 2 ^ N < 2 ^ (128 - N) :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos N)).mpr (by rw [← h128]; exact h3)
  calc base.toNat / 2 ^ N * 2 ^ N + r.toNat < base.toNat / 2 ^ N * 2 ^ N + 2 ^ N := by omega
    _ = (base.toNat / 2 ^ N + 1) * 2 ^ N := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ 2 ^ (128 - N) * 2 ^ N := Nat.mul_le_mul_right _ hq
    _ = 2 ^ 128 := h128.symm

theorem Rel.of_same_fp {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hr : js'.regs = js.regs)
    (hs : js'.sp = js.sp) (hp : js'.pc = js.pc) (hf : js'.flags = js.flags) : Rel js' s where
  gpr i hi := by rw [hr]; exact h.gpr i hi
  sp := by rw [hs]; exact h.sp
  pc := by rw [hp]; exact h.pc
  pstate := by rw [hf]; exact h.pstate

theorem scalar_post {N : Nat} {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s)
    (hfc : FPConfig s) {rd : Nat} (hrd : rd < 32) (B : Nat) (hB : B < 2 ^ 128) (r : BitVec N) (e : Nat)
    (he : e < 2 ^ 32)
    (hj1 : js1 = { js.setV rd 128 (B / 2 ^ N * 2 ^ N + r.toNat) with fpsr := js.fpsr ||| BitVec.ofNat 32 e })
    {z0 : Vector (BitVec 2048) 32} (hz : s.regs.get? ._Z = some z0) {z' : Vector (BitVec 2048) 32}
    (hz' : ∀ i < 32, (z'[i]!).toNat % 2 ^ 128 = if i = rd then B / 2 ^ N * 2 ^ N + r.toNat else (z0[i]!).toNat % 2 ^ 128)
    (hlt : B / 2 ^ N * 2 ^ N + r.toNat < 2 ^ 128) :
    Rel js1 ((s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 e)).set ._Z z') ∧
    FPRel js1 ((s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 e)).set ._Z z') ∧
    (∀ x, x ≠ ._Z → x ≠ .FPSR → ((s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 e)).set ._Z z').regs.get? x =
      s.regs.get? x) ∧
    SMZero ((s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 e)).set ._Z z') := by
  have hframe : ∀ x, x ≠ ._Z → x ≠ .FPSR → ((s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 e)).set ._Z z').regs.get? x =
      s.regs.get? x := fun x h1 h2 => by
    rw [get?_set_ne _ _ (Ne.symm h1), get?_set_ne _ _ (Ne.symm h2)]
  refine ⟨?_, ?_, hframe, ?_⟩
  · have h1 := (h.set_other .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 e) rfl (by decide) (by decide) (by decide)).set_other
      ._Z z' rfl (by decide) (by decide) (by decide)
    subst hj1
    exact h1.of_same_fp rfl rfl rfl rfl
  · subst hj1
    obtain ⟨z, hz1, hzv⟩ := hf.z
    rw [hz] at hz1; cases hz1
    refine { z := ⟨z', get?_set_self _ _ _, ?_⟩, fpcr := ?_, fpcrRes0 := hf.fpcrRes0, fpsr := ?_ }
    · intro i hi
      rw [hz' i hi]
      simp only [Janus.Arm64.State.setV]
      by_cases hir : i = rd
      · subst hir; simp only [if_true, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
      · simp only [hir, if_false]; exact hzv i hi
    · rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; exact hf.fpcr
    · rw [get?_set_ne _ _ (by decide), get?_set_FPSR]
      show _ = some ((js.fpsr ||| BitVec.ofNat 32 e).setWidth 64)
      rw [fpsr_or_cast js.fpsr e he]
  · obtain ⟨p, hp, hs⟩ := hfc.sm
    exact ⟨p, by rw [hframe _ (by decide) (by decide)]; exact hp, hs⟩

theorem ftype_fmt {N ftype : Nat} (hft : (ftype = 0 ∧ N = 32) ∨ (ftype = 1 ∧ N = 64)) :
    Janus.Arm64.ftypeFmt ftype = fmtN N ∧ Janus.Arm64.ftypeSize ftype = N := by
  rcases hft with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Janus.Arm64.ftypeFmt, Janus.Arm64.ftypeSize, fmtN]

theorem fpCommit_ok {js : Janus.Arm64.State} {e : Janus.Arm64.FP.Exc} {t js1 : Janus.Arm64.State}
    (h : Janus.Arm64.fpCommit js e t = .ok js1) :
    e.proc &&& Janus.Arm64.FP.trapEnables js.fpcr.toNat = 0 ∧
      js1 = { t with fpsr := t.fpsr ||| BitVec.ofNat 32 (e.proc ||| e.direct) } := by
  unfold Janus.Arm64.fpCommit at h
  by_cases ht : e.proc &&& Janus.Arm64.FP.trapEnables js.fpcr.toNat ≠ 0
  · simp [ht] at h
  · simp only [ht, if_false, Except.ok.injEq] at h
    exact ⟨by simpa using ht, h.symm⟩

theorem FPConfig.set_FPSR {s : SState} (h : FPConfig s) (v : BitVec 64) : FPConfig (s.set .FPSR v) :=
  h.of_eq fun r hr => get?_set_ne _ _ (fun e => by subst e; revert hr; decide)

/-- The common tail of the scalar floating-point execute functions: merge base, the operation, `Elem_set`, `V_set`. -/
def scalarTail {N : Nat} (src rd : Nat) (fpcr : BitVec 64) (opm : SailM (BitVec N)) : SailM Unit := do
  let merge ← IsMerging fpcr
  let result ← (if merge then V_read (src : Int) 128 else pure (Zeros (n := 128)))
  let result ← (do let r ← opm; Elem_set result 0 N r)
  V_set (rd : Int) 128 result

theorem run_scalarTail {N : Nat} (hN : N = 32 ∨ N = 64) {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s)
    (hf : FPRel js s) (hc : LinuxEL0Config s) (hfc : FPConfig s) {rd src : Nat} (hrd : rd < 32) (hsrc : src < 32)
    (o : Nat × Janus.Arm64.FP.Exc) (hlt : ExcLt o.2)
    (hj1 : js1 = { js.setScalar rd N (js.mergeBase src) o.1 with fpsr := js.fpsr ||| BitVec.ofNat 32 (o.2.proc ||| o.2.direct) })
    (opm : SailM (BitVec N))
    (hop : opm.run s = .ok (BitVec.ofNat N o.1)
      (s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 (o.2.proc ||| o.2.direct)))) :
    ∃ s', (scalarTail src rd (js.fpcr.setWidth 64) opm).run s = .ok () s' ∧ Rel js1 s' ∧ FPRel js1 s' ∧
      (∀ r, r ≠ ._Z → r ≠ .FPSR → s'.regs.get? r = s.regs.get? r) ∧ SMZero s' := by
  obtain ⟨z0, hz, hzv⟩ := hf.z
  have hfn : (js.fpcr.setWidth 64).toNat = js.fpcr.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := js.fpcr.isLt; omega)
  have he : o.2.proc ||| o.2.direct < 2 ^ 32 := by
    have := Nat.or_lt_two_pow (n := 8) hlt.1 hlt.2; omega
  have hB : js.mergeBase src < 2 ^ 128 := by
    unfold Janus.Arm64.State.mergeBase
    split
    · unfold Janus.Arm64.State.getV; exact Nat.mod_lt _ (by decide)
    · exact Nat.two_pow_pos 128
  have hbase : (if Janus.Arm64.FP.isMerging js.fpcr.toNat = true then BitVec.ofNat 128 (js.getV src 128) else 0#128) =
      BitVec.ofNat 128 (js.mergeBase src) := by
    unfold Janus.Arm64.State.mergeBase; split <;> simp
  unfold scalarTail
  simp only [run_bind, run_IsMerging hc hfc, hfn]
  have hv : (V_read (src : Int) 128).run s = .ok (BitVec.ofNat 128 (js.getV src 128)) s := run_V_read hf hsrc (by decide)
  have hz1 : (s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 (o.2.proc ||| o.2.direct))).regs.get? ._Z = some z0 := by
    rw [get?_set_ne _ _ (by decide)]; exact hz
  obtain ⟨z', hrun, hz'⟩ := run_elem_vset hN (hc.set_FPSR _) (hfc.set_FPSR _) hrd hz1
    (BitVec.ofNat 128 (js.mergeBase src)) (BitVec.ofNat N o.1)
  have hBt : (BitVec.ofNat 128 (js.mergeBase src)).toNat = js.mergeBase src := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hB
  rw [hBt] at hz'
  have hmerge : (if Janus.Arm64.FP.isMerging js.fpcr.toNat = true then V_read (src : Int) 128 else pure (Zeros (n := 128)) :
      SailM (BitVec 128)).run s = .ok (BitVec.ofNat 128 (js.mergeBase src)) s := by
    by_cases hm : Janus.Arm64.FP.isMerging js.fpcr.toNat = true
    · simp only [hm, ite_true, hv]
      unfold Janus.Arm64.State.mergeBase; simp only [hm, ite_true]
    · simp only [hm, ite_false, run_pure]
      unfold Janus.Arm64.State.mergeBase; simp only [hm, ite_false]; rfl
  have hrun' := hrun
  simp only [run_bind] at hrun'
  have hr : (BitVec.ofNat N o.1).toNat = o.1 % 2 ^ N := by rw [BitVec.toNat_ofNat]
  have hlt2 : js.mergeBase src / 2 ^ N * 2 ^ N + (BitVec.ofNat N o.1).toNat < 2 ^ 128 := by
    have := run_elem_vset_lt hN (BitVec.ofNat 128 (js.mergeBase src)) (BitVec.ofNat N o.1)
    rwa [hBt] at this
  have hj1' : js1 = { js.setV rd 128 (js.mergeBase src / 2 ^ N * 2 ^ N + (BitVec.ofNat N o.1).toNat) with
      fpsr := js.fpsr ||| BitVec.ofNat 32 (o.2.proc ||| o.2.direct) } := by
    rw [hj1, hr]; rfl
  obtain ⟨p1, p2, p3, p4⟩ := scalar_post h hf hfc hrd (js.mergeBase src) hB (BitVec.ofNat N o.1)
    (o.2.proc ||| o.2.direct) he hj1' hz hz' hlt2
  refine ⟨_, ?_, p1, p2, p3, p4⟩
  simp only [hmerge, hop, hrun']

theorem unpack_lt (f : Janus.Float.Fmt) (fpcr : Nat) (e : Bool) (x : Nat) :
    ExcLt (Janus.Arm64.FP.unpack f fpcr e x).2 := by
  refine ⟨?_, by rw [unpack_direct']; decide⟩
  rcases unpack_proc f fpcr e x with h | h <;> rw [h] <;> decide

theorem processNaN_lt (f : Janus.Float.Fmt) (fpcr : Nat) (t : Janus.Arm64.FP.FPType) (op : Nat) :
    ExcLt (Janus.Arm64.FP.processNaN f fpcr t op).2 := by
  unfold Janus.Arm64.FP.processNaN
  dsimp only
  split
  · exact ExcLt.raise (by decide)
  · exact ExcLt.empty

theorem processDenorms_lt (fpcr : Nat) (t1 t2 : Janus.Arm64.FP.FPType) :
    ExcLt (Janus.Arm64.FP.processDenorms fpcr t1 t2) := by
  rcases processDenorms_cases fpcr t1 t2 with h | h <;> rw [h]
  · exact ExcLt.raise (by decide)
  · exact ExcLt.empty

macro "exc_lt0" : tactic => `(tactic| repeat' (first
  | exact ExcLt.empty
  | exact ExcLt.raise (by decide)
  | apply ExcLt.append
  | (dsimp only; done)
  | (dsimp only; refine ⟨?_, ?_⟩ <;> decide)
  | split))

theorem fpRound_lt (f : Janus.Float.Fmt) (fpcr : Nat) (rm : Janus.Float.RM) (neg : Bool) (m : Nat) (e : Int) :
    ExcLt (Janus.Arm64.FP.fpRound f fpcr rm neg m e).2 := by
  unfold Janus.Arm64.FP.fpRound
  dsimp only
  exc_lt0

theorem processDenorms3_lt (fpcr : Nat) (t1 t2 t3 : Janus.Arm64.FP.FPType) :
    ExcLt (Janus.Arm64.FP.processDenorms3 fpcr t1 t2 t3) := by
  rcases processDenorms3_cases fpcr t1 t2 t3 with h | h <;> rw [h]
  · exact ExcLt.raise (by decide)
  · exact ExcLt.empty

theorem exc_snd_of {f : Janus.Float.Fmt} {fpcr : Nat} {t : Janus.Arm64.FP.FPType} {op r : Nat} {e : Janus.Arm64.FP.Exc}
    (h : Janus.Arm64.FP.processNaN f fpcr t op = (r, e)) : ExcLt e := by
  have := congrArg Prod.snd h
  simp only at this
  rw [← this]; exact processNaN_lt _ _ _ _

theorem processNaNs_lt (f : Janus.Float.Fmt) (fpcr : Nat) (t1 t2 : Janus.Arm64.FP.FPType) (a b r : Nat)
    (e : Janus.Arm64.FP.Exc) (h : Janus.Arm64.FP.processNaNs f fpcr t1 t2 a b = some (r, e)) : ExcLt e := by
  unfold Janus.Arm64.FP.processNaNs at h
  cases hc : (Janus.Arm64.FP.ah fpcr && t1.isNaN && t2.isNaN) <;>
    simp only [hc, Bool.false_eq_true, ite_false, ite_true] at h <;>
    repeat' split at h
  all_goals first
    | contradiction
    | (simp only [Option.some.injEq] at h; exact exc_snd_of h)

theorem processNaNs3_lt (f : Janus.Float.Fmt) (fpcr : Nat) (t1 t2 t3 : Janus.Arm64.FP.FPType) (a b c r : Nat)
    (e : Janus.Arm64.FP.Exc) (h : Janus.Arm64.FP.processNaNs3 f fpcr t1 t2 t3 a b c = some (r, e)) : ExcLt e := by
  unfold Janus.Arm64.FP.processNaNs3 at h
  simp only [] at h
  cases hc1 : (Janus.Arm64.FP.ah fpcr && t1.isNaN && t2.isNaN && t3.isNaN) <;>
  cases hc2 : (Janus.Arm64.FP.ah fpcr && t2.isNaN && (t1.isNaN || t3.isNaN)) <;>
  cases hc3 : (Janus.Arm64.FP.ah fpcr && t3.isNaN && t1.isNaN) <;>
    simp only [hc1, hc2, hc3, Bool.false_eq_true, ite_false, ite_true] at h <;>
    repeat' split at h
  all_goals first
    | contradiction
    | (simp only [Option.some.injEq] at h; exact exc_snd_of h)

macro "exc_lt" : tactic => `(tactic| repeat' (first
  | exact ExcLt.empty
  | exact ExcLt.raise (by decide)
  | apply ExcLt.append
  | exact unpack_lt _ _ _ _
  | exact processNaN_lt _ _ _ _
  | exact processDenorms_lt _ _ _
  | exact processDenorms3_lt _ _ _ _
  | exact fpRound_lt _ _ _ _ _ _
  | exact processNaNs_lt _ _ _ _ _ _ _ _ (by assumption)
  | exact processNaNs3_lt _ _ _ _ _ _ _ _ _ _ (by assumption)
  | (dsimp only; done)
  | (dsimp only; refine ⟨?_, ?_⟩ <;> decide)
  | split))

theorem fpAdd_lt (f : Janus.Float.Fmt) (fpcr a b : Nat) : ExcLt (Janus.Arm64.FP.fpAdd f fpcr a b).2 := by
  unfold Janus.Arm64.FP.fpAdd
  dsimp only
  exc_lt

theorem fpSub_lt (f : Janus.Float.Fmt) (fpcr a b : Nat) : ExcLt (Janus.Arm64.FP.fpSub f fpcr a b).2 := by
  unfold Janus.Arm64.FP.fpSub
  dsimp only
  exc_lt

theorem fpMul_lt (f : Janus.Float.Fmt) (fpcr a b : Nat) : ExcLt (Janus.Arm64.FP.fpMul f fpcr a b).2 := by
  unfold Janus.Arm64.FP.fpMul
  dsimp only
  exc_lt

theorem fpMulAdd_lt (f : Janus.Float.Fmt) (fpcr a b c : Nat) : ExcLt (Janus.Arm64.FP.fpMulAdd f fpcr a b c).2 := by
  unfold Janus.Arm64.FP.fpMulAdd
  dsimp only
  exc_lt

theorem hfn_fpcr (js : Janus.Arm64.State) : (js.fpcr.setWidth 64).toNat = js.fpcr.toNat := by
  simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := js.fpcr.isLt; omega)

theorem getV_ofNat (js : Janus.Arm64.State) (n N : Nat) : (BitVec.ofNat N (js.getV n N)).toNat = js.getV n N := by
  simp only [BitVec.toNat_ofNat, Janus.Arm64.State.getV, Nat.mod_mod]

theorem fpcr_bit_of_nt {js : Janus.Arm64.State} {e : Janus.Arm64.FP.Exc}
    (h : e.proc &&& Janus.Arm64.FP.trapEnables js.fpcr.toNat = 0) : NT (js.fpcr.setWidth 64).toNat e := by
  unfold NT; rw [hfn_fpcr]; exact h

/-- The ASL result of `op` run at `s` with FPSR from `FPRel`, as the lemmas `run_FPAdd` ... give it. -/
theorem set_fpsr_self {js : Janus.Arm64.State} {s : SState} (hf : FPRel js s) :
    s.set .FPSR (js.fpsr.setWidth 64) = s := SState.set_same s .FPSR _ hf.fpsr

theorem run_exec_addsub {N ftype : Nat} (hft : (ftype = 0 ∧ N = 32) ∨ (ftype = 1 ∧ N = 64)) (sub : Bool)
    {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) {rm rn rd : Nat} (hm : rm < 32) (hn : rn < 32) (hd : rd < 32)
    (hj : Janus.Arm64.execFpDP2 js ftype rm (if sub then 3 else 2) rn rd = .ok js1) :
    ∃ s', (execute_aarch64_instrs_float_arithmetic_add_sub rd N rm rn sub).run s = .ok () s' ∧ Rel js1 s' ∧
      FPRel js1 s' ∧ (∀ r, r ≠ ._Z → r ≠ .FPSR → s'.regs.get? r = s.regs.get? r) ∧ SMZero s' := by
  obtain ⟨hfmt, hsz⟩ := ftype_fmt hft
  have hN : N = 32 ∨ N = 64 := by rcases hft with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have e : execute_aarch64_instrs_float_arithmetic_add_sub rd N rm rn sub =
      (do CheckFPEnabled64 ()
          let a ← V_read (rn : Int) N
          let b ← V_read (rm : Int) N
          let fpcr ← FPCR_read ()
          scalarTail rn rd fpcr (if sub then FPSub a b fpcr else FPAdd a b fpcr)) := by
    cases sub <;> rfl
  unfold Janus.Arm64.execFpDP2 at hj
  have hv1 := run_V_read hf hn (w := N) (by omega)
  have hv2 := run_V_read hf hm (w := N) (by omega)
  have hfa := set_fpsr_self hf
  have hfcr := run_FPCR_read hf
  have hchk := run_CheckFPEnabled64 hc hfc
  cases sub
  · simp (config := { decide := true }) only [hfmt, hsz, Bool.false_eq_true, if_false, ite_true] at hj
    obtain ⟨hnt, hj1⟩ := fpCommit_ok hj
    have hlt := fpAdd_lt (fmtN N) js.fpcr.toNat (js.getV rn N) (js.getV rm N)
    have hop := run_FPAdd hN hc hfc.sm (BitVec.ofNat N (js.getV rn N)) (BitVec.ofNat N (js.getV rm N))
      (js.fpcr.setWidth 64) (js.fpsr.setWidth 64) (by rw [getV_ofNat, getV_ofNat, hfn_fpcr]; exact hnt)
    rw [getV_ofNat, getV_ofNat, hfn_fpcr, hfa] at hop
    generalize hO : Janus.Arm64.FP.fpAdd (fmtN N) js.fpcr.toNat (js.getV rn N) (js.getV rm N) = o at hop hlt hnt hj1
    obtain ⟨s', hs', p1, p2, p3, p4⟩ := run_scalarTail hN (js1 := js1) h hf hc hfc hd hn o hlt (by rw [hj1]; rfl)
      (FPAdd (BitVec.ofNat N (js.getV rn N)) (BitVec.ofNat N (js.getV rm N)) (js.fpcr.setWidth 64)) hop
    refine ⟨s', ?_, p1, p2, p3, p4⟩
    rw [e]
    simp only [run_bind, hchk, hv1, hv2, hfcr, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, hs']
  · simp (config := { decide := true }) only [hfmt, hsz, if_true, ite_true] at hj
    obtain ⟨hnt, hj1⟩ := fpCommit_ok hj
    have hlt := fpSub_lt (fmtN N) js.fpcr.toNat (js.getV rn N) (js.getV rm N)
    have hop := run_FPSub hN hc hfc.sm (BitVec.ofNat N (js.getV rn N)) (BitVec.ofNat N (js.getV rm N))
      (js.fpcr.setWidth 64) (js.fpsr.setWidth 64) (by rw [getV_ofNat, getV_ofNat, hfn_fpcr]; exact hnt)
    rw [getV_ofNat, getV_ofNat, hfn_fpcr, hfa] at hop
    generalize hO : Janus.Arm64.FP.fpSub (fmtN N) js.fpcr.toNat (js.getV rn N) (js.getV rm N) = o at hop hlt hnt hj1
    obtain ⟨s', hs', p1, p2, p3, p4⟩ := run_scalarTail hN (js1 := js1) h hf hc hfc hd hn o hlt (by rw [hj1]; rfl)
      (FPSub (BitVec.ofNat N (js.getV rn N)) (BitVec.ofNat N (js.getV rm N)) (js.fpcr.setWidth 64)) hop
    refine ⟨s', ?_, p1, p2, p3, p4⟩
    rw [e]
    simp only [run_bind, hchk, hv1, hv2, hfcr, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, hs']

end JanusASL.Proofs
