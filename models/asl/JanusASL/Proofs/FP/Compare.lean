import JanusASL.Proofs.FP.Unpack

/-! # `FPCompare` against Janus' `FP.fpCompare` -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem ofNat_or (w a b : Nat) : BitVec.ofNat w (a ||| b) = BitVec.ofNat w a ||| BitVec.ofNat w b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem LinuxEL0Config.set_FPSR {s : SState} (h : LinuxEL0Config s) (v : BitVec 64) :
    LinuxEL0Config (s.set .FPSR v) :=
  h.of_eq fun r hr => get?_set_ne _ _ (fun e => by subst e; revert hr; decide)

@[simp] theorem exc_append_proc (a b : Janus.Arm64.FP.Exc) : (a ++ b).proc = a.proc ||| b.proc := rfl
@[simp] theorem exc_append_direct (a b : Janus.Arm64.FP.Exc) : (a ++ b).direct = a.direct ||| b.direct := rfl

theorem eq_real_val (v w : Janus.Float.Val) (hv : Bnd v) (hw : Bnd w) :
    eq_real (valRat v) (valRat w) = Janus.Float.Val.eq v w := by
  rw [val_eq v w hv hw]; simp only [eq_real]
  by_cases h : valRat v = valRat w <;> simp [h]

theorem lt_real_val (v w : Janus.Float.Val) (hv : Bnd v) (hw : Bnd w) :
    lt_real (valRat v) (valRat w) = Janus.Float.Val.lt v w := by
  rw [val_lt v w hv hw]; rfl

theorem fpCompare_proc_bit (f : Janus.Float.Fmt) (fpcr : Nat) (sig : Bool) (a b k : Nat)
    (h : Nat.testBit (Janus.Arm64.FP.unpack f fpcr true a).2.proc k = true ∨
      Nat.testBit (Janus.Arm64.FP.unpack f fpcr true b).2.proc k = true) :
    Nat.testBit (Janus.Arm64.FP.fpCompare f fpcr sig a b).2.proc k = true := by
  unfold Janus.Arm64.FP.fpCompare
  generalize Janus.Arm64.FP.unpack f fpcr true a = u1 at *
  generalize Janus.Arm64.FP.unpack f fpcr true b = u2 at *
  rcases u1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases u2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at h ⊢
  split <;> simp [Nat.testBit_or] <;> rcases h with h | h <;> simp [h]

theorem unpack_bit7 (f : Janus.Float.Fmt) (fpcr : Nat) (x : Nat) (h : (Janus.Arm64.FP.unpack f fpcr true x).2.proc ≠ 0) :
    Nat.testBit (Janus.Arm64.FP.unpack f fpcr true x).2.proc 7 = true := by
  rcases unpack_proc f fpcr true x with h' | h' <;> simp_all <;> decide

set_option maxHeartbeats 8000000 in
theorem run_FPCompare32 {s : SState} (hc : LinuxEL0Config s) (op1 op2 : BitVec 32) (sig : Bool)
    (fpcr : BitVec 64) {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs)
    (hIO : Nat.testBit (Janus.Arm64.FP.fpCompare Janus.Float.binary32 fpcr.toNat sig op1.toNat op2.toNat).2.proc 0 = true →
      fpcr.getLsbD 8 = false)
    (hID : Nat.testBit (Janus.Arm64.FP.fpCompare Janus.Float.binary32 fpcr.toNat sig op1.toNat op2.toNat).2.proc 7 = true →
      fpcr.getLsbD 15 = false) :
    (FPCompare op1 op2 sig fpcr).run s =
      let r := Janus.Arm64.FP.fpCompare Janus.Float.binary32 fpcr.toNat sig op1.toNat op2.toNat
      .ok (BitVec.ofNat 4 r.1) (s.set .FPSR (xs ||| BitVec.ofNat 64 r.2.proc)) := by
  have hb1 := bnd_unpack _ (.inl rfl) fpcr.toNat true op1.toNat
  have hb2 := bnd_unpack _ (.inl rfl) fpcr.toNat true op2.toNat
  have hp1 := unpack_proc Janus.Float.binary32 fpcr.toNat true op1.toNat
  have hp2 := unpack_proc Janus.Float.binary32 fpcr.toNat true op2.toNat
  have hu1 : (Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat true op1.toNat).2.proc ≠ 0 →
      fpcr.getLsbD 15 = false := fun h => hID (fpCompare_proc_bit _ _ _ _ _ _ (.inl (unpack_bit7 _ _ _ h)))
  have hu2 : (Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat true op2.toNat).2.proc ≠ 0 →
      fpcr.getLsbD 15 = false := fun h => hID (fpCompare_proc_bit _ _ _ _ _ _ (.inr (unpack_bit7 _ _ _ h)))
  unfold FPCompare
  cfg_simp [undefined_FPType, undefined_real, run_internal_pick, Sail.BitVec.length,
    run_FPUnpack32' hc op1 fpcr hx hu1]
  rw [run_FPUnpack32' (hc.set_FPSR _) op2 fpcr (get?_set_FPSR _ _) hu2]
  dsimp only
  unfold Janus.Arm64.FP.fpCompare at hIO hID ⊢
  generalize Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat true op1.toNat = u1 at *
  generalize Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat true op2.toNat = u2 at *
  rcases u1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases u2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at hb1 hb2 hp1 hp2 hIO hID ⊢
  have hc2 : LinuxEL0Config ((s.set .FPSR (xs ||| BitVec.ofNat 64 x1.proc)).set .FPSR
      (xs ||| BitVec.ofNat 64 x1.proc ||| BitVec.ofNat 64 x2.proc)) := (hc.set_FPSR _).set_FPSR _
  rw [eq_real_val v1 v2 hb1 hb2, lt_real_val v1 v2 hb1 hb2, set_set_FPSR]
  by_cases hb8 : fpcr.getLsbD 8 = false <;> by_cases hb15 : fpcr.getLsbD 15 = false
  · have hE8 := fun v => run_FPProcessException (hc.set_FPSR v) .FPExc_InvalidOp fpcr hb8 (get?_set_FPSR s v)
    have hE15 := fun v => run_FPProcessException (hc.set_FPSR v) .FPExc_InputDenorm fpcr hb15 (get?_set_FPSR s v)
    by_cases hah : fpcr.toNat / 2 ^ 1 % 2 = 1 <;> cases sig <;> cases t1 <;> cases t2 <;>
    cfg_simp [hE8, hE15, aslFPType, run_map, Nat.testBit_or, FPProcessDenorms, HaveAltFP,
      fun v f => run_IsFeatureImplemented (hc.set_FPSR v) f, fun v => run_UsingAArch32 (hc.set_FPSR v),
      get_AH, ofBool_eq_one, hah,
      Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms, Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC,
      Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, fpExcBit, update_one_or, ofNat_or,
      BitVec.or_assoc] <;>
    first | (cases v1.eq v2 <;> cases v1.lt v2 <;> rfl)
  · have hE8 := fun v => run_FPProcessException (hc.set_FPSR v) .FPExc_InvalidOp fpcr hb8 (get?_set_FPSR s v)
    have hID' : Nat.testBit _ 7 = false := Bool.eq_false_iff.mpr fun h => hb15 (hID h)
    by_cases hah : fpcr.toNat / 2 ^ 1 % 2 = 1 <;> cases sig <;> cases t1 <;> cases t2 <;>
    try simp (config := { decide := true }) [Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms,
      Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC, Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah,
      Nat.testBit_or]
      at hID' <;>
    cfg_simp [hE8, aslFPType, run_map, Nat.testBit_or, FPProcessDenorms, HaveAltFP,
      fun v f => run_IsFeatureImplemented (hc.set_FPSR v) f, fun v => run_UsingAArch32 (hc.set_FPSR v),
      get_AH, ofBool_eq_one, hah,
      Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms, Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC,
      Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, fpExcBit, update_one_or, ofNat_or,
      BitVec.or_assoc] <;>
    first | (cases v1.eq v2 <;> cases v1.lt v2 <;> rfl)
  · have hE15 := fun v => run_FPProcessException (hc.set_FPSR v) .FPExc_InputDenorm fpcr hb15 (get?_set_FPSR s v)
    have hIO' : Nat.testBit _ 0 = false := Bool.eq_false_iff.mpr fun h => hb8 (hIO h)
    by_cases hah : fpcr.toNat / 2 ^ 1 % 2 = 1 <;> cases sig <;> cases t1 <;> cases t2 <;>
    try simp (config := { decide := true }) [Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms,
      Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC, Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah,
      Nat.testBit_or]
      at hIO' <;>
    cfg_simp [hE15, aslFPType, run_map, Nat.testBit_or, FPProcessDenorms, HaveAltFP,
      fun v f => run_IsFeatureImplemented (hc.set_FPSR v) f, fun v => run_UsingAArch32 (hc.set_FPSR v),
      get_AH, ofBool_eq_one, hah,
      Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms, Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC,
      Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, fpExcBit, update_one_or, ofNat_or,
      BitVec.or_assoc] <;>
    first | (cases v1.eq v2 <;> cases v1.lt v2 <;> rfl)
  · have hIO' : Nat.testBit _ 0 = false := Bool.eq_false_iff.mpr fun h => hb8 (hIO h)
    have hID' : Nat.testBit _ 7 = false := Bool.eq_false_iff.mpr fun h => hb15 (hID h)
    by_cases hah : fpcr.toNat / 2 ^ 1 % 2 = 1 <;> cases sig <;> cases t1 <;> cases t2 <;>
    try simp (config := { decide := true }) [Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms,
      Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC, Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah,
      Nat.testBit_or]
      at hIO' hID' <;>
    cfg_simp [aslFPType, run_map, Nat.testBit_or, FPProcessDenorms, HaveAltFP,
      fun v f => run_IsFeatureImplemented (hc.set_FPSR v) f, fun v => run_UsingAArch32 (hc.set_FPSR v),
      get_AH, ofBool_eq_one, hah,
      Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms, Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC,
      Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, fpExcBit, update_one_or, ofNat_or,
      BitVec.or_assoc] <;>
    first | (cases v1.eq v2 <;> cases v1.lt v2 <;> rfl)

set_option maxHeartbeats 8000000 in
theorem run_FPCompare64 {s : SState} (hc : LinuxEL0Config s) (op1 op2 : BitVec 64) (sig : Bool)
    (fpcr : BitVec 64) {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs)
    (hIO : Nat.testBit (Janus.Arm64.FP.fpCompare Janus.Float.binary64 fpcr.toNat sig op1.toNat op2.toNat).2.proc 0 = true →
      fpcr.getLsbD 8 = false)
    (hID : Nat.testBit (Janus.Arm64.FP.fpCompare Janus.Float.binary64 fpcr.toNat sig op1.toNat op2.toNat).2.proc 7 = true →
      fpcr.getLsbD 15 = false) :
    (FPCompare op1 op2 sig fpcr).run s =
      let r := Janus.Arm64.FP.fpCompare Janus.Float.binary64 fpcr.toNat sig op1.toNat op2.toNat
      .ok (BitVec.ofNat 4 r.1) (s.set .FPSR (xs ||| BitVec.ofNat 64 r.2.proc)) := by
  have hb1 := bnd_unpack _ (.inr rfl) fpcr.toNat true op1.toNat
  have hb2 := bnd_unpack _ (.inr rfl) fpcr.toNat true op2.toNat
  have hp1 := unpack_proc Janus.Float.binary64 fpcr.toNat true op1.toNat
  have hp2 := unpack_proc Janus.Float.binary64 fpcr.toNat true op2.toNat
  have hu1 : (Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat true op1.toNat).2.proc ≠ 0 →
      fpcr.getLsbD 15 = false := fun h => hID (fpCompare_proc_bit _ _ _ _ _ _ (.inl (unpack_bit7 _ _ _ h)))
  have hu2 : (Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat true op2.toNat).2.proc ≠ 0 →
      fpcr.getLsbD 15 = false := fun h => hID (fpCompare_proc_bit _ _ _ _ _ _ (.inr (unpack_bit7 _ _ _ h)))
  unfold FPCompare
  cfg_simp [undefined_FPType, undefined_real, run_internal_pick, Sail.BitVec.length,
    run_FPUnpack64' hc op1 fpcr hx hu1]
  rw [run_FPUnpack64' (hc.set_FPSR _) op2 fpcr (get?_set_FPSR _ _) hu2]
  dsimp only
  unfold Janus.Arm64.FP.fpCompare at hIO hID ⊢
  generalize Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat true op1.toNat = u1 at *
  generalize Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat true op2.toNat = u2 at *
  rcases u1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases u2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at hb1 hb2 hp1 hp2 hIO hID ⊢
  have hc2 : LinuxEL0Config ((s.set .FPSR (xs ||| BitVec.ofNat 64 x1.proc)).set .FPSR
      (xs ||| BitVec.ofNat 64 x1.proc ||| BitVec.ofNat 64 x2.proc)) := (hc.set_FPSR _).set_FPSR _
  rw [eq_real_val v1 v2 hb1 hb2, lt_real_val v1 v2 hb1 hb2, set_set_FPSR]
  by_cases hb8 : fpcr.getLsbD 8 = false <;> by_cases hb15 : fpcr.getLsbD 15 = false
  · have hE8 := fun v => run_FPProcessException (hc.set_FPSR v) .FPExc_InvalidOp fpcr hb8 (get?_set_FPSR s v)
    have hE15 := fun v => run_FPProcessException (hc.set_FPSR v) .FPExc_InputDenorm fpcr hb15 (get?_set_FPSR s v)
    by_cases hah : fpcr.toNat / 2 ^ 1 % 2 = 1 <;> cases sig <;> cases t1 <;> cases t2 <;>
    cfg_simp [hE8, hE15, aslFPType, run_map, Nat.testBit_or, FPProcessDenorms, HaveAltFP,
      fun v f => run_IsFeatureImplemented (hc.set_FPSR v) f, fun v => run_UsingAArch32 (hc.set_FPSR v),
      get_AH, ofBool_eq_one, hah,
      Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms, Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC,
      Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, fpExcBit, update_one_or, ofNat_or,
      BitVec.or_assoc] <;>
    first | (cases v1.eq v2 <;> cases v1.lt v2 <;> rfl)
  · have hE8 := fun v => run_FPProcessException (hc.set_FPSR v) .FPExc_InvalidOp fpcr hb8 (get?_set_FPSR s v)
    have hID' : Nat.testBit _ 7 = false := Bool.eq_false_iff.mpr fun h => hb15 (hID h)
    by_cases hah : fpcr.toNat / 2 ^ 1 % 2 = 1 <;> cases sig <;> cases t1 <;> cases t2 <;>
    try simp (config := { decide := true }) [Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms,
      Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC, Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah,
      Nat.testBit_or]
      at hID' <;>
    cfg_simp [hE8, aslFPType, run_map, Nat.testBit_or, FPProcessDenorms, HaveAltFP,
      fun v f => run_IsFeatureImplemented (hc.set_FPSR v) f, fun v => run_UsingAArch32 (hc.set_FPSR v),
      get_AH, ofBool_eq_one, hah,
      Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms, Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC,
      Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, fpExcBit, update_one_or, ofNat_or,
      BitVec.or_assoc] <;>
    first | (cases v1.eq v2 <;> cases v1.lt v2 <;> rfl)
  · have hE15 := fun v => run_FPProcessException (hc.set_FPSR v) .FPExc_InputDenorm fpcr hb15 (get?_set_FPSR s v)
    have hIO' : Nat.testBit _ 0 = false := Bool.eq_false_iff.mpr fun h => hb8 (hIO h)
    by_cases hah : fpcr.toNat / 2 ^ 1 % 2 = 1 <;> cases sig <;> cases t1 <;> cases t2 <;>
    try simp (config := { decide := true }) [Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms,
      Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC, Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah,
      Nat.testBit_or]
      at hIO' <;>
    cfg_simp [hE15, aslFPType, run_map, Nat.testBit_or, FPProcessDenorms, HaveAltFP,
      fun v f => run_IsFeatureImplemented (hc.set_FPSR v) f, fun v => run_UsingAArch32 (hc.set_FPSR v),
      get_AH, ofBool_eq_one, hah,
      Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms, Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC,
      Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, fpExcBit, update_one_or, ofNat_or,
      BitVec.or_assoc] <;>
    first | (cases v1.eq v2 <;> cases v1.lt v2 <;> rfl)
  · have hIO' : Nat.testBit _ 0 = false := Bool.eq_false_iff.mpr fun h => hb8 (hIO h)
    have hID' : Nat.testBit _ 7 = false := Bool.eq_false_iff.mpr fun h => hb15 (hID h)
    by_cases hah : fpcr.toNat / 2 ^ 1 % 2 = 1 <;> cases sig <;> cases t1 <;> cases t2 <;>
    try simp (config := { decide := true }) [Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms,
      Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC, Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah,
      Nat.testBit_or]
      at hIO' hID' <;>
    cfg_simp [aslFPType, run_map, Nat.testBit_or, FPProcessDenorms, HaveAltFP,
      fun v f => run_IsFeatureImplemented (hc.set_FPSR v) f, fun v => run_UsingAArch32 (hc.set_FPSR v),
      get_AH, ofBool_eq_one, hah,
      Janus.Arm64.FP.FPType.isNaN, Janus.Arm64.FP.processDenorms, Janus.Arm64.FP.raise, Janus.Arm64.FP.IOC,
      Janus.Arm64.FP.IDC, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, fpExcBit, update_one_or, ofNat_or,
      BitVec.or_assoc] <;>
    first | (cases v1.eq v2 <;> cases v1.lt v2 <;> rfl)

end JanusASL.Proofs
