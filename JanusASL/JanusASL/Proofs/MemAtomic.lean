import JanusASL.Proofs.MemOrd

/-! # Atomic read-modify-write: `MemAtomic` with the `atomAcc` descriptors -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem accGood_atom (op : MemAtomicOp) (a r : Bool) : AccGood (atomAcc op a r) :=
  ⟨rfl, fun _ va hc => run_AccessIsTagChecked hc va _ rfl rfl (by simp [atomAcc, gprAcc]), rfl, rfl, rfl⟩

theorem run_StoreOnlyTagCheckingEnabled {s : SState} (hc : LinuxEL0Config s) :
    (StoreOnlyTagCheckingEnabled 0#2).run s = .ok false s := by
  cfg_simp [StoreOnlyTagCheckingEnabled, HaveMTEStoreOnlyExt, run_IsFeatureImplemented hc, EL0, run_ELIsInHost hc,
    run_readReg hc.sctlr1, _get_SCTLR_EL1_Type_TCSO0]

/-- The new value and compare-fail flag of `MemAtomic` (as its `match accdesc.modop`). -/
def aslAtomicNew {k : Nat} (op : MemAtomicOp) (cmp old operand : BitVec k) : Bool × BitVec k :=
  match op with
  | .MemAtomicOp_ADD => (false, old + operand)
  | .MemAtomicOp_BIC => (false, old &&& ~~~operand)
  | .MemAtomicOp_EOR => (false, old ^^^ operand)
  | .MemAtomicOp_ORR => (false, old ||| operand)
  | .MemAtomicOp_SMAX => (false, integer_subrange (max old.toInt operand.toInt) ((k : Int) - 1) 0)
  | .MemAtomicOp_SMIN => (false, integer_subrange (min old.toInt operand.toInt) ((k : Int) - 1) 0)
  | .MemAtomicOp_UMAX => (false, integer_subrange (max (old.toNat : Int) (operand.toNat : Int)) ((k : Int) - 1) 0)
  | .MemAtomicOp_UMIN => (false, integer_subrange (min (old.toNat : Int) (operand.toNat : Int)) ((k : Int) - 1) 0)
  | .MemAtomicOp_SWP => (false, operand)
  | .MemAtomicOp_CAS => (cmp != old, operand)
  | .MemAtomicOp_GCSSS1 => (cmp != old, operand)

theorem spe_storeSt {t : SState} (hc : LinuxEL0Config t) (a n : Nat) (v : BitVec (8 * n)) :
    (readReg Register.SPESampleInFlight).run (storeSt t a n v) = .ok false (storeSt t a n v) :=
  run_readReg (s := storeSt t a n v) hc.speInFlight

set_option maxHeartbeats 16000000 in
theorem run_MemAtomic8 {t : SState} {m : Janus.Arm64.Memory} (hc : LinuxEL0Config t) (hM : MemRel m t)
    (op : MemAtomicOp) (a r tc : Bool) (va : BitVec 64)
    (hT : ∀ (al : Bool) (sz : Int), ∃ d, (AArch64_TranslateAddress va (atomAcc op a r) al sz).run t = .ok d t ∧ TransOK d va)
    (hal : va.toNat % 1 = 0) (hacc : m.accessible va.toNat 1 true = true)
    (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00)
    (cmp operand : BitVec 8) :
    (MemAtomic va cmp operand { atomAcc op a r with tagchecked := tc }).run t =
      .ok (BitVec.ofNat 8 (m.readLE va.toNat 1))
        (if (aslAtomicNew op cmp (BitVec.ofNat 8 (m.readLE va.toNat 1)) operand).1 then t
         else storeSt t va.toNat (Int.ediv 8 8).toNat (BitVec.setWidth (8 * (Int.ediv 8 8).toNat)
          (aslAtomicNew op cmp (BitVec.ofNat 8 (m.readLE va.toNat 1)) operand).2)) := by
  have hitc := (accGood_atom op a r).itc t va hc
  have hitc2 : (AArch64_AccessIsTagChecked va
      { ({ atomAcc op a r with tagchecked := true } : AccessDescriptor) with tagchecked := true }).run t = .ok false t :=
    hitc
  have e0 : ({ ({ atomAcc op a r with tagchecked := true } : AccessDescriptor) with tagchecked := false } :
      AccessDescriptor) = atomAcc op a r := rfl
  have hal' : IsAligned__1 va (Int.ediv 8 8) = true := by
    rw [show Int.ediv 8 8 = ((1 : Nat) : Int) from rfl, isAligned_iff va 1 (by decide)]; simp [hal]
  obtain ⟨d, hd, hok⟩ := hT true 8
  have hlt := accessible_lt hacc
  have hreg := accessible_bytes hacc
  obtain ⟨v, hv, hvn⟩ := run_PhysMemRead m hok (by omega) hdev (Int.ediv 8 8).toNat (by decide) (atomAcc op a r)
    (fun i hi => hM _ (hreg i (by rw [show (Int.ediv 8 8).toNat = 1 from rfl] at hi; exact hi)).read)
  have hw := fun data => run_PhysMemWrite (t := t) hok (by omega) hdev (Int.ediv 8 8).toNat (atomAcc op a r) data
  have e1 : ({ atomAcc op a r with tagchecked := false } : AccessDescriptor) = atomAcc op a r := rfl
  have e2 : (atomAcc op a r).atomicop = true := rfl
  have e3 : (atomAcc op a r).tagchecked = false := rfl
  have e4 : (atomAcc op a r).el = 0#2 := rfl
  have e5 : (atomAcc op a r).acctype = .AccessType_GPR := rfl
  have e6 : (atomAcc op a r).modop = op := rfl
  unfold MemAtomic
  generalize atomAcc op a r = A at *
  have hal4 : IsAligned__1 va 1 = true := hal'
  have hvn' : v.toNat = m.readLE va.toNat 1 := hvn
  have hsw : BitVec.setWidth 8 v = BitVec.ofNat 8 (m.readLE va.toNat 1) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, hvn', BitVec.toNat_ofNat]
  simp only [e2, e3, e4, e5, e6] at hitc hitc2 e0 e1
  cases tc <;>
  cfg_simp [HaveMTE2Ext, run_IsFeatureImplemented hc, hitc, hitc2, e0, e1, e2, e3, e4, e5, e6, hal', hal4, hd, IsFault,
    hok.fault, HaveMTEStoreOnlyExt, run_StoreOnlyTagCheckingEnabled hc, undefined_PhysMemRetStatus,
    undefined_ErrorState, undefined_Fault, run_internal_pick, hv, CreatePhysMemRetStatus, IsFault__2,
    run_BigEndian_gpr hc, run_readReg hc.speInFlight, show Int.ediv 8 8 = 1 from rfl, hw, hsw]
  all_goals cases op <;> simp only [aslAtomicNew]
  all_goals first
    | (cfg_simp [run_BigEndian_gpr hc, hw, run_readReg hc.speInFlight, spe_storeSt hc, IsFault__2,
        CreatePhysMemRetStatus]; done)
    | (by_cases hcmp : cmp = m.bytes va.toNat <;>
       cfg_simp [hcmp, run_BigEndian_gpr hc, hw, run_readReg hc.speInFlight, spe_storeSt hc, IsFault__2, CreatePhysMemRetStatus])

set_option maxHeartbeats 16000000 in
theorem run_MemAtomic16 {t : SState} {m : Janus.Arm64.Memory} (hc : LinuxEL0Config t) (hM : MemRel m t)
    (op : MemAtomicOp) (a r tc : Bool) (va : BitVec 64)
    (hT : ∀ (al : Bool) (sz : Int), ∃ d, (AArch64_TranslateAddress va (atomAcc op a r) al sz).run t = .ok d t ∧ TransOK d va)
    (hal : va.toNat % 2 = 0) (hacc : m.accessible va.toNat 2 true = true)
    (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00)
    (cmp operand : BitVec 16) :
    (MemAtomic va cmp operand { atomAcc op a r with tagchecked := tc }).run t =
      .ok (BitVec.ofNat 16 (m.readLE va.toNat 2))
        (if (aslAtomicNew op cmp (BitVec.ofNat 16 (m.readLE va.toNat 2)) operand).1 then t
         else storeSt t va.toNat (Int.ediv 16 8).toNat (BitVec.setWidth (8 * (Int.ediv 16 8).toNat)
          (aslAtomicNew op cmp (BitVec.ofNat 16 (m.readLE va.toNat 2)) operand).2)) := by
  have hitc := (accGood_atom op a r).itc t va hc
  have hitc2 : (AArch64_AccessIsTagChecked va
      { ({ atomAcc op a r with tagchecked := true } : AccessDescriptor) with tagchecked := true }).run t = .ok false t :=
    hitc
  have e0 : ({ ({ atomAcc op a r with tagchecked := true } : AccessDescriptor) with tagchecked := false } :
      AccessDescriptor) = atomAcc op a r := rfl
  have hal' : IsAligned__1 va (Int.ediv 16 8) = true := by
    rw [show Int.ediv 16 8 = ((2 : Nat) : Int) from rfl, isAligned_iff va 2 (by decide)]; simp [hal]
  obtain ⟨d, hd, hok⟩ := hT true 16
  have hlt := accessible_lt hacc
  have hreg := accessible_bytes hacc
  obtain ⟨v, hv, hvn⟩ := run_PhysMemRead m hok (by omega) hdev (Int.ediv 16 8).toNat (by decide) (atomAcc op a r)
    (fun i hi => hM _ (hreg i (by rw [show (Int.ediv 16 8).toNat = 2 from rfl] at hi; exact hi)).read)
  have hw := fun data => run_PhysMemWrite (t := t) hok (by omega) hdev (Int.ediv 16 8).toNat (atomAcc op a r) data
  have e1 : ({ atomAcc op a r with tagchecked := false } : AccessDescriptor) = atomAcc op a r := rfl
  have e2 : (atomAcc op a r).atomicop = true := rfl
  have e3 : (atomAcc op a r).tagchecked = false := rfl
  have e4 : (atomAcc op a r).el = 0#2 := rfl
  have e5 : (atomAcc op a r).acctype = .AccessType_GPR := rfl
  have e6 : (atomAcc op a r).modop = op := rfl
  unfold MemAtomic
  generalize atomAcc op a r = A at *
  have hal4 : IsAligned__1 va 2 = true := hal'
  have hvn' : v.toNat = m.readLE va.toNat 2 := hvn
  have hsw : BitVec.setWidth 16 v = BitVec.ofNat 16 (m.readLE va.toNat 2) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, hvn', BitVec.toNat_ofNat]
  simp only [e2, e3, e4, e5, e6] at hitc hitc2 e0 e1
  cases tc <;>
  cfg_simp [HaveMTE2Ext, run_IsFeatureImplemented hc, hitc, hitc2, e0, e1, e2, e3, e4, e5, e6, hal', hal4, hd, IsFault,
    hok.fault, HaveMTEStoreOnlyExt, run_StoreOnlyTagCheckingEnabled hc, undefined_PhysMemRetStatus,
    undefined_ErrorState, undefined_Fault, run_internal_pick, hv, CreatePhysMemRetStatus, IsFault__2,
    run_BigEndian_gpr hc, run_readReg hc.speInFlight, show Int.ediv 16 8 = 2 from rfl, hw, hsw]
  all_goals cases op <;> simp only [aslAtomicNew]
  all_goals first
    | (cfg_simp [run_BigEndian_gpr hc, hw, run_readReg hc.speInFlight, spe_storeSt hc, IsFault__2,
        CreatePhysMemRetStatus]; done)
    | (by_cases hcmp : cmp = BitVec.ofNat 16 (m.readLE va.toNat 2) <;>
       cfg_simp [hcmp, run_BigEndian_gpr hc, hw, run_readReg hc.speInFlight, spe_storeSt hc, IsFault__2, CreatePhysMemRetStatus])

set_option maxHeartbeats 16000000 in
theorem run_MemAtomic32 {t : SState} {m : Janus.Arm64.Memory} (hc : LinuxEL0Config t) (hM : MemRel m t)
    (op : MemAtomicOp) (a r tc : Bool) (va : BitVec 64)
    (hT : ∀ (al : Bool) (sz : Int), ∃ d, (AArch64_TranslateAddress va (atomAcc op a r) al sz).run t = .ok d t ∧ TransOK d va)
    (hal : va.toNat % 4 = 0) (hacc : m.accessible va.toNat 4 true = true)
    (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00)
    (cmp operand : BitVec 32) :
    (MemAtomic va cmp operand { atomAcc op a r with tagchecked := tc }).run t =
      .ok (BitVec.ofNat 32 (m.readLE va.toNat 4))
        (if (aslAtomicNew op cmp (BitVec.ofNat 32 (m.readLE va.toNat 4)) operand).1 then t
         else storeSt t va.toNat (Int.ediv 32 8).toNat (BitVec.setWidth (8 * (Int.ediv 32 8).toNat)
          (aslAtomicNew op cmp (BitVec.ofNat 32 (m.readLE va.toNat 4)) operand).2)) := by
  have hitc := (accGood_atom op a r).itc t va hc
  have hitc2 : (AArch64_AccessIsTagChecked va
      { ({ atomAcc op a r with tagchecked := true } : AccessDescriptor) with tagchecked := true }).run t = .ok false t :=
    hitc
  have e0 : ({ ({ atomAcc op a r with tagchecked := true } : AccessDescriptor) with tagchecked := false } :
      AccessDescriptor) = atomAcc op a r := rfl
  have hal' : IsAligned__1 va (Int.ediv 32 8) = true := by
    rw [show Int.ediv 32 8 = ((4 : Nat) : Int) from rfl, isAligned_iff va 4 (by decide)]; simp [hal]
  obtain ⟨d, hd, hok⟩ := hT true 32
  have hlt := accessible_lt hacc
  have hreg := accessible_bytes hacc
  obtain ⟨v, hv, hvn⟩ := run_PhysMemRead m hok (by omega) hdev (Int.ediv 32 8).toNat (by decide) (atomAcc op a r)
    (fun i hi => hM _ (hreg i (by rw [show (Int.ediv 32 8).toNat = 4 from rfl] at hi; exact hi)).read)
  have hw := fun data => run_PhysMemWrite (t := t) hok (by omega) hdev (Int.ediv 32 8).toNat (atomAcc op a r) data
  have e1 : ({ atomAcc op a r with tagchecked := false } : AccessDescriptor) = atomAcc op a r := rfl
  have e2 : (atomAcc op a r).atomicop = true := rfl
  have e3 : (atomAcc op a r).tagchecked = false := rfl
  have e4 : (atomAcc op a r).el = 0#2 := rfl
  have e5 : (atomAcc op a r).acctype = .AccessType_GPR := rfl
  have e6 : (atomAcc op a r).modop = op := rfl
  unfold MemAtomic
  generalize atomAcc op a r = A at *
  have hal4 : IsAligned__1 va 4 = true := hal'
  have hvn' : v.toNat = m.readLE va.toNat 4 := hvn
  have hsw : BitVec.setWidth 32 v = BitVec.ofNat 32 (m.readLE va.toNat 4) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, hvn', BitVec.toNat_ofNat]
  simp only [e2, e3, e4, e5, e6] at hitc hitc2 e0 e1
  cases tc <;>
  cfg_simp [HaveMTE2Ext, run_IsFeatureImplemented hc, hitc, hitc2, e0, e1, e2, e3, e4, e5, e6, hal', hal4, hd, IsFault,
    hok.fault, HaveMTEStoreOnlyExt, run_StoreOnlyTagCheckingEnabled hc, undefined_PhysMemRetStatus,
    undefined_ErrorState, undefined_Fault, run_internal_pick, hv, CreatePhysMemRetStatus, IsFault__2,
    run_BigEndian_gpr hc, run_readReg hc.speInFlight, show Int.ediv 32 8 = 4 from rfl, hw, hsw]
  all_goals cases op <;> simp only [aslAtomicNew]
  all_goals first
    | (cfg_simp [run_BigEndian_gpr hc, hw, run_readReg hc.speInFlight, spe_storeSt hc, IsFault__2,
        CreatePhysMemRetStatus]; done)
    | (by_cases hcmp : cmp = BitVec.ofNat 32 (m.readLE va.toNat 4) <;>
       cfg_simp [hcmp, run_BigEndian_gpr hc, hw, run_readReg hc.speInFlight, spe_storeSt hc, IsFault__2, CreatePhysMemRetStatus])

set_option maxHeartbeats 16000000 in
theorem run_MemAtomic64 {t : SState} {m : Janus.Arm64.Memory} (hc : LinuxEL0Config t) (hM : MemRel m t)
    (op : MemAtomicOp) (a r tc : Bool) (va : BitVec 64)
    (hT : ∀ (al : Bool) (sz : Int), ∃ d, (AArch64_TranslateAddress va (atomAcc op a r) al sz).run t = .ok d t ∧ TransOK d va)
    (hal : va.toNat % 8 = 0) (hacc : m.accessible va.toNat 8 true = true)
    (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00)
    (cmp operand : BitVec 64) :
    (MemAtomic va cmp operand { atomAcc op a r with tagchecked := tc }).run t =
      .ok (BitVec.ofNat 64 (m.readLE va.toNat 8))
        (if (aslAtomicNew op cmp (BitVec.ofNat 64 (m.readLE va.toNat 8)) operand).1 then t
         else storeSt t va.toNat (Int.ediv 64 8).toNat (BitVec.setWidth (8 * (Int.ediv 64 8).toNat)
          (aslAtomicNew op cmp (BitVec.ofNat 64 (m.readLE va.toNat 8)) operand).2)) := by
  have hitc := (accGood_atom op a r).itc t va hc
  have hitc2 : (AArch64_AccessIsTagChecked va
      { ({ atomAcc op a r with tagchecked := true } : AccessDescriptor) with tagchecked := true }).run t = .ok false t :=
    hitc
  have e0 : ({ ({ atomAcc op a r with tagchecked := true } : AccessDescriptor) with tagchecked := false } :
      AccessDescriptor) = atomAcc op a r := rfl
  have hal' : IsAligned__1 va (Int.ediv 64 8) = true := by
    rw [show Int.ediv 64 8 = ((8 : Nat) : Int) from rfl, isAligned_iff va 8 (by decide)]; simp [hal]
  obtain ⟨d, hd, hok⟩ := hT true 64
  have hlt := accessible_lt hacc
  have hreg := accessible_bytes hacc
  obtain ⟨v, hv, hvn⟩ := run_PhysMemRead m hok (by omega) hdev (Int.ediv 64 8).toNat (by decide) (atomAcc op a r)
    (fun i hi => hM _ (hreg i (by rw [show (Int.ediv 64 8).toNat = 8 from rfl] at hi; exact hi)).read)
  have hw := fun data => run_PhysMemWrite (t := t) hok (by omega) hdev (Int.ediv 64 8).toNat (atomAcc op a r) data
  have e1 : ({ atomAcc op a r with tagchecked := false } : AccessDescriptor) = atomAcc op a r := rfl
  have e2 : (atomAcc op a r).atomicop = true := rfl
  have e3 : (atomAcc op a r).tagchecked = false := rfl
  have e4 : (atomAcc op a r).el = 0#2 := rfl
  have e5 : (atomAcc op a r).acctype = .AccessType_GPR := rfl
  have e6 : (atomAcc op a r).modop = op := rfl
  unfold MemAtomic
  generalize atomAcc op a r = A at *
  have hal4 : IsAligned__1 va 8 = true := hal'
  have hvn' : v.toNat = m.readLE va.toNat 8 := hvn
  have hsw : BitVec.setWidth 64 v = BitVec.ofNat 64 (m.readLE va.toNat 8) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, hvn', BitVec.toNat_ofNat]
  simp only [e2, e3, e4, e5, e6] at hitc hitc2 e0 e1
  cases tc <;>
  cfg_simp [HaveMTE2Ext, run_IsFeatureImplemented hc, hitc, hitc2, e0, e1, e2, e3, e4, e5, e6, hal', hal4, hd, IsFault,
    hok.fault, HaveMTEStoreOnlyExt, run_StoreOnlyTagCheckingEnabled hc, undefined_PhysMemRetStatus,
    undefined_ErrorState, undefined_Fault, run_internal_pick, hv, CreatePhysMemRetStatus, IsFault__2,
    run_BigEndian_gpr hc, run_readReg hc.speInFlight, show Int.ediv 64 8 = 8 from rfl, hw, hsw]
  all_goals cases op <;> simp only [aslAtomicNew]
  all_goals first
    | (cfg_simp [run_BigEndian_gpr hc, hw, run_readReg hc.speInFlight, spe_storeSt hc, IsFault__2,
        CreatePhysMemRetStatus]; done)
    | (by_cases hcmp : cmp = BitVec.ofNat 64 (m.readLE va.toNat 8) <;>
       cfg_simp [hcmp, run_BigEndian_gpr hc, hw, run_readReg hc.speInFlight, spe_storeSt hc, IsFault__2, CreatePhysMemRetStatus])

end JanusASL.Proofs
