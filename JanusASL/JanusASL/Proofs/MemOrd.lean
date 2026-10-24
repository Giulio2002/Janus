import JanusASL.Proofs.MemPair

/-! # Ordered and exclusive accesses: `Mem_read`/`Mem_set` with the `OrdAcc` descriptors (aligned) -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- What the memory path needs of an access descriptor. -/
structure AccGood (A : AccessDescriptor) : Prop where
  tc : ({ A with tagchecked := false } : AccessDescriptor) = A
  itc : ∀ (t : SState) (va : BitVec 64), LinuxEL0Config t →
    (AArch64_AccessIsTagChecked va { A with tagchecked := true }).run t = .ok false t
  tr : A.transactional = false
  tg : A.tagchecked = false
  ty : A.acctype = .AccessType_GPR

theorem accGood_gpr (w : Bool) : AccGood (gprAcc w) :=
  ⟨rfl, fun _ va hc => run_AccessIsTagChecked_gpr hc va w, rfl, rfl, rfl⟩
theorem accGood_acqRel (w : Bool) : AccGood (acqRelAcc w) :=
  ⟨rfl, fun _ va hc => run_AccessIsTagChecked hc va _ rfl rfl (by cases w <;> simp [acqRelAcc, gprAcc]), rfl, rfl, rfl⟩
theorem accGood_acqPC : AccGood acqPCAcc :=
  ⟨rfl, fun _ va hc => run_AccessIsTagChecked hc va _ rfl rfl (by simp [acqPCAcc, gprAcc]), rfl, rfl, rfl⟩
theorem accGood_excl (w ar : Bool) : AccGood (exclAcc w ar) :=
  ⟨rfl, fun _ va hc => run_AccessIsTagChecked hc va _ rfl rfl (by cases w <;> simp [exclAcc, gprAcc]), rfl, rfl, rfl⟩

theorem run_MemSingle_read_a {t : SState} (m : Janus.Arm64.Memory) (hc : LinuxEL0Config t) {A : AccessDescriptor}
    (hA : AccGood A) {va : BitVec 64} {n : Nat}
    (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16) (hq : va.toNat % 16 + n ≤ 16) (tc aligned ip : Bool)
    (hT : ∃ d, (AArch64_TranslateAddress va A aligned (n : Int)).run t = .ok d t ∧ TransOK d va)
    (hva : va.toNat < 2 ^ 48) (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00)
    (hb : ∀ i < n, t.mem.get? (va.toNat + i) = some (m.bytes (va.toNat + i))) :
    ∃ v, (AArch64_MemSingle_read__1 va n { A with tagchecked := tc } aligned ip).run t = .ok v t ∧
      v.toNat = m.readLE va.toNat n := by
  obtain ⟨d, hd, hok⟩ := hT
  have hn0 : 0 < n := by omega
  obtain ⟨v, hv, hvn⟩ := run_PhysMemRead m hok hva hdev n hn0 A hb
  have hsz : ((n == 1) || ((n == 2) || ((n == 4) || ((n == 8) || (n == 16))))) = true := by
    rcases hn with h | h | h | h | h <;> subst h <;> rfl
  have hai := run_AllInAlignedQuantity t va n (by omega) (by omega) (by omega)
  rw [decide_eq_true hq] at hai
  have hitc := hA.itc t va hc
  unfold AArch64_MemSingle_read__1
  cases tc <;>
  cfg_simp [hsz, HaveLSE2Ext, run_IsFeatureImplemented hc, hai, HaveMTE2Ext, hitc,
    hA.tc, hd, IsFault, hok.fault, HaveTME, run_readReg hc.speInFlight, hok.normal, hok.inner, hok.outer, hv,
    IsFault__2, CreatePhysMemRetStatus]
  all_goals simp only [hA.tr, hA.tg]
  all_goals cfg_simp [run_IsFeatureImplemented hc, run_readReg hc.speInFlight, undefined_PhysMemRetStatus,
    undefined_ErrorState, undefined_Fault, run_internal_pick, hv, CreatePhysMemRetStatus]
  all_goals rw [Nat.mod_eq_of_lt (by rw [show n * 8 = 8 * n from Nat.mul_comm n 8]; exact v.isLt), hvn]

theorem run_MemSingle_set_a {t : SState} (hc : LinuxEL0Config t) {A : AccessDescriptor} (hA : AccGood A)
    {va : BitVec 64} {n : Nat}
    (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16) (hq : va.toNat % 16 + n ≤ 16) (tc aligned ip : Bool)
    (hT : ∃ d, (AArch64_TranslateAddress va A aligned (n : Int)).run t = .ok d t ∧ TransOK d va)
    (hva : va.toNat < 2 ^ 48) (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00) (val : BitVec (n * 8)) :
    (AArch64_MemSingle_set__1 va n { A with tagchecked := tc } aligned ip val).run t =
      .ok () (storeSt t va.toNat n (BitVec.setWidth (8 * n) val)) := by
  obtain ⟨d, hd, hok⟩ := hT
  have hw := fun data => run_PhysMemWrite (t := t) hok hva hdev n A data
  have hsz : ((n == 1) || ((n == 2) || ((n == 4) || ((n == 8) || (n == 16))))) = true := by
    rcases hn with h | h | h | h | h <;> subst h <;> rfl
  have hai := run_AllInAlignedQuantity t va n (by omega) (by omega) (by omega)
  rw [decide_eq_true hq] at hai
  have hitc := hA.itc t va hc
  unfold AArch64_MemSingle_set__1
  cases tc <;>
  cfg_simp [hsz, HaveLSE2Ext, run_IsFeatureImplemented hc, hai, HaveMTE2Ext, hitc,
    hA.tc, hd, IsFault, hok.fault, HaveTME, run_readReg hc.speInFlight, hok.normal, hok.inner, hok.outer,
    IsFault__2, CreatePhysMemRetStatus]
  all_goals simp only [hA.tr, hA.tg]
  all_goals cfg_simp [run_IsFeatureImplemented hc, run_readReg hc.speInFlight, undefined_PhysMemRetStatus,
    undefined_ErrorState, undefined_Fault, run_internal_pick, hw, CreatePhysMemRetStatus]

theorem aligned_quantity {va n : Nat} (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) (hal : va % n = 0) : va % 16 + n ≤ 16 := by
  rcases hn with rfl | rfl | rfl | rfl <;> omega

set_option maxHeartbeats 16000000 in
/-- An aligned `Mem[address, size]` read with any good descriptor. -/
theorem run_Mem_read_al {t : SState} {m : Janus.Arm64.Memory} (hc : LinuxEL0Config t) (hM : MemRel m t)
    {A : AccessDescriptor} (hA : AccGood A) (va : BitVec 64) (n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8)
    (hacc : m.accessible va.toNat n false = true) (hal : va.toNat % n = 0)
    (hT : ∀ al : Bool, ∃ d, (AArch64_TranslateAddress va A al (n : Int)).run t = .ok d t ∧ TransOK d va)
    (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00) (tc : Bool) :
    ∃ v, (Mem_read va n { A with tagchecked := tc }).run t = .ok v t ∧ v.toNat = m.readLE va.toNat n := by
  have hreg := accessible_bytes hacc
  have hlt := accessible_lt hacc
  have hb : ∀ i < n, t.mem.get? (va.toNat + i) = some (m.bytes (va.toNat + i)) := fun i hi => hM _ (hreg i hi)
  have hsz2 : (n == 1 || n == 2 || n == 4 || n == 8 || n == 16) = true := by
    rcases hn with h | h | h | h <;> subst h <;> rfl
  have hal' : IsAligned__1 va (n : Int) = true := by rw [isAligned_iff va n (by omega)]; simp [hal]
  have hq := aligned_quantity hn hal
  have hai := run_AllInAlignedQuantity t va n (by omega) (by omega) (by omega)
  rw [decide_eq_true hq] at hai
  obtain ⟨v, hv, hvn⟩ := run_MemSingle_read_a m hc hA (n := n) (by omega) hq tc true false (hT true)
    (by omega) hdev hb
  refine ⟨v, ?_, hvn⟩
  have hat : ({ A with tagchecked := tc } : AccessDescriptor).acctype = .AccessType_GPR := hA.ty
  unfold Mem_read Mem_read__2
  generalize ({ A with tagchecked := tc } : AccessDescriptor) = B at hat hv ⊢
  cfg_simp [hsz2, undefined_Constraint, run_internal_pick, hat, HaveLSE2Ext, run_IsFeatureImplemented hc, hai,
    run_BigEndian_gpr hc, hal', hv, show (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false from rfl]

set_option maxHeartbeats 16000000 in
/-- An aligned `Mem[address, size] = value` write with any good descriptor. -/
theorem run_Mem_set_al {t : SState} {m : Janus.Arm64.Memory} (hc : LinuxEL0Config t)
    {A : AccessDescriptor} (hA : AccGood A) (va : BitVec 64) (n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8)
    (hacc : m.accessible va.toNat n true = true) (hal : va.toNat % n = 0)
    (hT : ∀ al : Bool, ∃ d, (AArch64_TranslateAddress va A al (n : Int)).run t = .ok d t ∧ TransOK d va)
    (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00) (tc : Bool) (val : BitVec (n * 8)) :
    ∃ t', (Mem_set va n { A with tagchecked := tc } val).run t = .ok () t' ∧ Stored t t' va.toNat n val.toNat := by
  have hlt := accessible_lt hacc
  have hsz2 : (n == 1 || (n == 2 || (n == 4 || (n == 8 || n == 16)))) = true := by
    rcases hn with h | h | h | h <;> subst h <;> rfl
  have hsz3 : (n == 1 || n == 2 || n == 4 || n == 8 || n == 16) = true := by
    rcases hn with h | h | h | h <;> subst h <;> rfl
  have hal' : IsAligned__1 va (n : Int) = true := by rw [isAligned_iff va n (by omega)]; simp [hal]
  have hq := aligned_quantity hn hal
  have hai := run_AllInAlignedQuantity t va n (by omega) (by omega) (by omega)
  rw [decide_eq_true hq] at hai
  have hv := run_MemSingle_set_a hc hA (n := n) (by omega) hq tc true false (hT true) (by omega) hdev val
  refine ⟨_, ?_, stored_storeSt_cast t va.toNat n val⟩
  have hat : ({ A with tagchecked := tc } : AccessDescriptor).acctype = .AccessType_GPR := hA.ty
  unfold Mem_set Mem_set__2
  generalize ({ A with tagchecked := tc } : AccessDescriptor) = B at hat hv ⊢
  cfg_simp [hsz2, hsz3, undefined_Constraint, run_internal_pick, hat, HaveLSE2Ext, run_IsFeatureImplemented hc, hai,
    run_BigEndian_gpr hc, hal', hv, show (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false from rfl]

end JanusASL.Proofs
