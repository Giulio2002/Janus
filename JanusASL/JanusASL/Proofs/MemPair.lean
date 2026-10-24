import JanusASL.Proofs.MemWrite

/-! # Paired accesses (`ispair`): LDP/STP through `Mem_read__1`/`Mem_set__1` -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_MemSingle_read_p {t : SState} (m : Janus.Arm64.Memory) (hc : LinuxEL0Config t) {va : BitVec 64} {n : Nat}
    (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16) (hq : va.toNat % 16 + n ≤ 16) (tc aligned ip : Bool)
    (hT : ∃ d, (AArch64_TranslateAddress va (gprAcc false) aligned (n : Int)).run t = .ok d t ∧ TransOK d va)
    (hva : va.toNat < 2 ^ 48) (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00)
    (hb : ∀ i < n, t.mem.get? (va.toNat + i) = some (m.bytes (va.toNat + i))) :
    ∃ v, (AArch64_MemSingle_read__1 va n { gprAcc false with tagchecked := tc } aligned ip).run t = .ok v t ∧
      v.toNat = m.readLE va.toNat n := by
  obtain ⟨d, hd, hok⟩ := hT
  have hn0 : 0 < n := by omega
  obtain ⟨v, hv, hvn⟩ := run_PhysMemRead m hok hva hdev n hn0 (gprAcc false) hb
  have hsz : ((n == 1) || ((n == 2) || ((n == 4) || ((n == 8) || (n == 16))))) = true := by
    rcases hn with h | h | h | h | h <;> subst h <;> rfl
  have hai := run_AllInAlignedQuantity t va n (by omega) (by omega) (by omega)
  rw [decide_eq_true hq] at hai
  unfold AArch64_MemSingle_read__1
  cases tc <;>
  cfg_simp [hsz, HaveLSE2Ext, run_IsFeatureImplemented hc, hai, HaveMTE2Ext, run_AccessIsTagChecked_gpr hc,
    gprAcc_tc, hd, IsFault, hok.fault, HaveTME, run_readReg hc.speInFlight, hok.normal, hok.inner, hok.outer, hv,
    IsFault__2, CreatePhysMemRetStatus]
  all_goals simp only [gprAcc_transactional, gprAcc_tagchecked]
  all_goals cfg_simp [run_IsFeatureImplemented hc, run_readReg hc.speInFlight, undefined_PhysMemRetStatus,
    undefined_ErrorState, undefined_Fault, run_internal_pick, hv, CreatePhysMemRetStatus]
  all_goals rw [Nat.mod_eq_of_lt (by rw [show n * 8 = 8 * n from Nat.mul_comm n 8]; exact v.isLt), hvn]

theorem run_MemSingle_set_p {t : SState} (hc : LinuxEL0Config t) {va : BitVec 64} {n : Nat}
    (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16) (hq : va.toNat % 16 + n ≤ 16) (tc aligned ip : Bool)
    (hT : ∃ d, (AArch64_TranslateAddress va (gprAcc true) aligned (n : Int)).run t = .ok d t ∧ TransOK d va)
    (hva : va.toNat < 2 ^ 48) (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00) (val : BitVec (n * 8)) :
    (AArch64_MemSingle_set__1 va n { gprAcc true with tagchecked := tc } aligned ip val).run t =
      .ok () (storeSt t va.toNat n (BitVec.setWidth (8 * n) val)) := by
  obtain ⟨d, hd, hok⟩ := hT
  have hw := fun data => run_PhysMemWrite (t := t) hok hva hdev n (gprAcc true) data
  have hsz : ((n == 1) || ((n == 2) || ((n == 4) || ((n == 8) || (n == 16))))) = true := by
    rcases hn with h | h | h | h | h <;> subst h <;> rfl
  have hai := run_AllInAlignedQuantity t va n (by omega) (by omega) (by omega)
  rw [decide_eq_true hq] at hai
  unfold AArch64_MemSingle_set__1
  cases tc <;>
  cfg_simp [hsz, HaveLSE2Ext, run_IsFeatureImplemented hc, hai, HaveMTE2Ext, run_AccessIsTagChecked_gpr hc,
    gprAcc_tc, hd, IsFault, hok.fault, HaveTME, run_readReg hc.speInFlight, hok.normal, hok.inner, hok.outer,
    IsFault__2, CreatePhysMemRetStatus]
  all_goals simp only [gprAcc_transactional, gprAcc_tagchecked]
  all_goals cfg_simp [run_IsFeatureImplemented hc, run_readReg hc.speInFlight, undefined_PhysMemRetStatus,
    undefined_ErrorState, undefined_Fault, run_internal_pick, hw, CreatePhysMemRetStatus]

theorem readLE_add (m : Janus.Arm64.Memory) (a i j : Nat) :
    m.readLE a (i + j) = m.readLE a i + 2 ^ (8 * i) * m.readLE (a + i) j := by
  induction i generalizing a with
  | zero => simp [Janus.Arm64.Memory.readLE]
  | succ i ih =>
    rw [show i + 1 + j = (i + j) + 1 by omega, Janus.Arm64.Memory.readLE, ih (a + 1), Janus.Arm64.Memory.readLE,
      show a + 1 + i = a + (i + 1) by omega, show 8 * (i + 1) = 8 + 8 * i by omega, Nat.pow_add]
    have : (2 : Nat) ^ 8 = 256 := rfl
    rw [this]; simp only [Nat.mul_add, Nat.mul_assoc]; omega

set_option maxHeartbeats 16000000 in
/-- **A paired read** (`Mem[address, 2 * dbytes]` with `ispair`, as LDP does under FEAT_LSE2): one
access inside a 16-byte quantity, two halves when the address is aligned to the half size, the byte
loop otherwise. -/
theorem run_Mem_read_pair {s t : SState} {m : Janus.Arm64.Memory} (hU : UserMapped m s) (hf : TFrame m s t)
    (hc : LinuxEL0Config t) (hM : MemRel m t) (va : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16)
    (hreg : ∀ i < n, InRegion m (va.toNat + i) false) (hlt : va.toNat + n ≤ 2 ^ 48) (tc : Bool) :
    ∃ v, (Mem_read__1 va n { gprAcc false with tagchecked := tc } true).run t = .ok v t ∧
      v.toNat = m.readLE va.toNat n := by
  have hr0 : InRegion m va.toNat false := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  have hb : ∀ i < n, t.mem.get? (va.toNat + i) = some (m.bytes (va.toNat + i)) := fun i hi => hM _ (hreg i hi)
  have hai := run_AllInAlignedQuantity t va n (by omega) (by omega) (by omega)
  have hU1 := run_UnalignedAccessFaults_gpr hc false tc va n
  have hat : ({ gprAcc false with tagchecked := tc } : AccessDescriptor).acctype = .AccessType_GPR := rfl
  have hal := isAligned_iff va (n / 2) (by omega)
  by_cases hq : va.toNat % 16 + n ≤ 16
  · obtain ⟨v, hv, hvn⟩ := run_MemSingle_read_p m hc (n := n) (by omega) hq tc (IsAligned__1 va (n / 2 : Nat)) true
      (hU.trans t hf va false _ n hr0) hr0.lt (hU.nodev _ hr0) hb
    rw [decide_eq_true hq] at hai
    refine ⟨v, ?_, hvn⟩
    unfold Mem_read__1 Mem_read__2
    generalize ({ gprAcc false with tagchecked := tc } : AccessDescriptor) = A at hU1 hat hv ⊢
    rcases hn with rfl | rfl <;> simp only [Int.cast_ofNat_Int, Nat.reduceDiv] at hal hai hU1 hv <;>
    cases ha : IsAligned__1 va 4 <;> cases ha8 : IsAligned__1 va 8 <;> (try rw [ha] at hv) <;> (try rw [ha8] at hv) <;>
    cfg_simp [undefined_Constraint, run_internal_pick, hU1, hat, HaveLSE2Ext, run_IsFeatureImplemented hc, hai,
      run_BigEndian_gpr hc, ha, ha8, hv, show (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false from rfl,
      show Int.ediv 8 2 = 4 from rfl, show Int.ediv 16 2 = 8 from rfl]
  · rw [decide_eq_false hq] at hai
    by_cases hh : va.toNat % (n / 2) = 0
    · -- aligned to the half size: two half accesses
      have hhn : (Int.ediv (n : Int) 2).toNat = n / 2 := by rcases hn with rfl | rfl <;> rfl
      have hal' : IsAligned__1 va (Int.ediv (n : Int) 2) = true := by
        rw [show Int.ediv (n : Int) 2 = ((n / 2 : Nat) : Int) by rcases hn with rfl | rfl <;> rfl, hal]; simp [hh]
      have hq1 : va.toNat % 16 + (Int.ediv (n : Int) 2).toNat ≤ 16 := by
        rw [hhn]; rcases hn with rfl | rfl <;> simp at hh ⊢ <;> omega
      have hlo : ∀ i < (Int.ediv (n : Int) 2).toNat, t.mem.get? (va.toNat + i) = some (m.bytes (va.toNat + i)) :=
        fun i hi => hb i (by rw [hhn] at hi; omega)
      obtain ⟨v1, hv1, hvn1⟩ := run_MemSingle_read m hc (n := (Int.ediv (n : Int) 2).toNat) (by rw [hhn]; omega) hq1 tc true
        (hU.trans t hf va false _ _ hr0) hr0.lt (hU.nodev _ hr0) hlo
      have ha2 := addInt_toNat va (n / 2) (by omega)
      rw [show ((n / 2 : Nat) : Int) = Int.ediv (n : Int) 2 by omega] at ha2
      have hr2 : InRegion m (Sail.BitVec.addInt va (Int.ediv (n : Int) 2)).toNat false := by
        rw [ha2]; exact hreg _ (by omega)
      have hq2 : (Sail.BitVec.addInt va (Int.ediv (n : Int) 2)).toNat % 16 + (Int.ediv (n : Int) 2).toNat ≤ 16 := by
        rw [ha2, hhn]; rcases hn with rfl | rfl <;> simp at hh hq ⊢ <;> omega
      have hhi : ∀ i < (Int.ediv (n : Int) 2).toNat, t.mem.get? ((Sail.BitVec.addInt va (Int.ediv (n : Int) 2)).toNat + i) =
          some (m.bytes ((Sail.BitVec.addInt va (Int.ediv (n : Int) 2)).toNat + i)) := fun i hi => by
        rw [ha2, Nat.add_assoc]; exact hb _ (by rw [hhn] at hi; omega)
      obtain ⟨v2, hv2, hvn2⟩ := run_MemSingle_read m hc (n := (Int.ediv (n : Int) 2).toNat) (by rw [hhn]; omega) hq2 tc true
        (hU.trans t hf _ false _ _ hr2) hr2.lt (hU.nodev _ hr2) hhi
      have hs1 : (decide ((n : Int) > 1)) = true := by simp; omega
      have hs2 : (Int.ediv (n : Int) 2 == 1 || Int.ediv (n : Int) 2 == 2 || Int.ediv (n : Int) 2 == 4 ||
          Int.ediv (n : Int) 2 == 8) = true := by rcases hn with rfl | rfl <;> rfl
      have hs3 : (n == 1 || n == 2 || n == 4 || n == 8 || n == 16) = true := by rcases hn with rfl | rfl <;> rfl
      refine ⟨v2 +++ v1, ?_, ?_⟩
      · unfold Mem_read__1 Mem_read__2
        generalize ({ gprAcc false with tagchecked := tc } : AccessDescriptor) = A at hU1 hat hv1 hv2 ⊢
        simp only [ite_true]
        cfg_simp [undefined_Constraint, run_internal_pick, hU1, hat, HaveLSE2Ext, run_IsFeatureImplemented hc, hai,
          run_BigEndian_gpr hc, hal', AArch64_MemSingle_read, hv1, hv2, HaveLRCPC3Ext, hs1, hs2, hs3,
          show (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false from rfl]
        all_goals done
      · have hv1lt := v1.isLt
        have hv2lt := v2.isLt
        rw [BitVec.toNat_setWidth]
        show (v2 ++ v1).toNat % _ = _
        rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt hv1lt, Nat.shiftLeft_eq, hvn1, hvn2, ha2, hhn]
        rw [show n = n / 2 + n / 2 by omega, readLE_add, show (n / 2 + n / 2) / 2 = n / 2 by omega]
        rw [show 2 ^ (n / 2 * 8) = 2 ^ (8 * (n / 2)) by rw [Nat.mul_comm]]
        have b1 := readLE_lt m (va.toNat + n / 2) (n / 2)
        have b2 := readLE_lt m va.toNat (n / 2)
        have hX : 2 ^ ((n / 2 + n / 2) * 8) = 2 ^ (8 * (n / 2)) * 2 ^ (8 * (n / 2)) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [hX]
        generalize 2 ^ (8 * (n / 2)) = X at *
        generalize m.readLE (va.toNat + n / 2) (n / 2) = a at *
        generalize m.readLE va.toNat (n / 2) = b at *
        have : (a + 1) * X ≤ X * X := Nat.mul_le_mul_right _ b1
        rw [Nat.mod_eq_of_lt (by rw [Nat.add_mul] at this; omega), Nat.mul_comm X a]
        omega
    · -- unaligned: the byte loop
      have hna : IsAligned__1 va (Int.ediv (n : Int) 2) = false := by
        rw [show Int.ediv (n : Int) 2 = ((n / 2 : Nat) : Int) by rcases hn with rfl | rfl <;> rfl, hal]; simp [hh]
      have h0 := run_MemSingle_read_byte hU hf hc hM va hr0 tc false
      have h1 : ∀ i : Int, 1 ≤ i → i ≤ (n : Int) - 1 →
          (AArch64_MemSingle_read (Sail.BitVec.addInt va i) 1 { gprAcc false with tagchecked := tc } true).run t =
            .ok (BitVec.ofNat (1 * 8) (m.bytes (va.toNat + i.toNat)).toNat) t := by
        intro i hi1 hi2
        obtain ⟨k, rfl⟩ : ∃ k : Nat, i = k := ⟨i.toNat, by omega⟩
        have ha := addInt_toNat va k (by omega)
        have hrk := hreg k (by omega)
        rw [← ha] at hrk
        rw [run_MemSingle_read_byte hU hf hc hM _ hrk tc true, ha, Int.toNat_natCast]
      have hinit : (Sail.BitVec.updateSubrange (0#(n * 8)) 7 0 (m.bytes va.toNat)).toNat = m.readLE va.toNat 1 := by
        rw [Sail.BitVec.updateSubrange, updateSubrange'_toNat_low _ _ _ _ (by omega) (by simp)]
        simp [Janus.Arm64.Memory.readLE]
      obtain ⟨v, hv, hvn⟩ := run_byteLoop_read m { gprAcc false with tagchecked := tc } true va n (by omega) (by omega)
        h1 _ hinit
      have hs3 : (n == 1 || n == 2 || n == 4 || n == 8 || n == 16) = true := by rcases hn with rfl | rfl <;> rfl
      refine ⟨v, ?_, hvn⟩
      unfold Mem_read__1 Mem_read__2
      generalize ({ gprAcc false with tagchecked := tc } : AccessDescriptor) = A at hU1 hat h0 h1 hv ⊢
      rcases hn with rfl | rfl <;> simp only [Int.cast_ofNat_Int, Int.reduceSub, Nat.reduceMul,
        show Int.ediv 8 2 = 4 from rfl, show Int.ediv 16 2 = 8 from rfl] at hna hai hU1 h1 hv <;>
      cfg_simp [hs3, undefined_Constraint, run_internal_pick, hU1, hat, HaveLSE2Ext, run_IsFeatureImplemented hc, hai,
        run_BigEndian_gpr hc, hna, h0, show (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false from rfl,
        ConstrainUnpredictable, __UNKNOWN_Constraint, HaveLRCPC3Ext,
        show Int.ediv 8 2 = 4 from rfl, show Int.ediv 16 2 = 8 from rfl,
        show (Constraint.Constraint_NONE == Constraint.Constraint_NONE) = true from rfl,
        show (Constraint.Constraint_NONE == Constraint.Constraint_FAULT) = false from rfl]
      all_goals erw [hv]
      all_goals simp only [run_BigEndian_gpr hc, Bool.false_eq_true, ite_false, run_pure]


theorem byteMod_eq {x v k j : Nat} (hj : j < k) (h : x % 2 ^ (8 * k) = v % 2 ^ (8 * k)) :
    x / 256 ^ j % 256 = v / 256 ^ j % 256 := by
  have hd : 256 ^ j * 256 ∣ 2 ^ (8 * k) := by
    rw [show 256 ^ j * 256 = 2 ^ (8 * (j + 1)) by rw [Nat.pow_mul, Nat.pow_succ]]
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self (m := v), ← Nat.mod_mod_of_dvd x hd,
    ← Nat.mod_mod_of_dvd v hd, h]

theorem Stored.append {t t1 t2 : SState} {a a2 h h' x1 x2 v : Nat} (s1 : Stored t t1 a h x1)
    (s2 : Stored t1 t2 a2 h' x2) (ha2 : a2 = a + h) (hx1 : x1 % 2 ^ (8 * h) = v % 2 ^ (8 * h))
    (hx2 : x2 % 2 ^ (8 * h') = (v / 2 ^ (8 * h)) % 2 ^ (8 * h')) : Stored t t2 a (h + h') v where
  regs := s2.regs.trans s1.regs
  cycle := s2.cycle.trans s1.cycle
  out := s2.out.trans s1.out
  mem x := by
    subst ha2
    rw [s2.mem x, s1.mem x]
    by_cases hA : a ≤ x ∧ x < a + h
    · rw [if_neg (by omega), if_pos hA, if_pos (by omega)]
      congr 1; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from rfl]
      exact byteMod_eq (by omega) hx1
    · by_cases hB : a + h ≤ x ∧ x < a + h + h'
      · rw [if_pos hB, if_pos (by omega)]
        congr 1; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from rfl]
        rw [byteMod_eq (by omega) hx2, Nat.div_div_eq_div_mul, show (2 : Nat) ^ (8 * h) = 256 ^ h by
          rw [Nat.pow_mul], ← Nat.pow_add, show h + (x - (a + h)) = x - a by omega]
      · rw [if_neg hB, if_neg hA, if_neg (by omega)]

set_option maxHeartbeats 16000000 in
/-- **A paired write** (`Mem[address, 2 * dbytes] = data` with `ispair`, as STP does under FEAT_LSE2). -/
theorem run_Mem_set_pair {s t : SState} {m : Janus.Arm64.Memory} (hU : UserMapped m s) (hf : TFrame m s t)
    (hc : LinuxEL0Config t) (va : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16)
    (hreg : ∀ i < n, InRegion m (va.toNat + i) true) (hlt : va.toNat + n ≤ 2 ^ 48) (tc : Bool) (val : BitVec (n * 8)) :
    ∃ t', (Mem_set__1 va n { gprAcc true with tagchecked := tc } true val).run t = .ok () t' ∧
      Stored t t' va.toNat n val.toNat := by
  have hr0 : InRegion m va.toNat true := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  have hal := isAligned_iff va (n / 2) (by omega)
  have hai := run_AllInAlignedQuantity t va n (by omega) (by omega) (by omega)
  have hU1 := run_UnalignedAccessFaults_gpr hc true tc va n
  have hat : ({ gprAcc true with tagchecked := tc } : AccessDescriptor).acctype = .AccessType_GPR := rfl
  have hed : Int.ediv (n : Int) 2 = ((n / 2 : Nat) : Int) := by rcases hn with rfl | rfl <;> rfl
  have hs3 : (n == 1 || n == 2 || n == 4 || n == 8 || n == 16) = true := by rcases hn with rfl | rfl <;> rfl
  have hs3' : (n == 1 || (n == 2 || (n == 4 || (n == 8 || n == 16)))) = true := by rcases hn with rfl | rfl <;> rfl
  by_cases hq : va.toNat % 16 + n ≤ 16
  · have hv := run_MemSingle_set_p hc (n := n) (by omega) hq tc (IsAligned__1 va (Int.ediv (n : Int) 2)) true
      (hU.trans t hf va true _ n hr0) hr0.lt (hU.nodev _ hr0.read) val
    rw [decide_eq_true hq] at hai
    refine ⟨_, ?_, stored_storeSt_cast t va.toNat n val⟩
    unfold Mem_set__1 Mem_set__2
    generalize ({ gprAcc true with tagchecked := tc } : AccessDescriptor) = A at hU1 hat hv ⊢
    cases ha : IsAligned__1 va (Int.ediv (n : Int) 2) <;> rw [ha] at hv <;>
    cfg_simp [hs3, hs3', undefined_Constraint, run_internal_pick, hU1, hat, HaveLSE2Ext, run_IsFeatureImplemented hc,
      hai, run_BigEndian_gpr hc, ha, hv, show (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false from rfl]
    all_goals done
  · rw [decide_eq_false hq] at hai
    have hhn : (Int.ediv (n : Int) 2).toNat = n / 2 := by rcases hn with rfl | rfl <;> rfl
    by_cases hh : va.toNat % (n / 2) = 0
    · have hal' : IsAligned__1 va (Int.ediv (n : Int) 2) = true := by rw [hed, hal]; simp [hh]
      have hq1 : va.toNat % 16 + (Int.ediv (n : Int) 2).toNat ≤ 16 := by
        rw [hhn]; rcases hn with rfl | rfl <;> simp at hh ⊢ <;> omega
      have hw1 := fun data => run_MemSingle_set hc (n := (Int.ediv (n : Int) 2).toNat) (by rw [hhn]; omega) hq1 tc true
        (hU.trans t hf va true _ _ hr0) hr0.lt (hU.nodev _ hr0.read) data
      have ha2 := addInt_toNat va (n / 2) (by omega)
      rw [← hed] at ha2
      have hr2 : InRegion m (Sail.BitVec.addInt va (Int.ediv (n : Int) 2)).toNat true := by
        rw [ha2]; exact hreg _ (by omega)
      have hq2 : (Sail.BitVec.addInt va (Int.ediv (n : Int) 2)).toNat % 16 + (Int.ediv (n : Int) 2).toNat ≤ 16 := by
        rw [ha2, hhn]; rcases hn with rfl | rfl <;> simp at hh hq ⊢ <;> omega
      have hlo : ∀ i < (Int.ediv (n : Int) 2).toNat, InRegion m (va.toNat + i) false :=
        fun i hi => (hreg i (by rw [hhn] at hi; omega)).read
      have hw2 := fun (d1 : BitVec ((Int.ediv (n : Int) 2).toNat * 8)) data =>
        run_MemSingle_set (hc.stored (stored_storeSt_cast t va.toNat _ d1)) (n := (Int.ediv (n : Int) 2).toNat)
          (by rw [hhn]; omega) hq2 tc true
          (hU.trans _ (hf.stored (stored_storeSt_cast t va.toNat _ d1) hlo) _ true _ _ hr2) hr2.lt
          (hU.nodev _ hr2.read) data
      have hs1 : (decide ((n : Int) > 1)) = true := by simp; omega
      have hs2 : (Int.ediv (n : Int) 2 == 1 || Int.ediv (n : Int) 2 == 2 || Int.ediv (n : Int) 2 == 4 ||
          Int.ediv (n : Int) 2 == 8 || Int.ediv (n : Int) 2 == 16) = true := by rcases hn with rfl | rfl <;> rfl
      have hs4 : (decide (Int.ediv (n : Int) 2 > 0)) = true := by rcases hn with rfl | rfl <;> rfl
      have hs5 : ((n : Int) * 8 == Int.ediv (n : Int) 2 * 8 + Int.ediv (n : Int) 2 * 8) = true := by
        rcases hn with rfl | rfl <;> rfl
      unfold Mem_set__1 Mem_set__2
      generalize ({ gprAcc true with tagchecked := tc } : AccessDescriptor) = A at hU1 hat hw1 hw2 ⊢
      simp only [ite_true]
      cfg_simp [undefined_Constraint, run_internal_pick, hU1, hat, HaveLSE2Ext, run_IsFeatureImplemented hc, hai,
        run_BigEndian_gpr hc, hal', hw1, hw2, HaveLRCPC3Ext, hs1, hs2, hs3, hs4, hs5,
        show (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false from rfl]
      have st1 := stored_storeSt t va.toNat _ (BitVec.setWidth (8 * ((n : Int).ediv 2).toNat)
          (BitVec.setWidth (((n : Int).ediv 2).toNat * 8)
            (Sail.BitVec.extractLsb val ((n : Int) * 8 - 1 - (n : Int).ediv 2 * 8).toNat
              ((n : Int) * 8 - 1 - (n : Int).ediv 2 * 8 - (n : Int).ediv 2 * 8 + 1).toNat)))
      have st2 := stored_storeSt (storeSt t va.toNat ((n : Int).ediv 2).toNat (BitVec.setWidth (8 * ((n : Int).ediv 2).toNat)
          (BitVec.setWidth (((n : Int).ediv 2).toNat * 8)
            (Sail.BitVec.extractLsb val ((n : Int) * 8 - 1 - (n : Int).ediv 2 * 8).toNat
              ((n : Int) * 8 - 1 - (n : Int).ediv 2 * 8 - (n : Int).ediv 2 * 8 + 1).toNat))))
        (Sail.BitVec.addInt va ((n : Int).ediv 2)).toNat _ (BitVec.setWidth (8 * ((n : Int).ediv 2).toNat)
          (BitVec.setWidth (((n : Int).ediv 2).toNat * 8)
            (Sail.BitVec.extractLsb val ((n : Int) * 8 - 1).toNat ((n : Int) * 8 - 1 - (n : Int).ediv 2 * 8 + 1).toNat)))
      have := Stored.append st1 st2 (v := val.toNat) (by rw [ha2, hhn]) ?_ ?_
      · rwa [hhn, show n / 2 + n / 2 = n by omega] at this
      all_goals rcases hn with rfl | rfl <;>
        simp [Sail.BitVec.extractLsb, Nat.shiftRight_eq_div_pow, Nat.mod_mod_of_dvd, show Int.ediv 8 2 = 4 from rfl,
          show Int.ediv 16 2 = 8 from rfl]
    · have hna : IsAligned__1 va (Int.ediv (n : Int) 2) = false := by rw [hed, hal]; simp [hh]
      have h0 := fun b => run_MemSingle_set_byte hU hf hc va hr0 tc false b
      unfold Mem_set__1 Mem_set__2
      generalize hA : ({ gprAcc true with tagchecked := tc } : AccessDescriptor) = A at hU1 hat h0 ⊢
      rcases hn with rfl | rfl <;> simp only [Int.cast_ofNat_Int, Int.reduceSub, Nat.reduceMul,
        show Int.ediv 8 2 = 4 from rfl, show Int.ediv 16 2 = 8 from rfl] at hna hai hU1 <;>
      cfg_simp [undefined_Constraint, run_internal_pick, hU1, hat, HaveLSE2Ext, run_IsFeatureImplemented hc, hai,
        run_BigEndian_gpr hc, hna, h0, show (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false from rfl,
        ConstrainUnpredictable, __UNKNOWN_Constraint, HaveLRCPC3Ext,
        show Int.ediv 8 2 = 4 from rfl, show Int.ediv 16 2 = 8 from rfl,
        show (Constraint.Constraint_NONE == Constraint.Constraint_NONE) = true from rfl,
        show (Constraint.Constraint_NONE == Constraint.Constraint_FAULT) = false from rfl]
      all_goals subst hA
      all_goals refine run_byteLoop_store hU hf hc va _ (by omega) (by omega) hreg hlt tc val _ ?_
      all_goals exact (stored_storeSt _ _ _ _).mod1 (by simp [Sail.BitVec.extractLsb])


end JanusASL.Proofs
