import JanusASL.Proofs.Mem

/-! # Stores through the ASL: `Mem_set` on `UserMapped` addresses (see Mem.lean, docs/ASL.md) -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

def memIns (mem : Std.ExtHashMap Nat (BitVec 8)) (L : List (Nat × BitVec 8)) : Std.ExtHashMap Nat (BitVec 8) :=
  L.foldl (fun mm p => mm.insert p.1 p.2) mem

open Sail.ConcurrencyInterfaceV1.PreSail in
theorem run_forM_writeByte (L : List (Nat × BitVec 8)) (t : SState) :
    (List.forM L (fun (p : Nat × BitVec 8) => (writeByte p.1 p.2 : SailM PUnit))).run t =
      .ok () { t with mem := memIns t.mem L } := by
  induction L generalizing t with
  | nil => rfl
  | cons p L ih =>
    rw [show List.forM (p :: L) (fun (p : Nat × BitVec 8) => (writeByte p.1 p.2 : SailM PUnit)) =
      ((writeByte p.1 p.2 : SailM PUnit) >>= fun _ => List.forM L (fun (p : Nat × BitVec 8) => (writeByte p.1 p.2 : SailM PUnit))) from rfl, run_bind]
    rw [show (writeByte p.1 p.2 : SailM PUnit).run t = .ok PUnit.unit { t with mem := t.mem.insert p.1 p.2 } from rfl]
    simp only
    rw [ih]; rfl

theorem memIns_get (mem : Std.ExtHashMap Nat (BitVec 8)) (a n : Nat) (f : Nat → BitVec 8) (x : Nat) :
    (memIns mem (List.ofFn fun i : Fin n => (a + i.val, f i.val))).get? x =
      if a ≤ x ∧ x < a + n then some (f (x - a)) else mem.get? x := by
  induction n generalizing mem a f with
  | zero => simp [memIns]; intro _ _; omega
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [memIns, List.foldl_cons, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    have := ih (mem.insert a (f 0)) (a + 1) (fun k => f (k + 1))
    simp only [memIns] at this
    rw [show (List.ofFn fun i : Fin n => (a + (i.val + 1), f (i.val + 1))) =
      (List.ofFn fun i : Fin n => (a + 1 + i.val, (fun k => f (k + 1)) i.val)) by
        congr 1; funext i; simp only [Nat.add_assoc, Nat.add_comm 1]]
    rw [this, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, ← Std.ExtHashMap.get?_eq_getElem?]
    by_cases h1 : a + 1 ≤ x ∧ x < a + 1 + n
    · rw [if_pos h1, if_pos (by omega)]; congr 2; omega
    · rw [if_neg h1]
      by_cases h2 : x = a
      · subst h2; simp
      · have : (a == x) = false := by simp; omega
        rw [if_neg (by omega : ¬(a ≤ x ∧ x < a + (n + 1)))]
        simp [this]

/-- `t'` is `t` with the `n` bytes of `v` (little-endian) stored at `a`. -/
structure Stored (t t' : SState) (a n v : Nat) : Prop where
  regs : t'.regs = t.regs
  cycle : t'.cycleCount = t.cycleCount
  out : t'.sailOutput = t.sailOutput
  mem : ∀ x, t'.mem.get? x = if a ≤ x ∧ x < a + n then some (BitVec.ofNat 8 (v / 256 ^ (x - a))) else t.mem.get? x

theorem extractLsb'_byte {N : Nat} (v : BitVec N) (k : Nat) :
    v.extractLsb' (8 * k) 8 = BitVec.ofNat 8 (v.toNat / 256 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- The state after storing `data` at `a`. -/
def storeSt (t : SState) (a n : Nat) (data : BitVec (8 * n)) : SState :=
  { t with mem := memIns t.mem (List.ofFn fun i : Fin n => (a + i.val, data.extractLsb' (8 * i.val) 8)) }

theorem stored_storeSt (t : SState) (a n : Nat) (data : BitVec (8 * n)) : Stored t (storeSt t a n data) a n data.toNat :=
  ⟨rfl, rfl, rfl, fun x => by
    rw [storeSt, memIns_get t.mem a n (fun k => data.extractLsb' (8 * k) 8) x]
    simp only [extractLsb'_byte]⟩

open Sail.ConcurrencyInterfaceV1.PreSail in
theorem run_PhysMemWrite {t : SState} {d : AddressDescriptor} {va : BitVec 64}
    (hok : TransOK d va) (hva : va.toNat < 2 ^ 48) (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00)
    (n : Nat) (acc : AccessDescriptor) (data : BitVec (8 * n)) :
    (PhysMemWrite d n acc none data).run t = .ok (CreatePhysMemRetStatus .Fault_None) (storeSt t va.toNat n data) := by
  have g := pa_window_ne va hva GIC_BASE (by simp [GIC_BASE]; omega)
  have u := pa_window_ne va hva UART_BASE (by simp [UART_BASE]; omega)
  have hpa : (va.setWidth 56).toNat = va.toNat := by simp; omega
  unfold PhysMemWrite
  simp only [hok.pa, Sail.BitVec.length]
  split
  · next hc => simp only [Bool.and_eq_true] at hc; exact absurd (g.symm.trans hc.2) Bool.false_ne_true
  split
  · next hc => exact absurd (u.symm.trans hc) Bool.false_ne_true
  simp only [run_bind, sail_mem_write, write_request, hpa, writeBytes, run_forM_writeByte, run_pure]
  rfl

theorem run_MemSingle_set {t : SState} (hc : LinuxEL0Config t) {va : BitVec 64} {n : Nat}
    (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16) (hq : va.toNat % 16 + n ≤ 16) (tc aligned : Bool)
    (hT : ∃ d, (AArch64_TranslateAddress va (gprAcc true) aligned (n : Int)).run t = .ok d t ∧ TransOK d va)
    (hva : va.toNat < 2 ^ 48) (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00) (val : BitVec (n * 8)) :
    (AArch64_MemSingle_set__1 va n { gprAcc true with tagchecked := tc } aligned false val).run t =
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

theorem stored_storeSt_cast (t : SState) (a n : Nat) (val : BitVec (n * 8)) :
    Stored t (storeSt t a n (BitVec.setWidth (8 * n) val)) a n val.toNat := by
  have := stored_storeSt t a n (BitVec.setWidth (8 * n) val)
  rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by rw [show 8 * n = n * 8 from Nat.mul_comm 8 n]; exact val.isLt)]
    at this

theorem TFrame.stored {m : Janus.Arm64.Memory} {s t t' : SState} {a n v : Nat} (hf : TFrame m s t)
    (hs : Stored t t' a n v) (hr : ∀ i < n, InRegion m (a + i) false) : TFrame m s t' where
  regs r h1 h2 h3 := by rw [hs.regs]; exact hf.regs r h1 h2 h3
  mem x hx := by
    rw [hs.mem x, if_neg (fun h => hx (by have := hr (x - a) (by omega); rwa [show a + (x - a) = x by omega] at this))]
    exact hf.mem x hx
  cycle := hs.cycle.trans hf.cycle
  out := hs.out.trans hf.out

theorem LinuxEL0Config.stored {t t' : SState} {a n v : Nat} (hc : LinuxEL0Config t) (hs : Stored t t' a n v) :
    LinuxEL0Config t' :=
  hc.of_eq fun r _ => by
    show t'.regs.get? r = t.regs.get? r
    rw [hs.regs]

theorem Stored.snoc {t s s' : SState} {a i v b : Nat} (h1 : Stored t s a i v) (h2 : Stored s s' (a + i) 1 b)
    (hb : b % 256 = (v / 256 ^ i) % 256) : Stored t s' a (i + 1) v where
  regs := h2.regs.trans h1.regs
  cycle := h2.cycle.trans h1.cycle
  out := h2.out.trans h1.out
  mem x := by
    rw [h2.mem x, h1.mem x]
    by_cases hx : x = a + i
    · subst hx
      rw [if_pos (by omega), if_pos (by omega), show a + i - (a + i) = 0 by omega, show a + i - a = i by omega]
      congr 1; apply BitVec.eq_of_toNat_eq; simp [hb]
    · by_cases hx2 : a ≤ x ∧ x < a + i
      · rw [if_neg (by omega), if_pos hx2, if_pos (by omega)]
      · rw [if_neg (by omega), if_neg hx2, if_neg (by omega)]

theorem run_forIn_unit (start stop : Int) (hsp : (1 : Int) ≠ 0) (hle : start ≤ stop + 1)
    (f : Int → Unit → SailM (ForInStep Unit)) (Q : Int → SState → Prop) (t : SState) (h0 : Q start t)
    (hstep : ∀ i s, start ≤ i → i ≤ stop → Q i s → ∃ s', (f i ()).run s = .ok (.yield ()) s' ∧ Q (i + 1) s') :
    ∃ t', (forIn ({ start := start, stop := stop, step_pos := hsp } : IntRange) () f).run t = .ok () t' ∧
      Q (stop + 1) t' := by
  rw [show forIn ({ start := start, stop := stop, step_pos := hsp } : IntRange) () f =
    IntRange.forIn' ({ start := start, stop := stop, step_pos := hsp } : IntRange) () (fun a _ b => f a b) from rfl]
  unfold IntRange.forIn'
  simp only
  suffices H : ∀ (n : Nat) (i : Int) (hs) (s : SState), start ≤ i → i ≤ stop + 1 → Q i s → (stop - i + 1).toNat = n →
      ∃ t', (IntRange.forIn'.loop ({ start := start, stop := stop, step_pos := hsp } : IntRange)
        (fun a _ b => f a b) () i hs).run s = .ok () t' ∧ Q (stop + 1) t' from H _ start _ t (Int.le_refl _) hle h0 rfl
  intro n
  induction n with
  | zero =>
    intro i hs s hi hi2 hq hn
    rw [IntRange.forIn'.loop]
    have : ¬ i ≤ stop := by omega
    refine ⟨s, by simp [Membership.mem, this], by rwa [show stop + 1 = i by omega]⟩
  | succ n ih =>
    intro i hs s hi hi2 hq hn
    rw [IntRange.forIn'.loop]
    have hle : i ≤ stop := by omega
    have hm : i ∈ ({ start := start, stop := stop, step_pos := hsp } : IntRange) := by
      simp only [Membership.mem]; simp; omega
    obtain ⟨s', hf, hq'⟩ := hstep i s hi hle hq
    obtain ⟨t', ht, hq''⟩ := ih (i + 1) _ s' (by omega) (by omega) hq' (by omega)
    refine ⟨t', ?_, hq''⟩
    simp only [hm, dite_true, run_bind, hf]
    exact ht

theorem run_MemSingle_set_byte {s t : SState} {m : Janus.Arm64.Memory} (hU : UserMapped m s) (hf : TFrame m s t)
    (hc : LinuxEL0Config t) (va : BitVec 64) (hr : InRegion m va.toNat true) (tc al : Bool) (b : BitVec (1 * 8)) :
    (AArch64_MemSingle_set va 1 { gprAcc true with tagchecked := tc } al b).run t =
      .ok () (storeSt t va.toNat 1 (BitVec.setWidth (8 * 1) b)) :=
  run_MemSingle_set hc (n := 1) (Or.inl rfl) (by omega) tc al (hU.trans t hf va true al 1 hr) hr.lt
    (hU.nodev _ hr.read) b

theorem Stored.mod1 {t t' : SState} {a v v' : Nat} (h : Stored t t' a 1 v) (hv : v % 256 = v' % 256) :
    Stored t t' a 1 v' where
  regs := h.regs
  cycle := h.cycle
  out := h.out
  mem x := by
    rw [h.mem x]
    split
    · next hx =>
      rw [show x - a = 0 by omega]
      congr 1; apply BitVec.eq_of_toNat_eq; simp [hv]
    · rfl

theorem run_byteLoop_store {s t : SState} {m : Janus.Arm64.Memory} (hU : UserMapped m s) (hf : TFrame m s t)
    (hc : LinuxEL0Config t) (va : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn8 : n ≤ 16)
    (hreg : ∀ i < n, InRegion m (va.toNat + i) true) (hlt : va.toNat + n ≤ 2 ^ 48) (tc : Bool) (val : BitVec (n * 8))
    (t1 : SState) (h1 : Stored t t1 va.toNat 1 val.toNat) :
    ∃ t', (forIn ({ start := 1, stop := (n : Int) - 1, step_pos := by decide } : IntRange) () fun i (_ : Unit) =>
        ForInStep.yield <$> AArch64_MemSingle_set (Sail.BitVec.addInt va i) 1 { gprAcc true with tagchecked := tc } true
          (BitVec.setWidth 8 (Sail.BitVec.extractLsb val (8 * i + 7).toNat (8 * i).toNat))).run t1 = .ok () t' ∧
      Stored t t' va.toNat n val.toNat := by
  have hrr : ∀ i < n, InRegion m (va.toNat + i) false := fun i hi => (hreg i hi).read
  obtain ⟨t', ht, hq⟩ := run_forIn_unit 1 ((n : Int) - 1) (by decide) (by omega) (fun i (_ : Unit) =>
        ForInStep.yield <$> AArch64_MemSingle_set (Sail.BitVec.addInt va i) 1 { gprAcc true with tagchecked := tc } true
          (BitVec.setWidth 8 (Sail.BitVec.extractLsb val (8 * i + 7).toNat (8 * i).toNat)))
    (fun i u => Stored t u va.toNat i.toNat val.toNat) t1 h1 (by
      intro i u hi1 hi2 hq
      obtain ⟨k, rfl⟩ : ∃ k : Nat, i = k := ⟨i.toNat, by omega⟩
      simp only [Int.toNat_natCast] at hq
      have hfu := hf.stored hq (fun j hj => hrr j (by omega))
      have hcu := hc.stored hq
      have ha := addInt_toNat va k (by omega)
      have hrk := hreg k (by omega)
      rw [← ha] at hrk
      have hb := run_MemSingle_set_byte hU hfu hcu _ hrk tc true
        (BitVec.setWidth 8 (Sail.BitVec.extractLsb val (8 * (k : Int) + 7).toNat (8 * (k : Int)).toNat))
      refine ⟨_, by rw [run_map, hb], ?_⟩
      simp only [show ((k : Int) + 1).toNat = k + 1 by omega]
      refine hq.snoc (by rw [← ha]; exact stored_storeSt _ _ _ _) ?_
      simp [Sail.BitVec.extractLsb, Nat.shiftRight_eq_div_pow, show (8 * (k : Int)).toNat = 8 * k by omega,
        Nat.pow_mul]
      rw [show (8 * (k : Int) + 7).toNat - 8 * k + 1 = 8 by omega]
      simp)
  refine ⟨t', ht, ?_⟩
  simpa [show ((n : Int) - 1 + 1).toNat = n by omega] using hq

theorem run_Mem_set {s t : SState} {m : Janus.Arm64.Memory} (hU : UserMapped m s) (hf : TFrame m s t)
    (hc : LinuxEL0Config t) (va : BitVec 64) (n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8)
    (hacc : m.accessible va.toNat n true = true) (tc : Bool) (val : BitVec (n * 8)) :
    ∃ t', (Mem_set va n { gprAcc true with tagchecked := tc } val).run t = .ok () t' ∧
      Stored t t' va.toNat n val.toNat := by
  have hreg := accessible_bytes hacc
  have hlt := accessible_lt hacc
  have hr0 : InRegion m va.toNat true := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  have hal := isAligned_iff va n (by omega)
  have hai := run_AllInAlignedQuantity t va n (by omega) (by omega) (by omega)
  have hU1 := run_UnalignedAccessFaults_gpr hc true tc va n
  have hat : ({ gprAcc true with tagchecked := tc } : AccessDescriptor).acctype = .AccessType_GPR := rfl
  by_cases hq : va.toNat % 16 + n ≤ 16
  · have hv := run_MemSingle_set hc (n := n) (by omega) hq tc (IsAligned__1 va n)
      (hU.trans t hf va true _ n hr0) hr0.lt (hU.nodev _ hr0.read) val
    rw [decide_eq_true hq] at hai
    refine ⟨_, ?_, stored_storeSt_cast t va.toNat n val⟩
    unfold Mem_set Mem_set__2
    generalize ({ gprAcc true with tagchecked := tc } : AccessDescriptor) = A at hU1 hat hv ⊢
    have hsz2 : (n == 1 || (n == 2 || (n == 4 || (n == 8 || n == 16)))) = true := by
      rcases hn with h | h | h | h <;> subst h <;> rfl
    have hsz3 : (n == 1 || n == 2 || n == 4 || n == 8 || n == 16) = true := by
      rcases hn with h | h | h | h <;> subst h <;> rfl
    cases ha : IsAligned__1 va (n : Int) <;> rw [ha] at hv <;>
    cfg_simp [hsz2, hsz3, undefined_Constraint, run_internal_pick, hU1, hat, HaveLSE2Ext, run_IsFeatureImplemented hc, hai,
      run_BigEndian_gpr hc, ha, hv, show (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false from rfl]
    all_goals done
  · rw [decide_eq_false hq] at hai
    have hn2 : n = 2 ∨ n = 4 ∨ n = 8 := by omega
    have hna : IsAligned__1 va (n : Int) = false := by
      rw [hal]; apply decide_eq_false; intro h0; apply hq
      rcases hn2 with h | h | h <;> subst h <;> omega
    have h0 := fun b => run_MemSingle_set_byte hU hf hc va hr0 tc false b
    unfold Mem_set Mem_set__2
    generalize hA : ({ gprAcc true with tagchecked := tc } : AccessDescriptor) = A at hU1 hat h0 ⊢
    rcases hn2 with rfl | rfl | rfl <;> simp only [Int.cast_ofNat_Int, Int.reduceSub, Nat.reduceMul] at hna hai hU1 <;>
    cfg_simp [undefined_Constraint, run_internal_pick, hU1, hat, HaveLSE2Ext, run_IsFeatureImplemented hc, hai,
      run_BigEndian_gpr hc, hna, h0, show (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false from rfl,
      ConstrainUnpredictable, __UNKNOWN_Constraint, HaveLRCPC3Ext,
      show Int.ediv 2 2 = 1 from rfl, show Int.ediv 4 2 = 2 from rfl, show Int.ediv 8 2 = 4 from rfl,
      show (Constraint.Constraint_NONE == Constraint.Constraint_NONE) = true from rfl,
      show (Constraint.Constraint_NONE == Constraint.Constraint_FAULT) = false from rfl]
    all_goals subst hA
    all_goals refine run_byteLoop_store hU hf hc va _ (by omega) (by omega) hreg hlt tc val _ ?_
    all_goals exact (stored_storeSt _ _ _ _).mod1 (by simp [Sail.BitVec.extractLsb])

end JanusASL.Proofs