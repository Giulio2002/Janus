import JanusASL.Proofs.DP1

/-! # Proved: REV16, REV32, REV (data-processing, 1 source)

ASL REV is a doubly nested loop over containers and bytes with assertions on the indices;
`run_forIn_inv` runs each loop under an index invariant, `intFold_succ`/`intFold_done` unroll the
resulting folds (at most 8 bytes), and the unrolled result is compared with Janus'
`revContainersNat` bit by bit (`revContainersNat_testBit`). -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- A step-1 `IntRange` loop whose body, under an invariant, completes without changing the
state: the loop is the fold of the body's results. -/
theorem run_forIn_inv {β : Type} (start stop : Int) (hsp : (1 : Int) ≠ 0) (init : β)
    (f : Int → β → SailM (ForInStep β)) (g : Int → β → β) (P : Int → β → Prop) (s : SState)
    (h0 : P start init)
    (hstep : ∀ i b, start ≤ i → i ≤ stop → P i b → (f i b).run s = .ok (.yield (g i b)) s ∧ P (i + 1) (g i b)) :
    (forIn ({ start := start, stop := stop, step_pos := hsp } : IntRange) init f).run s =
      .ok (intFold g start stop init) s := by
  rw [show forIn ({ start := start, stop := stop, step_pos := hsp } : IntRange) init f =
    IntRange.forIn' ({ start := start, stop := stop, step_pos := hsp } : IntRange) init (fun a _ b => f a b) from rfl]
  unfold IntRange.forIn'
  simp only
  suffices H : ∀ (n : Nat) (i : Int) (hs) (b : β), start ≤ i → P i b → (stop - i + 1).toNat = n →
      (IntRange.forIn'.loop ({ start := start, stop := stop, step_pos := hsp } : IntRange)
        (fun a _ b => f a b) b i hs).run s = .ok (intFold g i stop b) s from H _ start _ init (Int.le_refl _) h0 rfl
  intro n
  induction n with
  | zero =>
    intro i hs b hi hp hn
    rw [IntRange.forIn'.loop, intFold]
    have : ¬ i ≤ stop := by omega
    simp [Membership.mem, this]
  | succ n ih =>
    intro i hs b hi hp hn
    rw [IntRange.forIn'.loop, intFold]
    have hle : i ≤ stop := by omega
    have hm : i ∈ ({ start := start, stop := stop, step_pos := hsp } : IntRange) := by
      simp only [Membership.mem]; simp; omega
    obtain ⟨hf, hp'⟩ := hstep i b hi hle hp
    simp only [hm, dite_true, hle, ite_true, run_bind, hf]
    exact ih (i + 1) _ (g i b) (by omega) hp' (by omega)

end JanusASL.Proofs
namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem getLsbD_updateSubrange' {N : Nat} (x : BitVec N) (lo len : Nat) (y : BitVec len) (k : Nat)
    (hlen : lo + len ≤ N) :
    (Sail.BitVec.updateSubrange' x lo len y).getLsbD k =
      if lo ≤ k ∧ k < lo + len then y.getLsbD (k - lo) else x.getLsbD k := by
  simp only [Sail.BitVec.updateSubrange']
  by_cases hkN : k < N
  · by_cases h1 : lo ≤ k ∧ k < lo + len
    · rw [if_pos h1]
      simp [BitVec.getLsbD_shiftLeft, hkN, h1.1, show ¬ k < lo by omega, show k - lo < len by omega]
    · rw [if_neg h1]
      by_cases h2 : k < lo
      · simp [BitVec.getLsbD_shiftLeft, hkN, h2]
      · have : y.getLsbD (k - lo) = false := BitVec.getLsbD_of_ge y _ (by omega)
        simp [BitVec.getLsbD_shiftLeft, hkN, h2, this]; omega
  · have e1 : x.getLsbD k = false := BitVec.getLsbD_of_ge x k (by omega)
    simp [hkN, BitVec.getLsbD_shiftLeft, e1]
    intro _ _; omega

end JanusASL.Proofs

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem intFold_inv {β : Type} (g : Int → β → β) (P : Int → β → Prop) (start stop : Int) (init : β)
    (hle : start ≤ stop + 1) (h0 : P start init)
    (hstep : ∀ i b, start ≤ i → i ≤ stop → P i b → P (i + 1) (g i b)) :
    P (stop + 1) (intFold g start stop init) := by
  suffices H : ∀ (n : Nat) (i : Int) (b : β), start ≤ i → i ≤ stop + 1 → P i b → (stop - i + 1).toNat = n →
      P (stop + 1) (intFold g i stop b) from H _ start init (Int.le_refl _) hle h0 rfl
  intro n
  induction n with
  | zero =>
    intro i b hi hi2 hp hn
    rw [intFold, if_neg (by omega)]
    rwa [show stop + 1 = i by omega]
  | succ n ih =>
    intro i b hi hi2 hp hn
    rw [intFold, if_pos (by omega)]
    exact ih (i + 1) (g i b) (by omega) (by omega) (hstep i b hi (by omega) hp) (by omega)

/-- One step of REV's inner (byte) loop. -/
def revIn {N : Nat} (x : BitVec N) (_e : Int) (st : Int × BitVec N × Int) : Int × BitVec N × Int :=
  (st.1 + 8, Sail.BitVec.updateSubrange st.2.1 (st.2.2 + 7).toNat st.2.2.toNat
    (BitVec.setWidth ((st.2.2 + 7).toNat - st.2.2.toNat + 1) (Sail.BitVec.extractLsb x (st.1 + 7).toNat st.1.toNat)),
   st.2.2 - 8)

theorem revIn_fst {N : Nat} (x : BitVec N) (m : Int) (init : Int × BitVec N × Int) (hm : 0 ≤ m + 1) :
    (intFold (revIn x) 0 m init).1 = init.1 + 8 * (m + 1) := by
  have := intFold_inv (revIn x) (fun e (st' : Int × BitVec N × Int) => st'.1 = init.1 + 8 * e) 0 m init hm
    (by simp) (fun e b _ _ hb => by simp only [revIn] at hb ⊢; omega)
  simpa using this

/-- One step of REV's outer (container) loop; `E` bytes per container. -/
def revOut {N : Nat} (x : BitVec N) (E : Int) (_c : Int) (st : Int × BitVec N × Int) : Int × BitVec N × Int :=
  let r := intFold (revIn x) 0 (E - 1) (st.1, st.2.1, st.1 + (E - 1) * 8)
  (r.1, r.2.1, r.2.2)

set_option maxHeartbeats 8000000 in
theorem run_execute_rev {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {C N : Nat}
    (hCN : (C = 16 ∧ N = 32) ∨ (C = 32 ∧ N = 32) ∨ (C = 16 ∧ N = 64) ∨ (C = 32 ∧ N = 64) ∨ (C = 64 ∧ N = 64))
    {d n : Nat} (hn : n < 32) :
    (execute_aarch64_instrs_integer_arithmetic_rev C d N n).run s =
      (X_set d N (intFold (revOut (js.getX N n) ((C : Int) / 8)) 0 ((N : Int) / C - 1) (0, 0#N, 0)).2.1).run s := by
  have hed : ∀ a b : Int, Int.ediv a b = a / b := fun _ _ => rfl
  have hx32 := run_X_read_rel h hn (N := 32) (Or.inl rfl)
  have hx64 := run_X_read_rel h hn (N := 64) (Or.inr rfl)
  simp only [execute_aarch64_instrs_integer_arithmetic_rev, run_bind, run_undefined_bitvector, run_undefined_int, hed]
  generalize hE : ((C : Int) / 8) = E
  generalize hK : ((N : Int) / C - 1) = K
  rcases hCN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp at hE hK
    subst hK
    simp only [hx32, hx64]
    rw [run_forIn_inv 0 _ _ _ _ (revOut _ E) (fun c st => st.1 = 8 * E * c) s (by simp) ?step]
    · rfl
    case step =>
      intro c st hc0 hc hP
      simp only [run_bind, run_pure]
      rw [run_forIn_inv 0 _ _ _ _ (revIn _)
        (fun e (st' : type_of% st) => st'.1 = st.1 + 8 * e ∧ st'.2.2 + 8 * e = st.1 + (E - 1) * 8) s
        (by subst hE; simp) ?inner]
      · subst hE
        refine ⟨rfl, ?_⟩
        simp only [revOut]
        rw [revIn_fst _ _ _ ?hm]
        simp only at hP ⊢
        omega
        case hm => omega
      case inner =>
        intro e st' he0 he hp
        subst hE
        obtain ⟨h1, h2⟩ := hp
        simp only [run_bind]
        rw [run_sail_assert_of ?a1]
        simp only
        rw [run_sail_assert_of ?a2]
        simp only [run_pure]
        refine ⟨rfl, ?_, ?_⟩ <;> simp only [revIn] <;> try omega
        case a1 => simp; generalize st'.2.2 = r at h2 ⊢; generalize st.1 = q at hP h2; constructor <;> omega
        case a2 => simp; generalize st'.1 = r at h1 ⊢; generalize st.1 = q at hP h1; constructor <;> omega

end JanusASL.Proofs
namespace JanusASL.Proofs
open ArmASL ArmASL.Functions
theorem intFold_succ {β : Type} (g : Int → β → β) {i stop : Int} (b : β) (h : i ≤ stop) :
    intFold g i stop b = intFold g (i + 1) stop (g i b) := by rw [intFold, if_pos h]
theorem intFold_done {β : Type} (g : Int → β → β) {i stop : Int} (b : β) (h : stop < i) :
    intFold g i stop b = b := by rw [intFold, if_neg (by omega)]


theorem revBytesNat_lt (n x : Nat) : Janus.Arm64.revBytesNat n x < 2 ^ (8 * n) := by
  induction n generalizing x with
  | zero => simp [Janus.Arm64.revBytesNat]
  | succ n ih =>
    simp only [Janus.Arm64.revBytesNat]
    have h1 := ih (x / 256)
    have h2 : x % 256 < 256 := Nat.mod_lt _ (by decide)
    have e : 256 ^ n = 2 ^ (8 * n) := by rw [Nat.pow_mul]
    rw [e, show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add]
    have : x % 256 * 2 ^ (8 * n) ≤ 255 * 2 ^ (8 * n) := Nat.mul_le_mul_right _ (by omega)
    have : 2 ^ 8 = 256 := rfl
    omega

theorem revBytesNat_testBit (n x i : Nat) :
    (Janus.Arm64.revBytesNat n x).testBit i = (decide (i < 8 * n) && x.testBit (8 * (n - 1 - i / 8) + i % 8)) := by
  induction n generalizing x i with
  | zero => simp [Janus.Arm64.revBytesNat]
  | succ n ih =>
    simp only [Janus.Arm64.revBytesNat]
    have e : 256 ^ n = 2 ^ (8 * n) := by rw [Nat.pow_mul]
    rw [e, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (revBytesNat_lt n (x / 256))]
    split
    · rw [ih, show x / 256 = x / 2 ^ 8 from rfl, Nat.testBit_div_two_pow]
      simp only [show i < 8 * (n + 1) from by omega, decide_true, Bool.true_and,
        show i < 8 * n from by omega]
      congr 1; omega
    · by_cases hi : i - 8 * n < 8
      · have : x % 256 = x % 2 ^ 8 := rfl
        rw [this, Nat.testBit_mod_two_pow]
        simp only [hi, decide_true, Bool.true_and, show i < 8 * (n + 1) from by omega]
        congr 1; omega
      · have : (x % 256).testBit (i - 8 * n) = false := Nat.testBit_lt_two_pow (by
          calc x % 256 < 256 := Nat.mod_lt _ (by decide)
            _ = 2 ^ 8 := rfl
            _ ≤ 2 ^ (i - 8 * n) := Nat.pow_le_pow_right (by decide) (by omega))
        rw [this]; simp; omega

theorem revContainersNat_testBit (cb : Nat) (hcb : cb = 2 ∨ cb = 4 ∨ cb = 8) (c x i : Nat) :
    (Janus.Arm64.revContainersNat cb c x).testBit i =
      (decide (i < 8 * cb * c) && x.testBit (8 * cb * (i / (8 * cb)) + 8 * (cb - 1 - (i % (8 * cb)) / 8) + i % 8)) := by
  induction c generalizing x i with
  | zero => simp [Janus.Arm64.revContainersNat]
  | succ c ih =>
    simp only [Janus.Arm64.revContainersNat]
    have e : ∀ k, (256 : Nat) ^ k = 2 ^ (8 * k) := fun k => by rw [Nat.pow_mul]
    rw [e, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (revBytesNat_lt _ _)]
    split
    · rw [revBytesNat_testBit, Nat.testBit_mod_two_pow]
      have key : 8 * (cb - 1 - i / 8) + i % 8 = 8 * cb * (i / (8 * cb)) + 8 * (cb - 1 - i % (8 * cb) / 8) + i % 8 := by
        rcases hcb with rfl | rfl | rfl <;> omega
      have c1 : (8 * (cb - 1 - i / 8) + i % 8 < 8 * cb) := by rcases hcb with rfl | rfl | rfl <;> omega
      have c2 : i < 8 * cb * (c + 1) := by rcases hcb with rfl | rfl | rfl <;> omega
      rw [key] at c1 ⊢
      simp [c1, c2, *]
    · rw [ih, Nat.testBit_div_two_pow]
      have key : 8 * cb * ((i - 8 * cb) / (8 * cb)) + 8 * (cb - 1 - (i - 8 * cb) % (8 * cb) / 8) + (i - 8 * cb) % 8 + 8 * cb =
          8 * cb * (i / (8 * cb)) + 8 * (cb - 1 - i % (8 * cb) / 8) + i % 8 := by
        rcases hcb with rfl | rfl | rfl <;> omega
      have c2 : (i - 8 * cb < 8 * cb * c) = (i < 8 * cb * (c + 1)) := by
        apply propext; rcases hcb with rfl | rfl | rfl <;> omega
      rw [key]
      simp only [c2]

open ArmASL ArmASL.Functions

set_option maxHeartbeats 40000000 in
theorem rev_val_16_32 (x : BitVec 32) : (intFold (revOut x 2) 0 1 (0, 0#32, 0)).2.1 =
    BitVec.ofNat 32 (Janus.Arm64.revContainersNat 2 2 x.toNat) := by
  simp (config := {decide := true}) only [intFold_succ, intFold_done, revOut, revIn, Int.reduceAdd, Int.reduceSub,
    Int.reduceMul]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_ofNat, revContainersNat_testBit 2 (by decide)]
  simp only [Sail.BitVec.updateSubrange, Int.reduceToNat]
  simp (disch := omega) only [getLsbD_updateSubrange', BitVec.getLsbD_setWidth, Sail.BitVec.extractLsb,
    BitVec.getLsbD_extractLsb, if_pos, if_neg, BitVec.getLsbD_zero]
  have : x.toNat.testBit = x.getLsbD := rfl
  rw [this]
  repeat' split
  all_goals
    congr 1
    · rw [decide_eq_decide]; omega
    congr 1
    · rw [decide_eq_decide]; omega
    congr 1; omega

set_option maxHeartbeats 40000000 in
theorem rev_val_32_32 (x : BitVec 32) : (intFold (revOut x 4) 0 0 (0, 0#32, 0)).2.1 =
    BitVec.ofNat 32 (Janus.Arm64.revContainersNat 4 1 x.toNat) := by
  simp (config := {decide := true}) only [intFold_succ, intFold_done, revOut, revIn, Int.reduceAdd, Int.reduceSub,
    Int.reduceMul]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_ofNat, revContainersNat_testBit 4 (by decide)]
  simp only [Sail.BitVec.updateSubrange, Int.reduceToNat]
  simp (disch := omega) only [getLsbD_updateSubrange', BitVec.getLsbD_setWidth, Sail.BitVec.extractLsb,
    BitVec.getLsbD_extractLsb, if_pos, if_neg, BitVec.getLsbD_zero]
  have : x.toNat.testBit = x.getLsbD := rfl
  rw [this]
  repeat' split
  all_goals
    congr 1
    · rw [decide_eq_decide]; omega
    congr 1
    · rw [decide_eq_decide]; omega
    congr 1; omega

set_option maxHeartbeats 40000000 in
theorem rev_val_16_64 (x : BitVec 64) : (intFold (revOut x 2) 0 3 (0, 0#64, 0)).2.1 =
    BitVec.ofNat 64 (Janus.Arm64.revContainersNat 2 4 x.toNat) := by
  simp (config := {decide := true}) only [intFold_succ, intFold_done, revOut, revIn, Int.reduceAdd, Int.reduceSub,
    Int.reduceMul]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_ofNat, revContainersNat_testBit 2 (by decide)]
  simp only [Sail.BitVec.updateSubrange, Int.reduceToNat]
  simp (disch := omega) only [getLsbD_updateSubrange', BitVec.getLsbD_setWidth, Sail.BitVec.extractLsb,
    BitVec.getLsbD_extractLsb, if_pos, if_neg, BitVec.getLsbD_zero]
  have : x.toNat.testBit = x.getLsbD := rfl
  rw [this]
  repeat' split
  all_goals
    congr 1
    · rw [decide_eq_decide]; omega
    congr 1
    · rw [decide_eq_decide]; omega
    congr 1; omega

set_option maxHeartbeats 40000000 in
theorem rev_val_32_64 (x : BitVec 64) : (intFold (revOut x 4) 0 1 (0, 0#64, 0)).2.1 =
    BitVec.ofNat 64 (Janus.Arm64.revContainersNat 4 2 x.toNat) := by
  simp (config := {decide := true}) only [intFold_succ, intFold_done, revOut, revIn, Int.reduceAdd, Int.reduceSub,
    Int.reduceMul]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_ofNat, revContainersNat_testBit 4 (by decide)]
  simp only [Sail.BitVec.updateSubrange, Int.reduceToNat]
  simp (disch := omega) only [getLsbD_updateSubrange', BitVec.getLsbD_setWidth, Sail.BitVec.extractLsb,
    BitVec.getLsbD_extractLsb, if_pos, if_neg, BitVec.getLsbD_zero]
  have : x.toNat.testBit = x.getLsbD := rfl
  rw [this]
  repeat' split
  all_goals
    congr 1
    · rw [decide_eq_decide]; omega
    congr 1
    · rw [decide_eq_decide]; omega
    congr 1; omega

set_option maxHeartbeats 40000000 in
theorem rev_val_64_64 (x : BitVec 64) : (intFold (revOut x 8) 0 0 (0, 0#64, 0)).2.1 =
    BitVec.ofNat 64 (Janus.Arm64.revContainersNat 8 1 x.toNat) := by
  simp (config := {decide := true}) only [intFold_succ, intFold_done, revOut, revIn, Int.reduceAdd, Int.reduceSub,
    Int.reduceMul]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_ofNat, revContainersNat_testBit 8 (by decide)]
  simp only [Sail.BitVec.updateSubrange, Int.reduceToNat]
  simp (disch := omega) only [getLsbD_updateSubrange', BitVec.getLsbD_setWidth, Sail.BitVec.extractLsb,
    BitVec.getLsbD_extractLsb, if_pos, if_neg, BitVec.getLsbD_zero]
  have : x.toNat.testBit = x.getLsbD := rfl
  rw [this]
  repeat' split
  all_goals
    congr 1
    · rw [decide_eq_decide]; omega
    congr 1
    · rw [decide_eq_decide]; omega
    congr 1; omega

set_option maxHeartbeats 8000000 in
theorem run_execute_rev_rel {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N opc : Nat}
    (hc : (opc = 1 ∧ N = 32) ∨ (opc = 2 ∧ N = 32) ∨ (opc = 1 ∧ N = 64) ∨ (opc = 2 ∧ N = 64) ∨ (opc = 3 ∧ N = 64))
    {d n : Nat} (hd : d < 32) (hn : n < 32) :
    ∃ s', (execute_aarch64_instrs_integer_arithmetic_rev (8 * 2 ^ opc) d N n).run s = .ok () s' ∧
      Rel (Janus.Arm64.execRev N js opc n d) s' ∧ Frame s s' := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e1 : (((16 : Nat) : Int) / 8) = 2 := rfl
    have e2 : (((32 : Nat) : Int) / ((16 : Nat) : Int) - 1) = 1 := rfl
    rw [show 8 * 2 ^ 1 = 16 from rfl, run_execute_rev h (by decide) hn, e1, e2, rev_val_16_32]
    obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd (by decide) (BitVec.ofNat 32 (Janus.Arm64.revContainersNat 2 2 (js.getX 32 n).toNat))
    exact ⟨s', hs', by simpa [Janus.Arm64.execRev] using hr, hf⟩
  · have e1 : (((32 : Nat) : Int) / 8) = 4 := rfl
    have e2 : (((32 : Nat) : Int) / ((32 : Nat) : Int) - 1) = 0 := rfl
    rw [show 8 * 2 ^ 2 = 32 from rfl, run_execute_rev h (by decide) hn, e1, e2, rev_val_32_32]
    obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd (by decide) (BitVec.ofNat 32 (Janus.Arm64.revContainersNat 4 1 (js.getX 32 n).toNat))
    exact ⟨s', hs', by simpa [Janus.Arm64.execRev] using hr, hf⟩
  · have e1 : (((16 : Nat) : Int) / 8) = 2 := rfl
    have e2 : (((64 : Nat) : Int) / ((16 : Nat) : Int) - 1) = 3 := rfl
    rw [show 8 * 2 ^ 1 = 16 from rfl, run_execute_rev h (by decide) hn, e1, e2, rev_val_16_64]
    obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd (by decide) (BitVec.ofNat 64 (Janus.Arm64.revContainersNat 2 4 (js.getX 64 n).toNat))
    exact ⟨s', hs', by simpa [Janus.Arm64.execRev] using hr, hf⟩
  · have e1 : (((32 : Nat) : Int) / 8) = 4 := rfl
    have e2 : (((64 : Nat) : Int) / ((32 : Nat) : Int) - 1) = 1 := rfl
    rw [show 8 * 2 ^ 2 = 32 from rfl, run_execute_rev h (by decide) hn, e1, e2, rev_val_32_64]
    obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd (by decide) (BitVec.ofNat 64 (Janus.Arm64.revContainersNat 4 2 (js.getX 64 n).toNat))
    exact ⟨s', hs', by simpa [Janus.Arm64.execRev] using hr, hf⟩
  · have e1 : (((64 : Nat) : Int) / 8) = 8 := rfl
    have e2 : (((64 : Nat) : Int) / ((64 : Nat) : Int) - 1) = 0 := rfl
    rw [show 8 * 2 ^ 3 = 64 from rfl, run_execute_rev h (by decide) hn, e1, e2, rev_val_64_64]
    obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd (by decide) (BitVec.ofNat 64 (Janus.Arm64.revContainersNat 8 1 (js.getX 64 n).toNat))
    exact ⟨s', hs', by simpa [Janus.Arm64.execRev] using hr, hf⟩

theorem run_decode_rev16 (Rd Rn : BitVec 5) (sf : BitVec 1) (s : SState) :
    (decode_rev16_int_aarch64_instrs_integer_arithmetic_rev Rd Rn 1#2 sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_rev (8 * 2 ^ 1) Rd.toNat (if sf == 1#1 then 64 else 32) Rn.toNat).run s := rfl

theorem run_decode_rev32 (Rd Rn : BitVec 5) (sf : BitVec 1) (s : SState) :
    (decode_rev_aarch64_instrs_integer_arithmetic_rev Rd Rn 2#2 sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_rev (8 * 2 ^ 2) Rd.toNat (if sf == 1#1 then 64 else 32) Rn.toNat).run s := rfl

theorem run_decode_rev64 (Rd Rn : BitVec 5) (s : SState) :
    (decode_rev_aarch64_instrs_integer_arithmetic_rev Rd Rn 3#2 1#1).run s =
      (execute_aarch64_instrs_integer_arithmetic_rev (8 * 2 ^ 3) Rd.toNat 64 Rn.toNat).run s := by
  unfold decode_rev_aarch64_instrs_integer_arithmetic_rev
  simp only [run_bind, run_pure]
  rfl
set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 737 (`decode_rev16_int_aarch64_instrs_integer_arithmetic_rev`). -/
theorem run_DataProcReg_dp1_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 1024 = 726) (h1 : (w / 2 ^ 16) % 32 = 0) (h2 : (w / 2 ^ 10) % 64 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_rev16_int_aarch64_instrs_integer_arithmetic_rev (fld w 0 5) (fld w 5 5) (fld w 10 2) (fld w 31 1)).run (s.set .SEE 737) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f33 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486853#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486852#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486855#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f39 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f40 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f41 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f42 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486854#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f43 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f44 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f45 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f46 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f47 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f48 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f49 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f50 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f51 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f52 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486848#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f53 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 11 == (743425#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t54_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486849#21 : BitVec 21)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, t54_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 737) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 736 (`decode_rev_aarch64_instrs_integer_arithmetic_rev`). -/
theorem run_DataProcReg_dp1_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 1024 = 726) (h1 : (w / 2 ^ 16) % 32 = 0) (h2 : (w / 2 ^ 10) % 64 = 2) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_rev_aarch64_instrs_integer_arithmetic_rev (fld w 0 5) (fld w 5 5) (fld w 10 2) (fld w 31 1)).run (s.set .SEE 736) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f33 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486853#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486852#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486855#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f39 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f40 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f41 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f42 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486854#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f43 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f44 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f45 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f46 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f47 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f48 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f49 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f50 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f51 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f52 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486848#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t53_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 11 == (743425#20 : BitVec 20)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, t53_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 736) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 736 (`decode_rev_aarch64_instrs_integer_arithmetic_rev`). -/
theorem run_DataProcReg_dp1_3 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 1024 = 726) (h1 : (w / 2 ^ 16) % 32 = 0) (h2 : (w / 2 ^ 10) % 64 = 3) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_rev_aarch64_instrs_integer_arithmetic_rev (fld w 0 5) (fld w 5 5) (fld w 10 2) (fld w 31 1)).run (s.set .SEE 736) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f33 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486853#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486852#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486855#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f39 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f40 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f41 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f42 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486854#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f43 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f44 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f45 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f46 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f47 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f48 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f49 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f50 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f51 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f52 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486848#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t53_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 11 == (743425#20 : BitVec 20)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, t53_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 736) = True from by decide]
  all_goals rfl


theorem decode_rev1_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 1) :
    Janus.Arm64.decode w = some (.rev (Janus.Arm64.bit w 31) 1 (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (Janus.Arm64.bits w 28 25 % 2 = 0 && Janus.Arm64.bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : Janus.Arm64.bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : Janus.Arm64.bit w 28 = true := by simp only [bit_def]; simp; omega
  have a7 : Janus.Arm64.bits w 24 21 = 0b0110 := by simp only [bits_def]; omega
  have a8 : Janus.Arm64.bit w 29 = false := by simp only [bit_def]; simp; omega
  have a9 : Janus.Arm64.bit w 30 = true := by simp only [bit_def]; simp; omega
  have a10 : ¬ Janus.Arm64.bits w 20 16 ≠ 0 := by simp only [bits_def]; omega
  have a11 : Janus.Arm64.bits w 15 10 = 1 := by simp only [bits_def]; omega
  simp only [Janus.Arm64.decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true,
    Janus.Arm64.decodeDPReg, a6, a7, a8, a9, a10, a11, Bool.not_true, Bool.not_false]
  all_goals simp

theorem decode_rev2_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 2) :
    Janus.Arm64.decode w = some (.rev (Janus.Arm64.bit w 31) 2 (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (Janus.Arm64.bits w 28 25 % 2 = 0 && Janus.Arm64.bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : Janus.Arm64.bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : Janus.Arm64.bit w 28 = true := by simp only [bit_def]; simp; omega
  have a7 : Janus.Arm64.bits w 24 21 = 0b0110 := by simp only [bits_def]; omega
  have a8 : Janus.Arm64.bit w 29 = false := by simp only [bit_def]; simp; omega
  have a9 : Janus.Arm64.bit w 30 = true := by simp only [bit_def]; simp; omega
  have a10 : ¬ Janus.Arm64.bits w 20 16 ≠ 0 := by simp only [bits_def]; omega
  have a11 : Janus.Arm64.bits w 15 10 = 2 := by simp only [bits_def]; omega
  simp only [Janus.Arm64.decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true,
    Janus.Arm64.decodeDPReg, a6, a7, a8, a9, a10, a11, Bool.not_true, Bool.not_false]
  all_goals simp

theorem decode_rev3_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 3) (hsf : (w / 2 ^ 31) % 2 = 1) :
    Janus.Arm64.decode w = some (.rev (Janus.Arm64.bit w 31) 3 (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (Janus.Arm64.bits w 28 25 % 2 = 0 && Janus.Arm64.bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : Janus.Arm64.bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : Janus.Arm64.bit w 28 = true := by simp only [bit_def]; simp; omega
  have a7 : Janus.Arm64.bits w 24 21 = 0b0110 := by simp only [bits_def]; omega
  have a8 : Janus.Arm64.bit w 29 = false := by simp only [bit_def]; simp; omega
  have a9 : Janus.Arm64.bit w 30 = true := by simp only [bit_def]; simp; omega
  have a10 : ¬ Janus.Arm64.bits w 20 16 ≠ 0 := by simp only [bits_def]; omega
  have a11 : Janus.Arm64.bits w 15 10 = 3 := by simp only [bits_def]; omega
  have a12 : Janus.Arm64.bit w 31 = true := by simp only [bit_def]; simp; omega
  simp only [Janus.Arm64.decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true,
    Janus.Arm64.decodeDPReg, a6, a7, a8, a9, a10, a11, Bool.not_true, Bool.not_false, a12]
  all_goals simp

set_option maxHeartbeats 8000000 in
theorem asl_rev16 {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 1)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execRev (if fld w 31 1 == 1#1 then 64 else 32) js 1 (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2) := by
  have e10 : fld w 10 2 = 1#2 := BitVec.eq_of_toNat_eq (by rw [fld_toNat w 10 2 hw]; simp; omega)
  rw [run_DecodeA64_DPReg hw (by omega), run_DataProcReg_dp1_1 hw h1 h2 h3 (see_entry _ _), e10, run_decode_rev16]
  obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_rev_rel (h.entry (BitVec.ofNat 32 w) 737)
    (N := if fld w 31 1 == 1#1 then 64 else 32) (opc := 1) (by split <;> simp)
    (fld_lt w 0 5) (fld_lt w 5 5)
  exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩

theorem rev16_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 1)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') := by
  let F : Nat → Janus.Arm64.State := fun N => Janus.Arm64.execRev N js 1 (fld w 5 5).toNat (fld w 0 5).toNat
  have hspec : ∀ N, (F N).pc = js.pc := by
    intro N; simp [F, Janus.Arm64.execRev, Janus.Arm64.State.setX, Janus.Arm64.State.writeZR]; split <;> rfl
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_rev16 hw h1 h2 h3 h (js.pc.toNat : Int)
  have e : F (if fld w 31 1 == 1#1 then 64 else 32) = if fld w 31 1 == 1#1 then F 64 else F 32 := by
    split <;> rfl
  have hrel' : Rel (if fld w 31 1 == 1#1 then F 64 else F 32) s2 := e ▸ hrel
  refine step_agree h ⟨s2, hrun, hrel', hbt⟩ (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_rev1_class hw h1 h2 h3)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  split <;> simp_all [Janus.Arm64.State.next, F]

set_option maxHeartbeats 8000000 in
theorem asl_rev32 {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 2)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execRev (if fld w 31 1 == 1#1 then 64 else 32) js 2 (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2) := by
  have e10 : fld w 10 2 = 2#2 := BitVec.eq_of_toNat_eq (by rw [fld_toNat w 10 2 hw]; simp; omega)
  rw [run_DecodeA64_DPReg hw (by omega), run_DataProcReg_dp1_2 hw h1 h2 h3 (see_entry _ _), e10, run_decode_rev32]
  obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_rev_rel (h.entry (BitVec.ofNat 32 w) 736)
    (N := if fld w 31 1 == 1#1 then 64 else 32) (opc := 2) (by split <;> simp)
    (fld_lt w 0 5) (fld_lt w 5 5)
  exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩

theorem rev32_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 2)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') := by
  let F : Nat → Janus.Arm64.State := fun N => Janus.Arm64.execRev N js 2 (fld w 5 5).toNat (fld w 0 5).toNat
  have hspec : ∀ N, (F N).pc = js.pc := by
    intro N; simp [F, Janus.Arm64.execRev, Janus.Arm64.State.setX, Janus.Arm64.State.writeZR]; split <;> rfl
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_rev32 hw h1 h2 h3 h (js.pc.toNat : Int)
  have e : F (if fld w 31 1 == 1#1 then 64 else 32) = if fld w 31 1 == 1#1 then F 64 else F 32 := by
    split <;> rfl
  have hrel' : Rel (if fld w 31 1 == 1#1 then F 64 else F 32) s2 := e ▸ hrel
  refine step_agree h ⟨s2, hrun, hrel', hbt⟩ (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_rev2_class hw h1 h2 h3)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  split <;> simp_all [Janus.Arm64.State.next, F]

set_option maxHeartbeats 8000000 in
theorem asl_rev64 {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 3) (hsf : (w / 2 ^ 31) % 2 = 1)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execRev 64 js 3 (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2) := by
  have e31 : fld w 31 1 = 1#1 := BitVec.eq_of_toNat_eq (by rw [fld_toNat w 31 1 hw]; simpa using hsf)
  have e10 : fld w 10 2 = 3#2 := BitVec.eq_of_toNat_eq (by rw [fld_toNat w 10 2 hw]; simp; omega)
  rw [run_DecodeA64_DPReg hw (by omega), run_DataProcReg_dp1_3 hw h1 h2 h3 (see_entry _ _), e10, e31, run_decode_rev64]
  obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_rev_rel (h.entry (BitVec.ofNat 32 w) 736) (N := 64) (opc := 3) (by decide)
    (fld_lt w 0 5) (fld_lt w 5 5)
  exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩

theorem rev64_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110)
    (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 3) (hsf : (w / 2 ^ 31) % 2 = 1)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') := by
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_rev64 hw h1 h2 h3 hsf h (js.pc.toNat : Int)
  have hpc : (Janus.Arm64.execRev 64 js 3 (fld w 5 5).toNat (fld w 0 5).toNat).pc = js.pc := by
    simp [Janus.Arm64.execRev, Janus.Arm64.State.setX, Janus.Arm64.State.writeZR]; split <;> rfl
  refine step_agree h ⟨s2, hrun, hrel, hbt⟩ hpc ?_
  rw [Janus.Arm64.step_of_decode (decode_rev3_class hw h1 h2 h3 hsf)]
  have hb : Janus.Arm64.bit w 31 = true := by simp only [bit_def]; simp; omega
  simp only [Janus.Arm64.exec, hb, ite_true, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  simp [Janus.Arm64.State.next, hpc]

end JanusASL.Proofs
