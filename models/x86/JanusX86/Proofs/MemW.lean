import JanusX86.Proofs.Top

/-! # Memory writes of the model (`wb`), and Janus' store against them -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_log_memory_write {s : SState} {r : BitVec 64} (hr : s.regs.get? .rip = some r)
    {w : Nat} (a : BitVec w) (len : Nat) (v : BitVec (8 * len)) :
    (log_memory_write a len v).run s = .ok () s := by
  simp only [log_memory_write, read_rip, run_bind, run_readReg hr, run_pure]

theorem run_bang_memi {s : SState} {r : BitVec 64} (hr : s.regs.get? .rip = some r) {w : Nat}
    (a : BitVec w) (hw : w ≤ 64) (b : BitVec 8) :
    (bang_memi a b).run s = .ok () { s with mem := s.mem.insert a.toNat b } := by
  have hm : (sail_mask 64 a).toNat = a.toNat := by
    simp only [sail_mask, Sail.BitVec.length, Sail.BitVec.truncate, Sail.BitVec.zeroExtend]
    split
    · next h => simp at h; have : w = 64 := by omega
                subst this; simp
    · simp; exact Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) hw)
  simp only [bang_memi, write_mem_ea, write_mem, run_bind, run_pure, hm]
  have hw1 : (Sail.ConcurrencyInterfaceV1.PreSail.writeBytes (n := 1) a.toNat b : SailM Bool).run s =
      .ok true { s with mem := s.mem.insert a.toNat b } := by
    simp [Sail.ConcurrencyInterfaceV1.PreSail.writeBytes, Sail.ConcurrencyInterfaceV1.PreSail.writeByte,
      EStateM.run, bind, EStateM.bind, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, pure,
      EStateM.pure, List.ofFn, List.forM, Fin.foldr, Fin.foldr.loop]
  rw [hw1]
  exact run_log_memory_write (s := { s with mem := s.mem.insert a.toNat b }) hr a 1 b

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- The memory after writing the low `n` bytes of `v` at `a` (little-endian). -/
def WroteLE (m m' : Std.ExtHashMap Nat (BitVec 8)) (a n v : Nat) : Prop :=
  ∀ j, m'[j]? = if a ≤ j ∧ j < a + n then some (BitVec.ofNat 8 (v / 256 ^ (j - a))) else m[j]?

theorem extract_byte {n : Nat} (v : BitVec (8 * n)) (o : Nat) (ho : o < n) :
    BitVec.setWidth 8 (Sail.BitVec.extractLsb v (8 * (o : Int) + 7).toNat (8 * (o : Int)).toNat) =
      BitVec.ofNat 8 (v.toNat / 256 ^ o) := by
  apply BitVec.eq_of_toNat_eq
  have e1 : (8 * (o : Int) + 7).toNat = 8 * o + 7 := by omega
  have e2 : (8 * (o : Int)).toNat = 8 * o := by omega
  simp only [Sail.BitVec.extractLsb, BitVec.toNat_setWidth, BitVec.extractLsb_toNat, e1, e2, BitVec.toNat_ofNat]
  rw [show 8 * o + 7 - 8 * o + 1 = 8 by omega, Nat.shiftRight_eq_div_pow, Nat.pow_mul]
  simp

theorem run_wb {s : SState} (happ : s.regs.get? .app_view = some true) {r : BitVec 64}
    (hr : s.regs.get? .rip = some r) {n : Nat} (hn : 0 < n) (addr : BitVec 64) (ha : addr.toNat + n ≤ 2 ^ 47)
    (v : BitVec (8 * n)) (k : String) :
    ∃ s', (wb n addr k v).run s = .ok () s' ∧ s'.regs = s.regs ∧ WroteLE s.mem s'.mem addr.toNat n v.toNat := by
  simp only [wb]
  refine run_forIn_bind_ex 0 ((n : Int) - 1) _ _ _ _
    (fun (i : Int) (_ : Unit) (σ : SState) => σ.regs = s.regs ∧ (0 ≤ i ∧ i ≤ n ∧
      WroteLE s.mem σ.mem addr.toNat i.toNat v.toNat)) s
    (fun R => ∃ s', R = .ok () s' ∧ s'.regs = s.regs ∧ WroteLE s.mem s'.mem addr.toNat n v.toNat)
    (by omega) ⟨rfl, by omega, by omega, ?_⟩ ?_ ?_
  · intro j; simp; intro h1 h2; omega
  · intro i b σ hi1 hi2 ⟨hreg, _, _, hw⟩
    obtain ⟨o, rfl⟩ := Int.eq_ofNat_of_zero_le hi1
    have ho : o < n := by omega
    have happ' : σ.regs.get? .app_view = some true := by rw [hreg]; exact happ
    have hr' : σ.regs.get? .rip = some r := by rw [hreg]; exact hr
    have hint : addr.toInt = addr.toNat := toInt_of_lt addr (by omega)
    have hc : decide (-(2 ^ 47 : Int) ≤ addr.toInt + (o : Int) ∧ addr.toInt + (o : Int) < 2 ^ 47) = true := by
      simp only [hint, decide_eq_true_eq]; omega
    simp only [run_bind, run_canonical_address_p, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, run_pure,
      run_readReg happ', run_bang_memi (w := 52) hr' _ (by decide), extract_byte v o ho]
    refine ⟨_, _, rfl, hreg, by omega, by omega, ?_⟩
    intro j
    simp only [Std.ExtHashMap.getElem?_insert, phys_toNat addr o (by omega), beq_iff_eq]
    rw [hw j]
    have e : ((o : Int) + 1).toNat = o + 1 := by omega
    rw [e]
    by_cases hj : addr.toNat + o = j
    · subst hj; simp
    · simp only [hj, ↓reduceIte]
      split <;> split <;> first | rfl | omega
  · intro b σ ⟨hreg, _, _, hw⟩
    refine ⟨σ, rfl, hreg, ?_⟩
    have : ((n : Int) - 1 + 1).toNat = n := by omega
    rw [this] at hw; exact hw

end JanusX86.Proofs
