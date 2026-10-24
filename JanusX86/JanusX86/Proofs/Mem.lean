import JanusX86.Proofs.Loop

/-! # Memory reads and writes of the generated model

With the application-level view (`app_view`), a linear address is the physical address, and
`rb`/`wb` read and write the bytes one at a time through `memi`/`bang_memi`, i.e. lean-sail's
byte map (`JanusX86Extras.lean`'s `read_mem`/`write_mem`). -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- `Σ_{j < n} f j * 256^j`: the little-endian value of the bytes `f 0, …, f (n-1)`. -/
def sumLE (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumLE f n + f n * 256 ^ n

theorem sumLE_lt (f : Nat → Nat) (hf : ∀ j, f j < 256) : ∀ n, sumLE f n < 256 ^ n
  | 0 => by simp [sumLE]
  | n + 1 => by
    have h1 := sumLE_lt f hf n
    have h2 := hf n
    simp only [sumLE, Nat.pow_succ]
    have : f n * 256 ^ n ≤ 255 * 256 ^ n := Nat.mul_le_mul_right _ (by omega)
    omega

theorem run_canonical_address_p (x : Int) (s : SState) :
    (canonical_address_p x).run s = .ok (decide (-(2 ^ 47 : Int) ≤ x ∧ x < 2 ^ 47)) s := by
  simp only [canonical_address_p, signed_byte_p_int, run_bind, run_sail_assert_of (show
    (decide ((48 : Int) ≥ 0)) = true by decide), run_pure]
  congr 1
  simp only [Bool.decide_and]
  rfl

theorem run_log_memory_read {s : SState} {r : BitVec 64} (hr : s.regs.get? .rip = some r)
    {w : Nat} (a : BitVec w) (len : Nat) (v : BitVec (8 * len)) :
    (log_memory_read a len v).run s = .ok () s := by
  simp only [log_memory_read, read_rip, run_bind, run_readReg hr, run_pure]

theorem run_memi {s : SState} {r : BitVec 64} (hr : s.regs.get? .rip = some r) {w : Nat}
    (a : BitVec w) (hw : w ≤ 64) {b : BitVec 8} (hb : s.mem[a.toNat]? = some b) :
    (memi a).run s = .ok b s := by
  have hm : (sail_mask 64 a).toNat = a.toNat := by
    simp only [sail_mask, Sail.BitVec.length, Sail.BitVec.truncate, Sail.BitVec.zeroExtend]
    split
    · next h => simp at h; have : w = 64 := by omega
                subst this; simp
    · simp; exact Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) hw)
  simp only [memi, read_mem, run_bind, hm]
  have hr1 : (Sail.ConcurrencyInterfaceV1.PreSail.readBytes 1 a.toNat : SailM _).run s = .ok (b, none) s := by
    simp [Sail.ConcurrencyInterfaceV1.PreSail.readBytes, Sail.ConcurrencyInterfaceV1.PreSail.readByte,
      EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hb, pure, EStateM.pure]
  rw [hr1]
  simp only [run_pure, run_log_memory_read hr]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem updateSubrange'_toNat {w : Nat} (x : BitVec w) (lo len : Nat) (y : BitVec len)
    (hx : x.toNat < 2 ^ lo) (hfit : lo + len ≤ w) :
    (Sail.BitVec.updateSubrange' x lo len y).toNat = x.toNat + y.toNat * 2 ^ lo := by
  have hmask : (~~~((BitVec.allOnes len).zeroExtend w <<< lo) &&& x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, hk, decide_true, Bool.true_and]
    by_cases hkl : k < lo
    · simp [hkl]
    · have : x.getLsbD k = false := by
        simp only [BitVec.getLsbD, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx
          (Nat.pow_le_pow_right (by decide) (by omega : lo ≤ k)))]
      simp [this]
  have hy : (y.zeroExtend w <<< lo).toNat = y.toNat * 2 ^ lo := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    have h1 : y.toNat < 2 ^ w := Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.mod_eq_of_lt h1]
    apply Nat.mod_eq_of_lt
    calc y.toNat * 2 ^ lo < 2 ^ len * 2 ^ lo := Nat.mul_lt_mul_of_pos_right y.isLt (Nat.two_pow_pos _)
      _ = 2 ^ (len + lo) := by rw [Nat.pow_add]
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [Sail.BitVec.updateSubrange', hmask, BitVec.toNat_or, hy]
  rw [show y.toNat * 2 ^ lo = 2 ^ lo * y.toNat from Nat.mul_comm _ _, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt hx]
  omega

theorem toInt_of_lt {w : Nat} (x : BitVec w) (h : 2 * x.toNat < 2 ^ w) : x.toInt = x.toNat := by
  simp [BitVec.toInt, h]

theorem phys_toNat (addr : BitVec 64) (j : Nat) (h : addr.toNat + j < 2 ^ 47) :
    (sail_mask_signed 52 (Sail.BitVec.addInt (sail_mask_signed 48 addr) (j : Int))).toNat =
      addr.toNat + j := by
  have e48 : (Sail.BitVec.addInt (sail_mask_signed 48 addr) (j : Int)).toNat = addr.toNat + j := by
    simp only [sail_mask_signed, Sail.BitVec.length, Sail.BitVec.addInt, Sail.BitVec.truncate,
      show decide (48 ≤ 64) = true from rfl, ite_true, BitVec.toNat_add, BitVec.toNat_setWidth,
      BitVec.toNat_ofInt]
    have h1 : addr.toNat % 2 ^ 48 = addr.toNat := Nat.mod_eq_of_lt (by omega)
    have h2 : ((j : Int) % ((2 ^ 48 : Nat) : Int)).toNat = j := by omega
    rw [h1, h2]; exact Nat.mod_eq_of_lt (by omega)
  have hmsb : (Sail.BitVec.addInt (sail_mask_signed 48 addr) (j : Int)).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, e48]; omega
  have : sail_mask_signed 52 (Sail.BitVec.addInt (sail_mask_signed 48 addr) (j : Int)) =
      (Sail.BitVec.addInt (sail_mask_signed 48 addr) (j : Int)).signExtend 52 := by
    simp only [sail_mask_signed, Sail.BitVec.length, show decide (52 ≤ 48) = false from rfl,
      Bool.false_eq_true, ite_false, Sail.BitVec.signExtend]
  rw [this, BitVec.signExtend_eq_setWidth_of_msb_false hmsb, BitVec.toNat_setWidth, e48]
  exact Nat.mod_eq_of_lt (by omega)

theorem run_rb {s : SState} (happ : s.regs.get? .app_view = some true) {r : BitVec 64}
    (hr : s.regs.get? .rip = some r) {n : Nat} (hn : 0 < n) (addr : BitVec 64)
    (ha : addr.toNat + n ≤ 2 ^ 47) (f : Nat → BitVec 8)
    (hm : ∀ j < n, s.mem[addr.toNat + j]? = some (f j)) (k : String) :
    (rb n addr k).run s = .ok (BitVec.ofNat (8 * n) (sumLE (fun j => (f j).toNat) n)) s := by
  simp only [rb]
  refine run_forIn_bind 0 ((n : Int) - 1) _ _ _ _
    (fun (i : Int) (b : BitVec (8 * (n : Int)).toNat) (σ : SState) => σ = s ∧ (0 ≤ i ∧ i ≤ n ∧
      b.toNat = sumLE (fun j => (f j).toNat) i.toNat)) s _ (by omega) ⟨rfl, by simp [sumLE]⟩ ?_ ?_
  · intro i b σ hi1 hi2 ⟨hσ, _, _, hb⟩
    subst hσ
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi1
    have hj : j < n := by omega
    have hint : addr.toInt = addr.toNat := toInt_of_lt addr (by omega)
    have hc : decide (-(2 ^ 47 : Int) ≤ addr.toInt + (j : Int) ∧ addr.toInt + (j : Int) < 2 ^ 47) = true := by
      simp only [hint, decide_eq_true_eq]; omega
    have hmem : σ.mem[(sail_mask_signed 52 (Sail.BitVec.addInt (sail_mask_signed 48 addr) (j : Int))).toNat]? =
        some (f j) := by rw [phys_toNat addr j (by omega)]; exact hm j hj
    simp only [run_bind, run_canonical_address_p, hc, Bool.not_true, Bool.false_eq_true, ite_false, run_pure,
      run_readReg happ, ite_true, run_memi hr _ (by decide) hmem]
    refine ⟨_, σ, rfl, rfl, by omega, by omega, ?_⟩
    have hlo : (8 * (j : Int)).toNat = 8 * j := by omega
    have hlen : (8 * (j : Int) + 7).toNat - (8 * (j : Int)).toNat + 1 = 8 := by omega
    have hblt : b.toNat < 2 ^ (8 * (j : Int)).toNat := by
      rw [hb, hlo, Nat.pow_mul]
      exact sumLE_lt _ (fun j => (f j).isLt) _
    simp only [Sail.BitVec.updateSubrange]
    rw [updateSubrange'_toNat _ _ _ _ hblt (by omega), hb, BitVec.toNat_setWidth, hlen, hlo]
    have e1 : ((j : Int) + 1).toNat = j + 1 := by omega
    have e2 : ((j : Int)).toNat = j := by omega
    rw [e1, e2, Nat.mod_eq_of_lt (f j).isLt, sumLE, Nat.pow_mul]
  · intro b σ ⟨hσ, h2⟩
    subst hσ
    show EStateM.Result.ok b σ = EStateM.Result.ok _ σ
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [h2.2.2]
    rw [show ∀ x, (@BitVec.toNat ((8 * (n : Int)).toNat) (BitVec.ofNat (8 * n) x)) = x % 2 ^ (8 * n) from
      fun x => rfl]
    have e : ((n : Int) - 1 + 1).toNat = n := by omega
    rw [e, Nat.mod_eq_of_lt]
    have := sumLE_lt (fun j => (f j).toNat) (fun j => (f j).isLt) n
    rwa [show (256 : Nat) ^ n = 2 ^ (8 * n) by rw [Nat.pow_mul]] at this

end JanusX86.Proofs
