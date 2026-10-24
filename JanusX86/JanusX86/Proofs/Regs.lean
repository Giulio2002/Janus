import JanusX86.Proofs.Rel

/-! # Sized GPR reads and writes: `rgfi_size`/`write_rgfi_size` against Janus' `readLoc`/`writeLoc`

The model reads an `n`-byte register operand with `rgfi_size` (`rr08` picks `AH`..`BH`, bits
15:8 of registers 0..3, for numbers 4..7 when there is no REX prefix) and writes it with
`write_rgfi_size` (8- and 16-bit writes merge, 32-bit writes zero-extend). -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_rgfi {s : SState} {n : Nat} (hn : n < 16) {v : BitVec 64} (h : gprVal s n = some v) :
    (rgfi (n : Int)).run s = .ok v s := by
  have ha : (decide (0 ≤ (n : Int)) && decide ((n : Int) < 16)) = true := by simp; omega
  simp only [rgfi, run_bind, run_sail_assert_of ha, Int.toNat_natCast, run_read_gpr hn h, run_pure, regval_from_reg]

theorem run_write_rgfi {s : SState} (hl : s.regs.get? .log_register_writes = some false) {n : Nat}
    (hn : n < 16) (v : BitVec 64) : (write_rgfi (n : Int) v).run s = .ok () (setGpr s v n) := by
  have ha : (decide (0 ≤ (n : Int)) && decide ((n : Int) < 16)) = true := by simp; omega
  simp only [write_rgfi, run_bind, run_sail_assert_of ha, Int.toNat_natCast, regval_into_reg,
    run_write_gpr hl hn]

theorem toNatInt_ofNat4 (n : Nat) (hn : n < 16) : Sail.BitVec.toNatInt (BitVec.ofNat 4 n) = (n : Int) := by
  simp [Sail.BitVec.toNatInt, Nat.mod_eq_of_lt hn]

/-- The 8-bit register number `n` with REX byte `rex`: `rr08`'s choice. -/
def low8 (rex : BitVec 8) (n : Nat) : Bool := !(rex == 0#8) || decide (n < 4)

theorem run_rr08_low {s : SState} {n : Nat} (hn : n < 16) {v : BitVec 64} (h : gprVal s n = some v)
    (rex : BitVec 8) (hl : low8 rex n = true) :
    (rr08 (BitVec.ofNat 4 n) rex).run s = .ok (v.setWidth 8) s := by
  simp only [low8] at hl
  simp only [rr08, toNatInt_ofNat4 n hn, Int.toNat_natCast, hl, ↓reduceIte, run_bind, run_rgfi hn h, run_pure,
    Sail.BitVec.truncate, BitVec.truncate_eq_setWidth]

theorem run_rr08_high {s : SState} {n : Nat} (hn4 : 4 ≤ n) (hn : n < 8) {v : BitVec 64}
    (h : gprVal s (n - 4) = some v) :
    (rr08 (BitVec.ofNat 4 n) 0#8).run s = .ok (v.extractLsb' 8 8) s := by
  have hl : (!(0#8 == 0#8) || decide (n < 4)) = false := by simp; omega
  have hb : Sail.BitVec.toNatInt (bits_of_int ((n : Int) - 4) 4) = ((n - 4 : Nat) : Int) := by
    rw [show (n : Int) - 4 = ((n - 4 : Nat) : Int) by omega]
    simp only [Sail.BitVec.toNatInt, bits_of_int_natCast_toNat, Int.ofNat_eq_natCast]; omega
  simp only [rr08, toNatInt_ofNat4 n (by omega), Int.toNat_natCast, hl, Bool.false_eq_true, ↓reduceIte, run_bind,
    hb, run_rgfi (by omega : n - 4 < 16) h, run_pure, Sail.BitVec.extractLsb]
  rfl

theorem run_rr16 {s : SState} {n : Nat} (hn : n < 16) {v : BitVec 64} (h : gprVal s n = some v) :
    (rr16 (BitVec.ofNat 4 n)).run s = .ok (v.setWidth 16) s := by
  simp only [rr16, toNatInt_ofNat4 n hn, run_bind, run_rgfi hn h, run_pure, Sail.BitVec.truncate,
    BitVec.truncate_eq_setWidth]

theorem run_rr32 {s : SState} {n : Nat} (hn : n < 16) {v : BitVec 64} (h : gprVal s n = some v) :
    (rr32 (BitVec.ofNat 4 n)).run s = .ok (v.setWidth 32) s := by
  simp only [rr32, toNatInt_ofNat4 n hn, run_bind, run_rgfi hn h, run_pure, Sail.BitVec.truncate,
    BitVec.truncate_eq_setWidth]

theorem run_rr64 {s : SState} {n : Nat} (hn : n < 16) {v : BitVec 64} (h : gprVal s n = some v) :
    (rr64 (BitVec.ofNat 4 n)).run s = .ok v s := by
  simp only [rr64, toNatInt_ofNat4 n hn, run_rgfi hn h]

/-- Janus' value of a register location at width `w` (`readLoc` on `.reg`/`.high`). -/
def regVal (js : Janus.Amd64.State) (w : Nat) : Janus.Amd64.Loc → BitVec w
  | .reg r => js.getReg w r
  | .high r => (js.getHigh r).setWidth w
  | .mem _ => 0

/-- The register location of number `n` at width `w` (Janus' `rmLoc`/`regLoc` on a register). -/
def regLocOf (rexP : Bool) (w n : Nat) : Janus.Amd64.Loc :=
  if w = 8 then Janus.Amd64.Decode.reg8 rexP n else .reg n

theorem nbytes_eq (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) :
    bits_of_int ((w / 8 : Nat) : Int) 4 = BitVec.ofNat 4 (w / 8) := by
  apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp

theorem run_rgfi_size {js : Janus.Amd64.State} {s : SState} (h : Rel js s) {w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (rexP : Bool) (rex : BitVec 8) (hrex : (rex == 0#8) = !rexP)
    {n : Nat} (hn : n < 16) (hn8 : n < 8 ∨ rexP = true) :
    (rgfi_size (BitVec.ofNat 4 (w / 8)) (BitVec.ofNat 4 n) rex).run s =
      .ok ((regVal js w (regLocOf rexP w n)).setWidth 64) s := by
  rcases hw with rfl | rfl | rfl | rfl
  · simp (config := {decide := true}) only [rgfi_size, eq_bits_nat, Sail.BitVec.toNatInt, ↓reduceIte, run_bind]
    simp only [regLocOf, ↓reduceIte, Janus.Amd64.Decode.reg8]
    by_cases hh : (!rexP && decide (4 ≤ n) && decide (n < 8)) = true
    · simp only [hh, ↓reduceIte, regVal, Janus.Amd64.State.getHigh]
      have hr : rex = 0#8 := by
        simp at hh hrex; cases rexP <;> simp_all
      subst hr
      rw [run_rr08_high (by simp at hh; omega) (by simp at hh; omega) (h.gpr _ (by omega))]
      simp only [run_pure, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq]
    · simp only [hh, Bool.false_eq_true, ↓reduceIte, regVal, Janus.Amd64.State.getReg]
      rw [run_rr08_low hn (h.gpr n hn) rex (by
        simp only [low8]; simp at hh hrex ⊢; cases rexP <;> simp_all <;> omega)]
      simp only [run_pure, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
  · simp only [rgfi_size, eq_bits_nat, Sail.BitVec.toNatInt]
    simp (config := {decide := true}) only [↓reduceIte, run_bind, regLocOf, regVal,
      Janus.Amd64.State.getReg, run_rr16 hn (h.gpr n hn), run_pure, Sail.BitVec.zeroExtend,
      BitVec.zeroExtend_eq_setWidth]
  · simp only [rgfi_size, eq_bits_nat, Sail.BitVec.toNatInt]
    simp (config := {decide := true}) only [↓reduceIte, run_bind, regLocOf, regVal,
      Janus.Amd64.State.getReg, run_rr32 hn (h.gpr n hn), run_pure, Sail.BitVec.zeroExtend,
      BitVec.zeroExtend_eq_setWidth]
  · simp only [rgfi_size, eq_bits_nat, Sail.BitVec.toNatInt]
    simp (config := {decide := true}) only [↓reduceIte, run_bind, regLocOf, regVal,
      Janus.Amd64.State.getReg, run_rr64 hn (h.gpr n hn), run_pure]
    simp

/-- Janus' write of a `w`-bit value to a register location (`writeLoc` on `.reg`/`.high`). -/
def regWrite (js : Janus.Amd64.State) (w : Nat) (l : Janus.Amd64.Loc) (v : BitVec w) : Janus.Amd64.State :=
  match l with
  | .reg r => js.putReg w r v
  | .high r => js.putHigh r (v.setWidth 8)
  | .mem _ => js

/-- The GPR a register location lives in. -/
def locReg : Janus.Amd64.Loc → Nat
  | .reg r => r
  | .high r => r
  | .mem _ => 0

theorem merge_low {k : Nat} (hk : k ≤ 64) (q : BitVec 64) (v : BitVec k) :
    Sail.BitVec.updateSubrange' q 0 k v = (q &&& ~~~(BitVec.allOnes k).setWidth 64) ||| v.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_updateSubrange' q 0 k v i (by omega)]
  by_cases h1 : i < k
  · simp [h1, hi]
  · have : v.getLsbD i = false := BitVec.getLsbD_of_ge v i (by omega)
    simp [h1, hi, this]

theorem ff00_bits : ∀ i < 64, (0xFF00 : BitVec 64).getLsbD i = decide (8 ≤ i ∧ i < 16) := by decide

theorem merge_high (q : BitVec 64) (v : BitVec 8) :
    Sail.BitVec.updateSubrange' q 8 8 v = (q &&& ~~~(0xFF00 : BitVec 64)) ||| (v.setWidth 64 <<< 8) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_updateSubrange' q 8 8 v i (by decide)]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
    ff00_bits i hi, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h1 : i < 8
  · simp [h1, show ¬ (8 ≤ i) by omega]
  by_cases h2 : i < 16
  · simp [h1, h2, show 8 ≤ i by omega, show i - 8 < 64 by omega]
  · have : v.getLsbD (i - 8) = false := BitVec.getLsbD_of_ge v _ (by omega)
    simp [h1, h2, this]

theorem setReg_regs_same (js : Janus.Amd64.State) (r : Nat) (v : BitVec 64) : (js.setReg r v).regs r = v := by
  simp [Janus.Amd64.State.setReg]

theorem run_write_rgfi_size {js : Janus.Amd64.State} {s : SState} (h : Rel js s)
    (hl : s.regs.get? .log_register_writes = some false) {w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (rexP : Bool) (rex : BitVec 8) (hrex : (rex == 0#8) = !rexP)
    {n : Nat} (hn : n < 16) (hn8 : n < 8 ∨ rexP = true) (v : BitVec w) :
    (write_rgfi_size (BitVec.ofNat 4 (w / 8)) (BitVec.ofNat 4 n) (v.setWidth 64) rex).run s =
      .ok () (setGpr s ((regWrite js w (regLocOf rexP w n) v).regs (locReg (regLocOf rexP w n)))
        (locReg (regLocOf rexP w n))) := by
  rcases hw with rfl | rfl | rfl | rfl
  · simp (config := {decide := true}) only [write_rgfi_size, eq_bits_nat, Sail.BitVec.toNatInt, ↓reduceIte]
    simp only [regLocOf, ↓reduceIte, Janus.Amd64.Decode.reg8]
    by_cases hh : (!rexP && decide (4 ≤ n) && decide (n < 8)) = true
    · simp only [hh, ↓reduceIte, regWrite, locReg, Janus.Amd64.State.putHigh, setReg_regs_same]
      have hr : rex = 0#8 := by
        simp at hh hrex; cases rexP <;> simp_all
      subst hr
      have hl2 : (!(0#8 == 0#8) || decide (n < 4)) = false := by simp at hh ⊢; omega
      have hb : Sail.BitVec.toNatInt (bits_of_int (Sail.BitVec.toNatInt (bits_of_int (n : Int) 4) - 4) 4) =
          ((n - 4 : Nat) : Int) := by
        have e1 : Sail.BitVec.toNatInt (bits_of_int (n : Int) 4) = (n : Int) := by
          simp only [Sail.BitVec.toNatInt, bits_of_int_natCast_toNat, Int.ofNat_eq_natCast]; omega
        rw [e1, show (n : Int) - 4 = ((n - 4 : Nat) : Int) by simp at hh; omega]
        simp only [Sail.BitVec.toNatInt, bits_of_int_natCast_toNat, Int.ofNat_eq_natCast]; omega
      simp only [wr08, toNatInt_ofNat4 n hn, Int.toNat_natCast, hl2, Bool.false_eq_true, ↓reduceIte, run_bind, hb,
        run_rgfi (by omega : n - 4 < 16) (h.gpr _ (by omega)), run_write_rgfi hl (by omega : n - 4 < 16),
        changeSlice_bits, Sail.BitVec.updateSubrange, Sail.BitVec.extractLsb]
      rw [← merge_high]
      congr 2
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [getLsbD_updateSubrange' _ _ _ _ _ (by decide), getLsbD_updateSubrange' _ _ _ _ _ (by decide)]
      have e8 : (((8 : Nat) : Int) + ((8 : Nat) : Int) - 1).toNat - 8 + 1 = 8 := rfl
      by_cases h1 : 8 ≤ i ∧ i < 16
      · simp only [e8, h1, ↓reduceIte, Nat.reduceAdd]
        simp [Sail.BitVec.truncate]
      · simp only [e8, h1, ↓reduceIte, Nat.reduceAdd]
        simp [BitVec.getLsbD_extractLsb, hi]
    · simp only [hh, Bool.false_eq_true, ↓reduceIte, regWrite, locReg, Janus.Amd64.State.putReg,
        setReg_regs_same, show ¬ ((8 : Nat) = 64 ∨ (8 : Nat) = 32) by decide]
      have hl2 : (!(rex == 0#8) || decide (n < 4)) = true := by
        simp at hh hrex ⊢; cases rexP <;> simp_all <;> omega
      simp only [wr08, toNatInt_ofNat4 n hn, Int.toNat_natCast, hl2, ↓reduceIte, run_bind,
        run_rgfi hn (h.gpr n hn), run_write_rgfi hl hn,
        changeSlice_bits, Sail.BitVec.updateSubrange, Sail.BitVec.extractLsb]
      rw [← merge_low (by decide)]
      congr 2
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [getLsbD_updateSubrange' _ _ _ _ _ (by decide), getLsbD_updateSubrange' _ _ _ _ _ (by decide)]
      have e8 : (((0 : Nat) : Int) + ((8 : Nat) : Int) - 1).toNat - 0 + 1 = 8 := rfl
      by_cases h1 : 0 ≤ i ∧ i < 8
      · simp only [e8, h1, ↓reduceIte, Nat.reduceAdd]
        simp [Sail.BitVec.truncate]
      · simp only [e8, h1, ↓reduceIte, Nat.reduceAdd]
        simp [BitVec.getLsbD_extractLsb, hi]
  · simp (config := {decide := true}) only [write_rgfi_size, eq_bits_nat, Sail.BitVec.toNatInt, ↓reduceIte]
    simp only [regLocOf, show ¬ ((16 : Nat) = 8) by decide, ↓reduceIte, regWrite, locReg,
      Janus.Amd64.State.putReg, setReg_regs_same, show ¬ ((16 : Nat) = 64 ∨ (16 : Nat) = 32) by decide]
    simp only [wr16, toNatInt_ofNat4 n hn, run_bind, run_rgfi hn (h.gpr n hn), run_write_rgfi hl hn,
      changeSlice_bits, Sail.BitVec.updateSubrange, Sail.BitVec.extractLsb]
    rw [← merge_low (by decide)]
    congr 2
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [getLsbD_updateSubrange' _ _ _ _ _ (by decide), getLsbD_updateSubrange' _ _ _ _ _ (by decide)]
    have e16 : (((0 : Nat) : Int) + ((16 : Nat) : Int) - 1).toNat - 0 + 1 = 16 := rfl
    by_cases h1 : 0 ≤ i ∧ i < 16
    · simp only [e16, h1, ↓reduceIte, Nat.reduceAdd]
      simp [Sail.BitVec.truncate]
    · simp only [e16, h1, ↓reduceIte, Nat.reduceAdd]
      simp [BitVec.getLsbD_extractLsb, hi]
  · simp (config := {decide := true}) only [write_rgfi_size, eq_bits_nat, Sail.BitVec.toNatInt, ↓reduceIte]
    simp only [regLocOf, show ¬ ((32 : Nat) = 8) by decide, ↓reduceIte, regWrite, locReg,
      Janus.Amd64.State.putReg, setReg_regs_same, show ((32 : Nat) = 64 ∨ (32 : Nat) = 32) by decide]
    simp only [wr32, toNatInt_ofNat4 n hn, run_write_rgfi hl hn, Sail.BitVec.zeroExtend, Sail.BitVec.truncate]
    simp only [true_or, or_true, ↓reduceIte, setReg_regs_same]
    congr 2
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp
  · simp (config := {decide := true}) only [write_rgfi_size, eq_bits_nat, Sail.BitVec.toNatInt, ↓reduceIte]
    simp only [regLocOf, show ¬ ((64 : Nat) = 8) by decide, ↓reduceIte, regWrite, locReg,
      Janus.Amd64.State.putReg, setReg_regs_same, show ((64 : Nat) = 64 ∨ (64 : Nat) = 32) by decide]
    simp only [wr64, toNatInt_ofNat4 n hn, run_write_rgfi hl hn]
    simp only [true_or, ↓reduceIte, setReg_regs_same]

end JanusX86.Proofs
