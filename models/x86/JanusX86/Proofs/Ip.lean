import JanusX86.Proofs.Arith
import JanusX86.Proofs.Rel

/-! # The instruction pointer and the end of an instruction -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem toInt_ofNat48 (a : Nat) (h : a < 2 ^ 47) : (BitVec.ofNat 48 a).toInt = (a : Int) := by
  rw [toInt_of_lt _ (by simp; omega)]; simp; omega

theorem check_len_ok (sr tr : Nat) (h1 : sr ≤ tr) (h2 : tr ≤ sr + 15) (h3 : tr < 2 ^ 47) :
    check_instruction_length (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) 0#3 = none := by
  have e1 := toInt_ofNat48 sr (by omega)
  have e2 := toInt_ofNat48 tr h3
  have e3 : (bits_of_int (tr : Int) 48).toInt = (tr : Int) := bits_of_int_toInt _ _ (by omega) (by omega)
  have e4 : (bits_of_int (sr : Int) 48).toInt = (sr : Int) := bits_of_int_toInt _ _ (by omega) (by omega)
  have e5 : Sail.BitVec.toNatInt (bits_of_int (((Sail.BitVec.toNatInt (0#3)).toNat : Nat) : Int) 3) = 0 := by decide
  have e6 : (bits_of_int (tr : Int) 49).toInt = (tr : Int) := bits_of_int_toInt _ _ (by omega) (by omega)
  have e7 : (bits_of_int ((tr : Int) - (sr : Int)) 50).toInt = (tr : Int) - (sr : Int) :=
    bits_of_int_toInt _ _ (by omega) (by omega)
  unfold check_instruction_length
  have e6' : (bits_of_int ((tr : Int) + 0) 49).toInt = (tr : Int) := by rw [Int.add_zero]; exact e6
  simp only [e1, e2, e3, e4, e5, e6', e7]
  have : ((15 : Int) <b ((tr : Int) - (sr : Int))) = false := by simp; omega
  simp only [this, Bool.false_eq_true, ↓reduceIte]

theorem run_write_iptr {s : SState} (hl : s.regs.get? .log_register_writes = some false) (tr : Nat)
    (h : tr < 2 ^ 47) :
    (write_iptr .Mode_64bit (BitVec.ofNat 48 tr)).run s = .ok () (s.set .rip (BitVec.ofNat 64 tr)) := by
  have e : regval_into_reg (Sail.BitVec.signExtend (BitVec.ofNat 48 tr) 64) = BitVec.ofNat 64 tr := by
    apply BitVec.eq_of_toNat_eq
    rw [regval_into_reg, signExtend48_toNat tr h]; simp; omega
  simp only [write_iptr, in_64bit_mode, ↓reduceIte, write_rip, run_bind, run_writeReg, e,
    run_readReg (show (s.set .rip (BitVec.ofNat 64 tr)).regs.get? .log_register_writes = some false by
      rw [get?_set_ne _ _ (by decide)]; exact hl), Bool.false_eq_true, run_pure]

theorem Rel.flagsRip {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (f : Janus.Amd64.Flags)
    (r : BitVec 32) (hf : FlagsRel f js.df r) (v : BitVec 64) :
    Rel ((js.setFlags f).setRip v) ((s.set .rflags r).set .rip v) := by
  obtain ⟨m, hm, hmr⟩ := h.fs
  refine ⟨?_, by simp [Janus.Amd64.State.setRip], ⟨r, ?_, hf⟩, ⟨m, ?_, hmr⟩, h.mem, h.canon⟩
  · intro i hi
    rw [gprVal_set_of_not _ rfl, gprVal_set_of_not _ rfl]; exact h.gpr i hi
  · rw [get?_set_ne _ _ (by decide)]; simp
  · rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; exact hm

end JanusX86.Proofs
