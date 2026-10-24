import JanusASL.Proofs.Gpr

/-! Run lemmas for the register accessors of the generated model (X[], SP[], undefined). -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

@[simp] theorem run_undefined_bitvector (n : Nat) (s : SState) :
    (undefined_bitvector n).run s = .ok 0#n s := by
  cases s; rfl

@[simp] theorem run_undefined_bool (s : SState) : (undefined_bool ()).run s = .ok false s := by
  cases s; rfl

@[simp] theorem run_undefined_int (s : SState) : (undefined_int ()).run s = .ok 0 s := by
  cases s; rfl

theorem run_sail_assert_of {p : Bool} (h : p = true) (msg : String) (s : SState) :
    (sail_assert p msg).run s = .ok () s := by subst h; rfl

@[simp] theorem run_sail_assert_true (msg : String) (s : SState) :
    (sail_assert true msg).run s = .ok () s := rfl

theorem run_X_read {s : SState} {n : Nat} (hn : n < 31) {v : BitVec 64} (h : gprVal s n = some v)
    {w : Nat} (hw : w = 32 ∨ w = 64) :
    (X_read (n : Int) w).run s = .ok (Sail.BitVec.extractLsb v ((w : Int) - 1).toNat 0 |>.setWidth w) s := by
  have h1 : ((n : Int) != 31) = true := by simp; omega
  have h2 : (decide ((n : Int) ≥ 0) && decide ((n : Int) ≤ 31)) = true := by simp; omega
  have h3 : (w == 8 || (w == 16 || (w == 32 || w == 64))) = true := by rcases hw with rfl | rfl <;> rfl
  have h4 : ((n : Int).toNat) = n := by omega
  simp only [X_read, run_bind, h1, h2, h3, h4, get_R, run_sail_assert_true, ite_true,
    run_read_gpr hn h]
  rcases hw with rfl | rfl <;> rfl

theorem run_X_read_zr (s : SState) {w : Nat} (hw : w = 32 ∨ w = 64) :
    (X_read (31 : Nat) w).run s = .ok 0#w s := by
  rcases hw with rfl | rfl <;> rfl

theorem run_X_set {s : SState} {n : Nat} (hn : n < 31) {w : Nat} (hw : w = 32 ∨ w = 64) (v : BitVec w) :
    (X_set (n : Int) w v).run s = .ok () (setGpr s (Sail.BitVec.zeroExtend v 64) n) := by
  have h1 : ((n : Int) != 31) = true := by simp; omega
  have h2 : (decide ((n : Int) ≥ 0) && decide ((n : Int) ≤ 31)) = true := by simp; omega
  have h3 : (w == 32 || w == 64) = true := by rcases hw with rfl | rfl <;> rfl
  have h4 : ((n : Int).toNat) = n := by omega
  simp only [X_set, run_bind, h1, h2, h3, h4, set_R, run_sail_assert_true, ite_true,
    run_write_gpr s hn]

theorem run_X_set_zr (s : SState) {w : Nat} (hw : w = 32 ∨ w = 64) (v : BitVec w) :
    (X_set (31 : Nat) w v).run s = .ok () s := by
  rcases hw with rfl | rfl <;> rfl

theorem run_SP_read {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p) (hsp : p.SP = 0#1)
    {v : BitVec 64} (h : s.regs.get? .SP_EL0 = some v) : (SP_read ()).run s = .ok v s := by
  simp only [SP_read, run_bind, run_readReg hp, hsp]
  exact run_readReg h

theorem run_SP_set {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p) (hsp : p.SP = 0#1)
    (v : BitVec 64) : (SP_set v).run s = .ok () (s.set .SP_EL0 v) := by
  simp only [SP_set, run_bind, run_readReg hp, hsp]
  rfl

end JanusASL.Proofs
