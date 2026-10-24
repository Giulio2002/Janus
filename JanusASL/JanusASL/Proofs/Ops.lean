import JanusASL.Proofs.Rel
import JanusASL.Proofs.Arith

/-! Operand access through `Rel`: `X[n]` reads and `X[d] = v` writes of the generated model
against Janus' `getX` / `setX`. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- Registers other than X0-X30, SP_EL0 and PSTATE are unchanged. -/
def Frame (s s' : SState) : Prop :=
  ∀ r, isGprReg r = false → r ≠ .SP_EL0 → r ≠ .PSTATE → s'.regs.get? r = s.regs.get? r

theorem extract_setWidth {N : Nat} (hN : N = 32 ∨ N = 64) (x : BitVec 64) :
    BitVec.setWidth N (Sail.BitVec.extractLsb x ((N : Int) - 1).toNat 0) = x.setWidth N := by
  rcases hN with rfl | rfl <;> (apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.extractLsb]) <;>
    first | exact x.isLt | omega

theorem Frame.refl (s : SState) : Frame s s := fun _ _ _ _ => rfl

theorem Frame.trans {s1 s2 s3 : SState} (a : Frame s1 s2) (b : Frame s2 s3) : Frame s1 s3 :=
  fun r g h1 h2 => (b r g h1 h2).trans (a r g h1 h2)

theorem run_X_read_rel {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {n : Nat} (hn : n < 32)
    {N : Nat} (hN : N = 32 ∨ N = 64) : (X_read (n : Int) N).run s = .ok (js.getX N n) s := by
  by_cases hn31 : n = 31
  · subst hn31
    rw [run_X_read_zr s hN]
    simp [Janus.Arm64.State.getX, Janus.Arm64.State.readZR]
  · have hn' : n < 31 := by omega
    rw [run_X_read hn' (h.gpr n hn') hN, extract_setWidth hN]
    simp [Janus.Arm64.State.getX, Janus.Arm64.State.readZR, hn31]

theorem run_X_set_rel {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {d : Nat} (hd : d < 32)
    {N : Nat} (hN : N = 32 ∨ N = 64) (v : BitVec N) :
    ∃ s', (X_set (d : Int) N v).run s = .ok () s' ∧ Rel (js.setX d v) s' ∧ Frame s s' := by
  by_cases hd31 : d = 31
  · subst hd31
    refine ⟨s, run_X_set_zr s hN v, ?_, Frame.refl s⟩
    simpa [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR] using h
  · have hd' : d < 31 := by omega
    refine ⟨_, run_X_set hd' hN v, ?_, fun x hx _ _ => get?_setGpr _ _ hd' x hx⟩
    simpa [Janus.Arm64.State.setX, Sail.BitVec.zeroExtend] using h.writeZR hd' (v.setWidth 64)

theorem pair_ofBool {N : Nat} (sub : Bool) (y : BitVec N) :
    (if sub = true then (1#1, ~~~y) else (0#1, y)) = (BitVec.ofBool sub, if sub then ~~~y else y) := by
  cases sub <;> rfl

end JanusASL.Proofs
