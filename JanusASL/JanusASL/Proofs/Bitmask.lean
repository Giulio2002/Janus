import JanusASL.Proofs.Step

/-! # `DecodeBitMasks`: the generated ASL against Janus' `decodeBitMasks`

`dbm64`/`dbm32` check all 2 * 64 * 64 * 2 `(immN, imms, immr, immediate)` inputs at both widths by kernel
evaluation (`decide +kernel`: the kernel evaluates both functions; no `native_decide`, no
compiled code is trusted). `run_DBM_of` lifts the result from the `default` state to any state
(the function reads no state). -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- The value of a `SailM` result, if it completed. -/
def resOpt {ε σ α} : EStateM.Result ε σ α → Option α
  | .ok v _ => some v
  | _ => none

def aslDBM (immN : BitVec 1) (imms immr : BitVec 6) (imm : Bool) (M : Nat) : Option (BitVec M × BitVec M) :=
  resOpt ((DecodeBitMasks immN imms immr imm M).run default)

def janDBM (immN : BitVec 1) (imms immr : BitVec 6) (imm : Bool) (M : Nat) : Option (BitVec M × BitVec M) :=
  (Janus.Arm64.decodeBitMasks (immN == 1#1) imms.toNat immr.toNat imm M).map
    fun p => (BitVec.ofNat M p.1, BitVec.ofNat M p.2)

set_option maxRecDepth 100000 in
theorem dbm64 : ∀ immN : BitVec 1, ∀ imms immr : BitVec 6, ∀ imm : Bool,
    aslDBM immN imms immr imm 64 = janDBM immN imms immr imm 64 := by decide +kernel

set_option maxRecDepth 100000 in
theorem dbm32 : ∀ immN : BitVec 1, ∀ imms immr : BitVec 6, ∀ imm : Bool,
    aslDBM immN imms immr imm 32 = janDBM immN imms immr imm 32 := by decide +kernel

theorem run_bind_ifThrow {β} (c : Bool) (e : exception) (f : Unit → SailM β) (s : SState) :
    (((if c then sailThrow e else pure ()) : SailM Unit) >>= f).run s =
      if c then .error (.User e) s else (f ()).run s := by
  cases c <;> rfl

theorem run_bind_assert {β} (p : Bool) (msg : String) (f : Unit → SailM β) (s : SState) :
    (sail_assert p msg >>= f).run s = if p then (f ()).run s else .error (.Assertion msg) s := by
  cases p <;> rfl

theorem run_DBM_of {a : BitVec 1} {b c : BitVec 6} {imm : Bool} {M : Nat} {v : BitVec M × BitVec M}
    (h : aslDBM a b c imm M = some v) (s : SState) : (DecodeBitMasks a b c imm M).run s = .ok v s := by
  simp only [aslDBM, DecodeBitMasks, run_bind_ifThrow, run_bind_assert, run_pure, apply_ite resOpt] at h ⊢
  repeat (split <;> simp_all [resOpt])

/-- Where Janus' `decodeBitMasks` succeeds, the ASL's `DecodeBitMasks` returns the same masks. -/
theorem run_DBM_janus {a : BitVec 1} {b c : BitVec 6} {imm : Bool} {M : Nat} (hM : M = 32 ∨ M = 64)
    {p : Nat × Nat} (h : Janus.Arm64.decodeBitMasks (a == 1#1) b.toNat c.toNat imm M = some p) (s : SState) :
    (DecodeBitMasks a b c imm M).run s = .ok (BitVec.ofNat M p.1, BitVec.ofNat M p.2) s := by
  apply run_DBM_of
  have hj : janDBM a b c imm M = some (BitVec.ofNat M p.1, BitVec.ofNat M p.2) := by simp [janDBM, h]
  rcases hM with rfl | rfl
  · rw [dbm32]; exact hj
  · rw [dbm64]; exact hj

end JanusASL.Proofs
