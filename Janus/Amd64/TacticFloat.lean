import Janus.Amd64.Tactic
import Janus.Amd64.FloatLemmas

/-!
# Symbolic execution of the SSE scalar floating-point instructions (amd64)

The executor plumbing (`readXs`, `fpDone`, `State.setXmmLow`, `State.raiseMx`, `sseArithOp`) is
unfolded by `janus64_exec`; the operations themselves (`FP.binop`, `FP.toInt`, ...) are not, so
a symbolic `XMM` register holds a term like `(FP.binop .add binary64 mx a b).res`. With the
value of `MXCSR` given to `janus64_run` (e.g. `s.mxcsr = 0x1F80`), the trap check
`traps AND unmasked(MXCSR) ≠ 0` is a closed literal. Nothing here is trusted.
-/

namespace Janus.Amd64.Tactic

open Janus.Amd64

attribute [janus64_exec] readXs State.setXmmLow State.raiseMx fpDone sseArithOp fmtOf FP.XR.trap

@[janus64_exec] theorem fp_unmasked_default : FP.unmasked 8064 = 0 := by decide
@[janus64_exec] theorem fp_ctl_default : FP.ctl 8064 = ⟨.rne, false, false⟩ := by decide
@[janus64_exec] theorem fp_and_zero (n : Nat) : n &&& 0 = 0 := Nat.and_zero n
@[janus64_exec] theorem fp_mxcsr_default_toNat : (8064#32).toNat = 8064 := rfl
@[janus64_exec] theorem fp_mod_default : (8064 : Nat) % 4294967296 = 8064 := rfl

/-- Raising flags (bits 5:0) keeps every control bit of `MXCSR` (bits 6 and up). -/
theorem mx_raise_div (m x : Nat) : ((m ||| x % 64) % 4294967296) / 64 = (m % 4294967296) / 64 := by
  have hy : x % 64 < 2 ^ 6 := Nat.mod_lt _ (by decide)
  rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, Nat.or_mod_two_pow,
    Nat.mod_eq_of_lt (Nat.lt_trans hy (by decide)), show (64 : Nat) = 2 ^ 6 from rfl,
    Nat.or_div_two_pow, Nat.div_eq_of_lt hy, Nat.or_zero]

theorem mx_div (m : Nat) (k : Nat) : m / 2 ^ (6 + k) = m / 64 / 2 ^ k := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]

@[janus64_exec] theorem unmasked_raise (m x : Nat) :
    FP.unmasked ((m ||| x % 64) % 4294967296) = FP.unmasked (m % 4294967296) := by
  unfold FP.unmasked; rw [show (7 : Nat) = 6 + 1 from rfl, mx_div, mx_div, mx_raise_div]

@[janus64_exec] theorem ctl_raise (m x : Nat) :
    FP.ctl ((m ||| x % 64) % 4294967296) = FP.ctl (m % 4294967296) := by
  unfold FP.ctl FP.rounding FP.daz FP.ftz FP.mxBit
  rw [show (13 : Nat) = 6 + 7 from rfl, show (15 : Nat) = 6 + 9 from rfl,
    show (6 : Nat) = 6 + 0 from rfl, mx_div, mx_div, mx_div, mx_div, mx_div, mx_div, mx_raise_div]

end Janus.Amd64.Tactic
