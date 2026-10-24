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
@[janus64_exec] theorem fp_rounding_default : FP.rounding 8064 = .rne := by decide
@[janus64_exec] theorem fp_and_zero (n : Nat) : n &&& 0 = 0 := Nat.and_zero n
@[janus64_exec] theorem fp_mxcsr_default_toNat : (8064#32).toNat = 8064 := rfl

end Janus.Amd64.Tactic
