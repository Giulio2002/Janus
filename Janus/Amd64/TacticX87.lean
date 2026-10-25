import Janus.Amd64.Tactic
import Janus.Amd64.X87Lemmas

/-!
# Symbolic execution of the x87 instructions (amd64)

The executor plumbing of `Janus.Amd64.X87Exec` (the register stack, the tag word, the
pending-exception check, the condition codes) is unfolded by `janus64_exec`; the operations
themselves (`X87.binop`, `X87.toFmt`, ...) are not, so a symbolic `ST(i)` holds a term like
`(X87.binop .mul 64 .rne a b).res`. With the control word of the System V ABI (`X87.Idle`:
`0x037F`) the trap checks and the precision/rounding controls are closed literals, also after
instructions raised flags (`sw_raise_es`). Nothing here is trusted.
-/

namespace Janus.Amd64.Tactic

open Janus.Amd64

attribute [janus64_exec] X87.exec X87.execWaiting X87.getST X87.operand X87.memAddr X87.arithOp
  X87.fin X87.St.popIf X87.St.setCC X87.St.get X87.St.set X87.St.push X87.St.pop X87.St.raise
  X87.St.ccC1 X87.St.phys X87.St.used X87.St.pending X87.MemFmt.size X87.MemFmt.intWidth X87.done

@[janus64_exec] theorem x87_unmasked_default : X87.unmasked 0x37F = 0 := by decide
@[janus64_exec] theorem x87_precision_default : X87.precision 0x37F = some 64 := by decide
@[janus64_exec] theorem x87_rounding_default : X87.rounding 0x37F = .rne := by decide

/-- Raising flags (bits 5:0) keeps `ES` (bit 7). -/
@[janus64_exec] theorem sw_raise_es (a b : Nat) : (a ||| b % 64) / 128 = a / 128 := by
  rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.or_div_two_pow,
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)), Nat.or_zero]

@[janus64_exec] theorem x87_mod_one_bne (x : Nat) : (x % 1 != 0) = false := by rw [Nat.mod_one]; rfl

@[janus64_exec] theorem x87_and_zero (n : Nat) : n &&& 0 = 0 := Nat.and_zero n
@[janus64_exec] theorem x87_or_zero (n : Nat) : n ||| 0 = n := Nat.or_zero n

end Janus.Amd64.Tactic
