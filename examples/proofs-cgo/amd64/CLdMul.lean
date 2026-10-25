import Extracted

/-!
# `long double ld_mul(long double a, long double b)` (C, amd64): x87 extended multiplication

The code is `endbr64; fldt 0x8(%rsp); fldt 0x18(%rsp); fmulp %st,%st(1); ret`: System V passes
each `long double` argument in memory (class X87, 16 bytes on the stack, the double-extended
value in the low 10) and returns the result in `ST(0)`.

**Guarantee.** For all 80-bit `a` and `b`, every System V call of the gcc-compiled `ld_mul`
with `a` at `[RSP+8]` and `b` at `[RSP+24]` (the stack readable up to `RSP+40`) and the x87 FPU
in its call state (`X87.Idle`: empty register stack, control word `0x037F`, no pending
exception) returns without faulting, restores what the C calling convention requires
(`CReturn`), and leaves exactly one register in use: `ST(0)` holds `X87.binop .mul 64 .rne a b`,
the double-extended product rounded to nearest at 64-bit precision; the control word is
unchanged. `ieee` restates the result through `X87.std` as IEEE 754 multiplication on the
format (15, 63) (`Janus.Float.mul`, `X87.binop_mul_ieee`) for supported operands.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic

namespace Proof

/-- What `ld_mul` leaves: the product in `ST(0)`, the only register in use, and the control
word unchanged. -/
def LdResult (r : Nat) (t : X87.St) : Prop :=
  t.get 0 = some r ∧ (∀ i, t.tags i = decide (i = t.top)) ∧ t.top < 8 ∧ t.cw = 0x37F

set_option maxHeartbeats 2000000 in
theorem correctness (a b : Nat) :
    CEnsures Extracted.program Extracted.entry []
      (fun s => CStack s 0 40 ∧ X87.Idle s.x87 ∧
        s.mem.readLE ((s.regs 4).toNat + 8) 10 = a ∧ s.mem.readLE ((s.regs 4).toNat + 24) 10 = b)
      (fun _ s' => LdResult (X87.binop .mul 64 .rne a b).res s'.x87) := by
  simp only [LdResult]
  intro ret hret s hs ⟨⟨_, _, hnw, hacc⟩, ⟨hcw, htags, hes, htop⟩, ha, hb⟩
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add, Program.withExit] at hacc hnw h_ret
  janus64_run [hcw, htags, hes, ha, hb]
  refine ⟨?_, fun i => ?_, by omega⟩
  · simp [X87.St.get, X87.St.used, X87.St.phys]; omega
  · by_cases h1 : i = (s.x87.top + 6) % 8 <;> by_cases h2 : i = (s.x87.top + 7) % 8 <;>
      simp [h1, h2] <;> omega

/-- The result as IEEE 754: for supported operands, `std` of the product is the IEEE product
of `std a` and `std b`, rounded to nearest (a NaN exactly when the IEEE result is). -/
theorem ieee (a b : Nat) (ha : X87.unsupported a = false) (hb : X87.unsupported b = false) :
    Janus.Float.ResultIs X87.ext (Janus.Float.mul X87.ext .rne (X87.std a) (X87.std b))
      (X87.std (X87.binop .mul 64 .rne a b).res) :=
  X87.binop_mul_ieee .rne a b false ha hb

end Proof
