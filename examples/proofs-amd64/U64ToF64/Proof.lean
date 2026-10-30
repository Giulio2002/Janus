import Janus
import Extracted

/-!
# `U64ToF64(x uint64) float64` on amd64: Go's unsigned conversion sequence

**What Go emits.** SSE2 converts only signed integers, so Go tests the sign bit:

```
TESTQ AX, AX; JL big
XORPS X1, X1; CVTSI2SDQ AX, X1; JMP done           // x < 2^63: convert directly
big: MOVQ AX, CX; ANDL $1, AX; SHRQ $1, CX; ORQ AX, CX
     XORPS X1, X1; CVTSI2SDQ CX, X1; ADDSD X1, X1   // convert x/2 | x&1, double it
done: MOVUPS X1, X0; RET
```

**Guarantee.** For every 64-bit `x` in `RAX`, `GoMXCSR` and 8 readable bytes at `RSP`, the call
returns, obeys the ABI, and the low 64 bits of `X0` are `Janus.Float.fromInt binary64 .rne x`, the
correctly rounded conversion: the same result as arm64's single `UCVTF`. The second path is
exact because halving with the lost bit or-ed in ("sticky") keeps every bit the rounding of `x` to
53 bits looks at (`Janus.Float.roundAt_sticky`), and doubling is exact (`Janus.Amd64.FP.u64_big`);
this holds in every rounding direction.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 0 8 ∧ GoMXCSR s)
      (fun _ s' => (s'.xmm 0).toNat % 2 ^ 64 = fromInt binary64 .rne x.toNat) := by
  intro ret hret s hs ⟨hst, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  have hc : IEEEMode (⟨.rne, false, false⟩ : Ctl) := ⟨rfl, rfl⟩
  have hfl := fromInt_lt binary64 .rne
  janus64_run [GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  · have hmsb : x.msb = true := by assumption
    have hx : 2 ^ 63 ≤ x.toNat := by
      rw [BitVec.msb_eq_decide] at hmsb; simp at hmsb; omega
    have hy : (x >>> 1 ||| BitVec.setWidth 64 (BitVec.setWidth 32 x &&& 1#32)).toNat =
        x.toNat / 2 ||| x.toNat % 2 := by
      rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_and,
        BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow, show (1#32).toNat = 1 from rfl,
        Nat.and_one_is_mod, Nat.pow_one]
      first | (with_reducible congr 1; omega) | (congr 1; omega)
    have hylt : x.toNat / 2 ||| x.toNat % 2 < 2 ^ (64 - 1) := by
      have := or_bit (x.toNat / 2) (x.toNat % 2) (Nat.mod_lt _ (by decide))
      have hb : x.toNat / 2 % 2 ||| x.toNat % 2 < 2 :=
        Nat.or_lt_two_pow (n := 1) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
      omega
    rw [hy, ofInt_ieee hc]
    simp only [hylt, ite_true]
    have h1 : fromInt binary64 .rne ((x.toNat / 2 ||| x.toNat % 2 : Nat) : Int) < 18446744073709551616 :=
      hfl _
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega : fromInt binary64 .rne
      ((x.toNat / 2 ||| x.toNat % 2 : Nat) : Int) < 340282366920938463463374607431768211456)]
    rw [u64_big hc x.toNat hx x.isLt]
    have h2 : fromInt binary64 .rne (x.toNat : Int) < 18446744073709551616 := hfl _
    dsimp only
    omega
  · rw [ofInt_ieee hc]
    have hlt : fromInt binary64 .rne (x.toNat : Int) < 18446744073709551616 := hfl _
    have hmsb : ¬ x.msb = true := by assumption
    have hx : x.toNat < 2 ^ 63 := by
      rw [BitVec.msb_eq_decide] at hmsb; simp at hmsb; omega
    simp only [show x.toNat < 2 ^ (64 - 1) from hx, ite_true]
    rw [Nat.mod_eq_of_lt hlt]
    exact Nat.mod_eq_of_lt (by omega)

end Proof
