import Janus
import Extracted

/-!
# `MaxF64(a, b float64) float64` on amd64: the `min` sequence on the negations

**What Go emits.** `max(a, b) = -min(-a, -b)`: the sign bit (`$f64.8000000000000000`, loaded from
`.rodata`) is flipped in both operands with `PXOR`, the `MINSD`/`MINSD`/`POR` sequence of `MinF64`
runs, and the result's sign is flipped back.

**Guarantee.** For all binary64 encodings `a`, `b` in the low 64 bits of `X0`, `X1`, the constant
loaded (`DataLoaded`), `GoMXCSR` and 8 readable bytes at `RSP`, the call returns, obeys the ABI,
and the low 64 bits of `X0` are IEEE 754-2019 `maximum(a, b)` (`Janus.Float.maximum`): a NaN if
either is a NaN, `+0` for two zeros of different signs, the larger operand otherwise. Same
statement as arm64's `FMAX` (`Janus.Float.minimum_flip`, `Janus.Amd64.FP.maxsd_seq`).
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP

def lit : Janus.DataSegment := Extracted.data[0]
theorem lit_mem : lit ∈ Extracted.program.data := List.mem_cons_self

theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ Extracted.program.DataLoaded s.mem ∧
        (s.xmm 0).toNat % 2 ^ 64 = a.toNat ∧ (s.xmm 1).toNat % 2 ^ 64 = b.toNat ∧ GoMXCSR s)
      (fun _ s' => ResultIs binary64 (maximum binary64 a.toNat b.toNat) ((s'.xmm 0).toNat % 2 ^ 64)) := by
  intro ret hret s hs ⟨hst, hdl, ha, hb, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  have hrd := DataLoaded.accessible hdl lit_mem
  have hlen : lit.bytes.length = 8 := by decide
  have hb' : lit.base = dataBase Extracted.program 0 := rfl
  simp only [reduceDataBase] at hb'
  rw [hlen, hb'] at hrd
  have hc := DataLoaded.readLE hdl lit_mem 0 8 (by rw [hlen]; omega)
  rw [hb', show listLE (lit.bytes.drop 0) 8 = 0x8000000000000000 by decide] at hc
  janus64_run [ha, hb, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  have hflip : ∀ (v : BitVec 128) (y : BitVec 64), v.toNat % 2 ^ 64 = y.toNat →
      (v ^^^ 9223372036854775808#128).toNat % 18446744073709551616 = y.toNat ^^^ 2 ^ 63 := by
    intro v y hv
    rw [BitVec.toNat_xor, show (18446744073709551616 : Nat) = 2 ^ 64 from rfl, Nat.xor_mod_two_pow, hv]
    rfl
  rw [hflip _ a ha, hflip _ b hb]
  have hc : IEEEMode (⟨.rne, false, false⟩ : Ctl) := ⟨rfl, rfl⟩
  have ha' := flip_lt a.toNat a.isLt
  have hb' := flip_lt b.toNat b.isLt
  obtain ⟨hl, hr⟩ := maxsd_seq hc a.toNat b.toNat a.isLt b.isLt
  have htl : (minmax false binary64 ⟨.rne, false, false⟩ (a.toNat ^^^ 2 ^ 63) (b.toNat ^^^ 2 ^ 63)).res < 2 ^ 64 := by
    rw [minmax_min_ieee hc _ _ ha' hb']
    split <;> (try split) <;> (try split) <;> omega
  generalize (minmax false binary64 ⟨.rne, false, false⟩ (a.toNat ^^^ 2 ^ 63) (b.toNat ^^^ 2 ^ 63)).res = t
    at hl hr htl ⊢
  rw [show (BitVec.toNat (s.xmm 0 ^^^ 9223372036854775808#128) / 18446744073709551616 * 18446744073709551616 +
    t % 18446744073709551616) % 18446744073709551616 = t by omega]
  have hul : (minmax false binary64 ⟨.rne, false, false⟩ t (a.toNat ^^^ 2 ^ 63)).res < 2 ^ 64 := by
    rw [minmax_min_ieee hc _ _ htl ha']
    split <;> (try split) <;> (try split) <;> omega
  generalize (minmax false binary64 ⟨.rne, false, false⟩ t (a.toNat ^^^ 2 ^ 63)).res = u at hl hr hul ⊢
  have key : ∀ A B : Nat, (BitVec.ofNat 128 ((A / 18446744073709551616 * 18446744073709551616 +
      u % 18446744073709551616) % 340282366920938463463374607431768211456 |||
      (B / 18446744073709551616 * 18446744073709551616 + t % 18446744073709551616) %
      340282366920938463463374607431768211456) ^^^ 9223372036854775808#128).toNat % 18446744073709551616 =
      (u ||| t) ^^^ 2 ^ 63 := by
    intro A B
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, show (18446744073709551616 : Nat) = 2 ^ 64 from rfl,
      Nat.xor_mod_two_pow, Nat.mod_mod_of_dvd _ (by decide), Nat.or_mod_two_pow]
    rw [show (A / 2 ^ 64 * 2 ^ 64 + u % 2 ^ 64) % 340282366920938463463374607431768211456 % 2 ^ 64 = u by omega,
      show (B / 2 ^ 64 * 2 ^ 64 + t % 2 ^ 64) % 340282366920938463463374607431768211456 % 2 ^ 64 = t by omega,
      show (9223372036854775808#128).toNat % 2 ^ 64 = 2 ^ 63 from rfl]
  rw [key]
  exact hr

end Proof
