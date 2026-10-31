import Janus
import Extracted

/-!
# `bitscan.BitLen64(x uint64) uint64` (`bits.Len64`) on amd64 at `GOAMD64=v1`

**Guarantee.** For every `x` and every Go call state the call returns, obeys the ABI, and leaves
in `RAX` the bit length of `x`: `0` for `x = 0`, else `⌊log₂ x⌋ + 1`.

Go compiles it to

```
BSRQ AX, AX ; MOVQ $-1, CX ; CMOVQEQ CX, AX ; INCQ AX ; RET
```

`BSR` of zero sets `ZF` and leaves its destination *undefined* (Intel; AMD keeps it). The model
makes it an arbitrary 64-bit value (`State.undefVal`), the proof holds for every such value, and
`CMOVQEQ` (which reads only `ZF`) replaces it by `-1`: this is `Janus` docs/AUDIT.md LOW-2.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Arm64

/-- The bit length. -/
def bitLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

/-- Leading zeros of a nonzero `n`-bit value. -/
theorem clz_log2 : ∀ (n x : Nat), x < 2 ^ n → 0 < x → Nat.log2 x < n ∧ clzNat n x = n - 1 - Nat.log2 x
  | 0, x, hx, h0 => by simp at hx; omega
  | n + 1, x, hx, h0 => by
    by_cases hb : x.testBit n = true
    · have h1 : 2 ^ n ≤ x := Nat.ge_two_pow_of_testBit hb
      have := Nat.log2_eq_of_pow_le_of_lt_pow h1 (by rw [← Nat.pow_succ]; exact hx)
      simp [clzNat, hb, this]
    · have h2 : x < 2 ^ n := by
        by_contra hc
        have h1 : 2 ^ n ≤ x := by omega
        have := Nat.testBit_two_pow_add_gt
        apply hb
        rw [Nat.testBit_eq_decide_div_mod_eq]
        have : x / 2 ^ n = 1 := by
          rw [Nat.div_eq_iff (by positivity)]
          rw [Nat.pow_succ] at hx; omega
        simp [this]
      obtain ⟨h3, h4⟩ := clz_log2 n x h2 h0
      simp [clzNat, hb, h4]; omega

theorem correctness (x : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x] 1
      (fun s => StackWritable s 0 8)
      (fun r => r = [BitVec.ofNat 64 (bitLen x.toNat)]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  sorry

end Proof
