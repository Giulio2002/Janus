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
`CMOVQEQ` (which reads only `ZF`) replaces it by `-1`: this is `Janus` docs/audit/AUDIT.md LOW-2.
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
      have hl : Nat.log2 x = n := by
        have a := (Nat.le_log2 (by omega)).2 h1
        have b := (Nat.log2_lt (by omega)).2 hx
        omega
      simp [clzNat, hb, hl]
    · have h2 : x < 2 ^ n := by
        refine Classical.byContradiction fun hc => ?_
        apply hb
        have h1 : 2 ^ n ≤ x := by omega
        have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
        have hd1 : 1 ≤ x / 2 ^ n := (Nat.le_div_iff_mul_le hpos).2 (by omega)
        have hd2 : x / 2 ^ n < 2 := (Nat.div_lt_iff_lt_mul hpos).2 (by rw [Nat.pow_succ] at hx; omega)
        have : x / 2 ^ n = 1 := by omega
        simp [Nat.testBit_eq_decide_div_mod_eq, this]
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
  by_cases hx0 : x.toNat = 0
  · simp [hx0, bitLen]
  · have hlt := x.isLt
    obtain ⟨h3, h4⟩ := clz_log2 64 x.toNat hlt (by omega)
    simp only [hx0, ite_false, bitLen]
    apply congrArg (fun v => [v])
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def s0 (x : BitVec 64) : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then x else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup0 : CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] (s0 0) :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem setup1 : CallSetup (Extracted.program.withExit ret) Extracted.entry [0x40#64] (s0 0x40) :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem pre0 : StackWritable (s0 0) 0 8 := ⟨by decide, by decide, by decide⟩
theorem pre1 : StackWritable (s0 0x40) 0 8 := ⟨by decide, by decide, by decide⟩

/-- So the guarantee is reached: `BitLen64(0)` returns `0` and `BitLen64(0x40)` returns `7`. -/
theorem returns :
    Returns (Extracted.program.withExit ret) (s0 0) (fun s' => ABIReturn (s0 0) s' ∧ results 1 s' = [0#64]) ∧
    Returns (Extracted.program.withExit ret) (s0 0x40) (fun s' => ABIReturn (s0 0x40) s' ∧ results 1 s' = [7#64]) := by
  refine ⟨(correctness 0 ret hret _ setup0 pre0).mono ?_, (correctness 0x40 ret hret _ setup1 pre1).mono ?_⟩
  · intro s' h; exact ⟨h.1, by rw [h.2]; decide⟩
  · intro s' h; exact ⟨h.1, by rw [h.2]; decide⟩

/-- The hypotheses of `correctness` hold, for the zero source (where `BSR` leaves its destination
undefined) and for a non-zero one. -/
theorem nonvacuous : ∃ (ret : Nat) (s s' : Janus.Amd64.State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s ∧ StackWritable s 0 8 ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0x40#64] s' ∧ StackWritable s' 0 8 ∧
    Returns (Extracted.program.withExit ret) s (fun t => ABIReturn s t ∧ results 1 t = [0#64]) ∧
    Returns (Extracted.program.withExit ret) s' (fun t => ABIReturn s' t ∧ results 1 t = [7#64]) :=
  ⟨ret, s0 0, s0 0x40, hret, setup0, pre0, setup1, pre1, returns.1, returns.2⟩

end Witness

end Proof
