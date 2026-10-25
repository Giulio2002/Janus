import Janus
import Extracted

/-! `example.com/basic.Log2(x uint64) uint64` on amd64: a `for` loop with only a condition.

For every 64-bit `x` the call returns (the loop terminates) with `r = RAX` the floor of the
base-2 logarithm of `x`: `2^r ≤ x < 2^(r+1)` when `x ≥ 1`, and `r = 0` when `x = 0`.

```
XORL CX, CX ; JMP head
body: SHRQ $1, AX ; INCQ CX
head: CMPQ AX, $1 ; JA body
MOVQ CX, AX ; RET
```

`loop` is the invariant at the head (`count + log2(x) = log2(x₀)`), proved by induction on a
bound `k` with `x < 2^k`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- The loop head (`CMPQ AX, $1`). -/
def loopHead : Nat := Extracted.entry + 0xa

theorem loop (x : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (m : Memory) :
    ∀ k (y c : BitVec 64) (t : State), y.toNat < 2 ^ k →
      c.toNat + Nat.log2 y.toNat = Nat.log2 x.toNat →
      t.rip = BitVec.ofNat 64 loopHead → t.regs 0 = y → t.regs 1 = c →
      t.mem = m → m.accessible (t.regs 4).toNat 8 false = true →
      m.readLE (t.regs 4).toNat 8 = ret →
      Reaches (Extracted.program.withExit ret) t (IsReturn fun t' =>
        (t'.regs 0).toNat = Nat.log2 x.toNat ∧ t'.regs 4 = t.regs 4 + 8 ∧
        t'.regs 5 = t.regs 5 ∧ t'.regs 14 = t.regs 14 ∧ t'.xmm 15 = t.xmm 15) := by
  have hlx : Nat.log2 x.toNat < 64 := by
    by_cases h : x.toNat = 0
    · rw [h]; decide
    · exact (Nat.log2_lt h).2 x.isLt
  intro k
  induction k
  case zero =>
    intro y c t hy hc h_rip h0 h1 hmem hsp hra
    simp only [loopHead] at h_rip
    janus64_run
    rw [← hc, show y.toNat = 0 by omega]; rfl
  case succ k ih =>
    intro y c t hy hc h_rip h0 h1 hmem hsp hra
    simp only [loopHead] at h_rip
    janus64_run until [loopHead]
    · have hbr' : 1 < y.toNat := by omega
      have hl : Nat.log2 y.toNat = Nat.log2 (y.toNat / 2) + 1 := by
        rw [Nat.log2_def]; simp; omega
      have hy2 : (y >>> 1).toNat = y.toNat / 2 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
      refine Reaches.mono (ih (y >>> 1) (c + 1#64) _ (by rw [hy2]; rw [Nat.pow_succ] at hy; omega)
        (by rw [hy2, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega) (by rfl)
        (by simp [setRegF]) (by simp [setRegF]) rfl
        (by simpa [setRegF] using hsp) (by simpa [setRegF] using hra)) ?_
      intro o ho
      cases o with
      | stub _ _ _ => exact ho.elim
      | returned t' =>
        simp only [isReturn_returned, setRegF] at ho ⊢
        obtain ⟨e0, e4, e5, e14, e15⟩ := ho
        exact ⟨e0, by simpa using e4, by simpa using e5, by simpa using e14, e15⟩
    · rw [← hc, Nat.log2_def]; simp; omega

theorem correctness (x : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x] 1
      (fun s => StackWritable s 0 8)
      (fun res => ∃ r, res = [r] ∧ ((x.toNat = 0 ∧ r.toNat = 0) ∨
        (2 ^ r.toNat ≤ x.toNat ∧ x.toNat < 2 ^ (r.toNat + 1)))) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run until [loopHead]
  refine Reaches.mono (loop x ret hret _ 64 x 0 _ x.isLt (by simp) (by rfl)
    (by simp [setRegF, h_a0]) (by simp [setRegF]) rfl
    (by simpa [setRegF] using accessible_sub hacc (by decide) (Nat.le_refl _) (Nat.le_refl _))
    (by simpa [setRegF] using h_ret)) ?_
  intro o ho
  cases o with
  | stub _ _ _ => exact ho.elim
  | returned t' =>
    simp only [isReturn_returned, setRegF] at ho ⊢
    obtain ⟨e0, e4, e5, e14, e15⟩ := ho
    refine ⟨⟨by simpa using e4, by simpa using e5, by simpa using e14, by simpa using e15⟩, ?_⟩
    simp only [results, intArgRegs, List.take, List.map]
    refine ⟨_, rfl, ?_⟩
    rw [e0]
    by_cases h : x.toNat = 0
    · left; rw [h]; exact ⟨rfl, rfl⟩
    · right; exact (Nat.log2_eq_iff h).1 rfl

end Proof
