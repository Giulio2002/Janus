import Janus
import Extracted

/-! `example.com/basic.GotoSum(n uint64) uint64` on amd64: a loop built from labels and `goto`.

For every 64-bit `n` the call returns (so the `goto` loop terminates) with
`RAX = (1 + 2 + … + n) mod 2^64 = n·(n+1)/2 mod 2^64`.

```
XORL CX, CX ; XORL DX, DX ; JMP head
body: LEAQ 0(CX)(DX*1), DX ; LEAQ 1(DX), DX ; INCQ CX      ; s += i + 1; i++
head: CMPQ AX, CX ; JA body                                 ; n > i (unsigned)
MOVQ DX, AX ; RET
```

`loop` is the invariant at the head (after `i` iterations the sum is `i·(i+1)/2 mod 2^64`),
proved by induction on the `n - i` iterations left. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- The loop head (`CMPQ AX, CX`). -/
def loopHead : Nat := Extracted.entry + 0x11

/-- `(i+1)(i+2)/2 = i(i+1)/2 + (i+1)`. -/
theorem tri_succ (i : Nat) : (i + 1) * (i + 1 + 1) / 2 = i * (i + 1) / 2 + (i + 1) := by
  have : (i + 1) * (i + 1 + 1) = i * (i + 1) + 2 * (i + 1) := by janus_ring
  rw [this, Nat.add_mul_div_left _ _ (by decide)]

theorem loop (n : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (m : Memory) :
    ∀ k (i acc : BitVec 64) (t : State), i.toNat + k = n.toNat →
      t.rip = BitVec.ofNat 64 loopHead → t.regs 0 = n → t.regs 1 = i → t.regs 2 = acc →
      acc.toNat = i.toNat * (i.toNat + 1) / 2 % 2 ^ 64 →
      t.mem = m → m.accessible (t.regs 4).toNat 8 false = true →
      m.readLE (t.regs 4).toNat 8 = ret →
      Reaches (Extracted.program.withExit ret) t (IsReturn fun t' =>
        (t'.regs 0).toNat = n.toNat * (n.toNat + 1) / 2 % 2 ^ 64 ∧ t'.regs 4 = t.regs 4 + 8 ∧
        t'.regs 5 = t.regs 5 ∧ t'.regs 14 = t.regs 14 ∧ t'.xmm 15 = t.xmm 15) := by
  intro k
  induction k
  case zero =>
    intro i acc t hk h_rip h0 h1 h2 hacc hmem hsp hra
    simp only [loopHead] at h_rip
    janus64_run
    rw [hacc, show i.toNat = n.toNat by omega]
  case succ k ih =>
    intro i acc t hk h_rip h0 h1 h2 hacc hmem hsp hra
    simp only [loopHead] at h_rip
    janus64_run until [loopHead]
    refine Reaches.mono (ih (i + 1#64) (i + acc + 1#64) _ (by simp; omega) (by rfl)
      (by simp [setRegF, h0]) (by simp [setRegF]) (by simp [setRegF]) ?_ rfl
      (by simpa [setRegF] using hsp) (by simpa [setRegF] using hra)) ?_
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [show (i.toNat + 1 % 2 ^ 64) % 2 ^ 64 = i.toNat + 1 by omega, tri_succ]
      omega
    · intro o ho
      cases o with
      | stub _ _ _ => exact ho.elim
      | returned t' =>
        simp only [isReturn_returned, setRegF] at ho ⊢
        obtain ⟨e0, e4, e5, e14, e15⟩ := ho
        exact ⟨e0, by simpa using e4, by simpa using e5, by simpa using e14, e15⟩

theorem correctness (n : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [n] 1
      (fun s => StackWritable s 0 8)
      (fun r => ∃ v, r = [v] ∧ v.toNat = n.toNat * (n.toNat + 1) / 2 % 2 ^ 64) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run until [loopHead]
  refine Reaches.mono (loop n ret hret _ n.toNat 0 0 _ (by simp) (by rfl)
    (by simp [setRegF, h_a0]) (by simp [setRegF]) (by simp [setRegF]) (by simp) rfl
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
    exact ⟨_, rfl, e0⟩

end Proof
