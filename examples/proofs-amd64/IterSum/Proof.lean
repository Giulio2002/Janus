import Janus
import Extracted

/-! `example.com/basic.IterSum(n int) uint64` on amd64: range over a function iterator.

For every 64-bit `n`, read as a signed `int`, the call returns with
`RAX = (0 + 1 + … + (N-1)) mod 2^64 = N·(N-1)/2 mod 2^64` where `N = max(n, 0)`: the iterator
`upTo(n)` yields `0, 1, …, n-1`. The compiler inlines `upTo`, its closure and the `yield`
callback and removes the range-over-func state checks, so the code is a plain counting loop
(`ADDQ CX, DX; INCQ CX; CMPQ AX, CX; JG`) with no call into the runtime. `loop` is the invariant
at its head, proved by induction on the `N - i` iterations left. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- The loop head (`CMPQ AX, CX; JG body`). -/
def loopHead : Nat := Extracted.entry + 0xd

/-- `(i+1)·i/2 = i(i-1)/2 + i`. -/
theorem tri_succ (i : Nat) : (i + 1) * i / 2 = i * (i - 1) / 2 + i := by
  rcases i with _ | j
  · rfl
  · have : (j + 1 + 1) * (j + 1) = (j + 1) * (j + 1 - 1) + 2 * (j + 1) := by
      simp only [Nat.add_sub_cancel]; janus_ring
    rw [this, Nat.add_mul_div_left _ _ (by decide)]

theorem toInt_of_lt (i : BitVec 64) (h : i.toNat < 2 ^ 63) : i.toInt = i.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]; simp; omega

theorem loop (n : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (m : Memory) :
    ∀ k (i acc : BitVec 64) (t : State), i.toNat + k = n.toInt.toNat →
      t.rip = BitVec.ofNat 64 loopHead → t.regs 0 = n → t.regs 1 = i → t.regs 2 = acc →
      acc.toNat = i.toNat * (i.toNat - 1) / 2 % 2 ^ 64 →
      t.mem = m → m.accessible (t.regs 4).toNat 8 false = true →
      m.readLE (t.regs 4).toNat 8 = ret →
      Reaches (Extracted.program.withExit ret) t (IsReturn fun t' =>
        (t'.regs 0).toNat = n.toInt.toNat * (n.toInt.toNat - 1) / 2 % 2 ^ 64 ∧ t'.regs 4 = t.regs 4 + 8 ∧
        t'.regs 5 = t.regs 5 ∧ t'.regs 14 = t.regs 14 ∧ t'.xmm 15 = t.xmm 15) := by
  have hn := BitVec.toInt_lt (x := n)
  simp only [Nat.add_one_sub_one] at hn
  intro k
  induction k
  case zero =>
    intro i acc t hk h_rip h0 h1 h2 hacc hmem hsp hra
    have hi : i.toInt = i.toNat := toInt_of_lt i (by omega)
    simp only [loopHead] at h_rip
    janus64_run
    rw [hacc, show i.toNat = n.toInt.toNat by omega]
  case succ k ih =>
    intro i acc t hk h_rip h0 h1 h2 hacc hmem hsp hra
    have hi : i.toInt = i.toNat := toInt_of_lt i (by omega)
    simp only [loopHead] at h_rip
    janus64_run until [loopHead]
    refine Reaches.mono (ih (i + 1#64) (acc + i) _ (by simp; omega) (by rfl)
      (by simp [setRegF, h0]) (by simp [setRegF]) (by simp [setRegF]) ?_ rfl
      (by simpa [setRegF] using hsp) (by simpa [setRegF] using hra)) ?_
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [show (i.toNat + 1 % 2 ^ 64) % 2 ^ 64 = i.toNat + 1 by omega, Nat.add_sub_cancel, tri_succ]
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
      (fun r => ∃ v, r = [v] ∧ v.toNat = n.toInt.toNat * (n.toInt.toNat - 1) / 2 % 2 ^ 64) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run until [loopHead]
  refine Reaches.mono (loop n ret hret _ n.toInt.toNat 0 0 _ (by simp) (by rfl)
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
