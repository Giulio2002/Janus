import Extracted

/-!
# `uint64_t c_sum(const uint64_t *p, uint64_t n)` (C, amd64): the sum of `n` words, a loop

**Guarantee.** For every pointer `p` and count `n` such that the `8·n` bytes at `p` are readable
(and below `2^48`), every System V call of the gcc-compiled `c_sum` (return address readable at
`[RSP]`) returns without faulting, restores `RSP + 8`, `RBX RBP R12–R15` and the direction flag,
and leaves `(p[0] + … + p[n-1]) mod 2^64` in `RAX`, where `p[k]` is the word at `p + 8k`. Memory
is not changed. This holds for every `n`: the loop terminates.

**How.** gcc compiles the loop to a pointer walk: `RDI` runs from `p` to `RDX = p + 8n`
(`add (%rdi),%rax; add $8,%rdi; cmp %rdx,%rdi; jne`). `loop` is the invariant at the loop head,
by induction on the iterations left; `summary` is the callee contract the cgo wrapper uses, and
`correctness` follows from it by `CEnsures.of_summary`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Amd64.FFI Janus.Spec

namespace Proof

/-- The loop head `add (%rdi),%rax`. -/
abbrev head : Nat := Extracted.entry + 0x10

/-- What `c_sum` guarantees to a caller, as plain equations. -/
abbrev SumPost (p n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 3 = s.regs 3 ∧ s'.regs 5 = s.regs 5 ∧
    s'.regs 12 = s.regs 12 ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧
    s'.regs 15 = s.regs 15 ∧ s'.df = false ∧ s'.mem = s.mem ∧
    (s'.regs 0).toNat = sumWords s.mem p.toNat n.toNat % 2 ^ 64

/-- The precondition of the summary: the arguments, the buffer, and the return address slot. -/
abbrev SumPre (p n : BitVec 64) (s : State) : Prop :=
  s.regs 7 = p ∧ s.regs 6 = n ∧ p.toNat + 8 * n.toNat ≤ 2 ^ 48 ∧
    s.mem.accessible p.toNat (8 * n.toNat) false = true ∧
    (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 4).toNat 8 false = true ∧
    s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.df = false

/-- `S` agrees with `s` on everything `c_sum` must keep. -/
abbrev Kept (s S : State) : Prop :=
  S.regs 4 = s.regs 4 ∧ S.mem = s.mem ∧ S.regs 3 = s.regs 3 ∧ S.regs 5 = s.regs 5 ∧
    S.regs 12 = s.regs 12 ∧ S.regs 13 = s.regs 13 ∧ S.regs 14 = s.regs 14 ∧
    S.regs 15 = s.regs 15 ∧ S.df = s.df

/-- The loop invariant at `head` after `i` of the `n` iterations. -/
theorem loop (p n : BitVec 64) (s : State) (hpre : SumPre p n s) :
    ∀ k (S : State) (i acc : BitVec 64), i.toNat + (k + 1) = n.toNat →
      S.rip = BitVec.ofNat 64 head → S.regs 0 = acc →
      S.regs 2 = BitVec.ofNat 64 (p.toNat + 8 * n.toNat) →
      S.regs 7 = BitVec.ofNat 64 (p.toNat + 8 * i.toNat) → Kept s S →
      acc.toNat = sumWords s.mem p.toNat i.toNat % 2 ^ 64 →
      ReachesRet Extracted.program (retAddrOf s) S (SumPost p n s) := by
  obtain ⟨h7, h6, hb, hacc, hsb, hsa, hra, hdf0⟩ := hpre
  intro k
  induction k with
  | zero =>
    intro S i acc hk hpc hS0 hS2 hS7 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf⟩ hs
    janus64_run
    janus64_simp [SumPost, sumWords_succ, show n.toNat = i.toNat + 1 by omega]
    omega
  | succ k ih =>
    intro S i acc hk hpc hS0 hS2 hS7 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf⟩ hs
    janus64_run until [head]
    have hi : (i + 1#64).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    apply ih _ (i + 1#64) _ (by omega) (by janus64_simp) rfl (by janus64_simp) ?_
      (by simp only [Kept]; janus64_simp) (by janus64_simp [sumWords_succ, hi]; omega)
    · janus64_simp
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, hi]; omega

/-- The callee contract of `c_sum`, used by the cgo wrapper's proof. -/
theorem summary (p n : BitVec 64) :
    Summary Extracted.program Extracted.entry (SumPre p n) (SumPost p n) := by
  intro s hpc hpre
  have hpre' := hpre
  obtain ⟨h7, h6, hb, hacc, hsb, hsa, hra, hdf0⟩ := hpre
  janus64_run until [head]
  · janus64_simp [SumPost, sumWords_zero]
  · have he : p + n <<< 3 = BitVec.ofNat 64 (p.toNat + 8 * n.toNat) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    exact loop p n s hpre' (n.toNat - 1) _ 0#64 0#64 (by simp; omega) (by janus64_simp)
      (by janus64_simp) (by janus64_simp [he]) (by janus64_simp) (by simp only [Kept]; janus64_simp)
      (by simp)

theorem correctness (p n : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [p, n]
      (fun s => CStack s 0 8 ∧ p.toNat + 8 * n.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible p.toNat (8 * n.toNat) false = true)
      (fun s s' => (s'.regs 0).toNat = sumWords s.mem p.toNat n.toNat % 2 ^ 64 ∧ s'.mem = s.mem) :=
  CEnsures.of_summary (summary p n)
    (fun ret s hret hs ⟨⟨_, _, hnw, hst⟩, hb, hacc⟩ => by
      have h0 : s.regs 7 = p := hs.reg (i := 0) (by simp)
      have h1 : s.regs 6 = n := hs.reg (i := 1) (by simp)
      have hr := hs.ret
      simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add, Program.withExit] at hst hnw hr
      exact ⟨h0, h1, hb, hacc, hnw, Janus.Arm64.Memory.accessible_weaken _ hst,
        by rw [hr]; exact hret.user, hs.df⟩)
    (fun s s' _ h => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
      exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, h10, h9⟩)

end Proof
