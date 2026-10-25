import Extracted

/-!
# `uint64_t c_sum(const uint64_t *p, uint64_t n)` (C, arm64): the sum of `n` words, a loop

**Guarantee.** For every pointer `p` and count `n` such that the `8·n` bytes at `p` are readable
(and below `2^48`), every AAPCS64 call of the gcc-compiled `c_sum` returns without faulting,
restores `SP` and `X19`–`X29`, and leaves `(p[0] + … + p[n-1]) mod 2^64` in `X0`, where `p[k]` is
the word at `p + 8k`. Memory is not changed. This holds for every `n`: the loop terminates.

**How.** gcc compiles the loop to a pointer walk: `x2` runs from `p` to `x1 = p + 8n`
(`ldr x3, [x2], #8; add x0, x0, x3; cmp x2, x1; b.ne`). `loop` is the invariant at the loop
head, by induction on the iterations left; `summary` is the callee contract the cgo wrapper
uses (`CSumW`), and `correctness` follows from it by `CEnsures.of_summary`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.Spec Janus.FFI

namespace Proof

/-- The loop head `ldr x3, [x2], #8`. -/
abbrev head : Nat := Extracted.entry + 0x18

/-- What `c_sum` guarantees to a caller: `SP`, `X19`–`X29` and memory unchanged, the sum in
`X0` (stated as plain equations, so that a caller's `janus_run` can use them). -/
abbrev SumPost (p n : BitVec 64) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 19 = s.regs 19 ∧ s'.regs 20 = s.regs 20 ∧ s'.regs 21 = s.regs 21 ∧
    s'.regs 22 = s.regs 22 ∧ s'.regs 23 = s.regs 23 ∧ s'.regs 24 = s.regs 24 ∧
    s'.regs 25 = s.regs 25 ∧ s'.regs 26 = s.regs 26 ∧ s'.regs 27 = s.regs 27 ∧
    s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.fpcr = s.fpcr ∧ s'.vregs = s.vregs ∧
    s'.mem = s.mem ∧
    (s'.regs 0).toNat = sumWords s.mem p.toNat n.toNat % 2 ^ 64

/-- The precondition of the summary: the buffer, and a return address `RET` can branch to. -/
abbrev SumPre (p n : BitVec 64) (s : State) : Prop :=
  s.regs 0 = p ∧ s.regs 1 = n ∧ p.toNat + 8 * n.toNat ≤ 2 ^ 48 ∧
    s.mem.accessible p.toNat (8 * n.toNat) false = true ∧
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56

/-- `S` agrees with `s` on everything `c_sum` must keep: `SP`, memory, `X19`–`X30`, `FPCR`. -/
abbrev Kept (s S : State) : Prop :=
  S.sp = s.sp ∧ S.mem = s.mem ∧ S.regs 19 = s.regs 19 ∧ S.regs 20 = s.regs 20 ∧
    S.regs 21 = s.regs 21 ∧ S.regs 22 = s.regs 22 ∧ S.regs 23 = s.regs 23 ∧
    S.regs 24 = s.regs 24 ∧ S.regs 25 = s.regs 25 ∧ S.regs 26 = s.regs 26 ∧
    S.regs 27 = s.regs 27 ∧ S.regs 28 = s.regs 28 ∧ S.regs 29 = s.regs 29 ∧
    S.regs 30 = s.regs 30 ∧ S.fpcr = s.fpcr ∧ S.vregs = s.vregs

/-- The loop invariant at `head`, after `i` of the `n` iterations: `X2 = p + 8i`, `X1 = p + 8n`,
`X0` the sum of the first `i` words. -/
theorem loop (p n : BitVec 64) (s : State) (hpre : SumPre p n s) :
    ∀ k (S : State) (i acc : BitVec 64), i.toNat + (k + 1) = n.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = acc →
      S.regs 1 = BitVec.ofNat 64 (p.toNat + 8 * n.toNat) →
      S.regs 2 = BitVec.ofNat 64 (p.toNat + 8 * i.toNat) → Kept s S →
      acc.toNat = sumWords s.mem p.toNat i.toNat % 2 ^ 64 →
      ReachesRet Extracted.program (s.regs 30) S (SumPost p n s) := by
  obtain ⟨h0, h1, hb, hacc, hal, htag⟩ := hpre
  intro k
  induction k with
  | zero =>
    intro S i acc hk hpc hS0 hS1 hS2 ⟨hsp, hm, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, hfc, hv⟩ hs
    janus_run
    janus_simp [SumPost, sumWords_succ, show n.toNat = i.toNat + 1 by omega, hfc, hv]
    omega
  | succ k ih =>
    intro S i acc hk hpc hS0 hS1 hS2 ⟨hsp, hm, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, hfc, hv⟩ hs
    janus_run until [head]
    have hi : (i + 1#64).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    apply ih _ (i + 1#64) _ (by omega) (by janus_simp) rfl (by janus_simp) ?_
      (by simp only [Kept]; janus_simp [hfc, hv])
      (by janus_simp [sumWords_succ, hi]; omega)
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

/-- The callee contract of `c_sum`, used by the cgo wrapper's proof. -/
theorem summary (p n : BitVec 64) :
    Summary Extracted.program Extracted.entry (SumPre p n) (SumPost p n) := by
  intro s hpc hpre
  have hpre' := hpre
  obtain ⟨h0, h1, hb, hacc, hal, htag⟩ := hpre
  janus_run until [head]
  · janus_simp [SumPost, sumWords_zero]
  · have he : p + n <<< 3 = BitVec.ofNat 64 (p.toNat + 8 * n.toNat) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    exact loop p n s hpre' (n.toNat - 1) _ 0#64 0#64 (by simp; omega) (by janus_simp)
      (by janus_simp) (by janus_simp [he]) (by janus_simp) (by simp only [Kept]; janus_simp)
      (by simp)

theorem correctness (p n : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [p, n]
      (fun s => p.toNat + 8 * n.toNat ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat (8 * n.toNat) false = true)
      (fun s s' => (s'.regs 0).toNat = sumWords s.mem p.toNat n.toNat % 2 ^ 64 ∧ s'.mem = s.mem) :=
  CEnsures.of_summary (summary p n)
    (fun ret s hret hs ⟨hb, hacc⟩ => by
      have h0 := hs.call.reg (i := 0) (by simp)
      have h1 := hs.call.reg (i := 1) (by simp)
      have hlr := hs.call.lr
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, Program.withExit] at h0 h1 hlr
      refine ⟨h0, h1, hb, hacc, ?_, ?_⟩ <;> rw [hlr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hret.lt64]
      · exact hret.aligned
      · have := hret.user; omega)
    (fun s s' _ h => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hv, h14, h15⟩ := h
      exact ⟨CReturn.of_eqs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hv, h15, h14⟩)

end Proof
