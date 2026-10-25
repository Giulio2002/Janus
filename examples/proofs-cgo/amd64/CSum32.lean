import Extracted

/-!
# `int32_t c_sum32(const int32_t *p, uint64_t n)` (C, amd64, clang -O2): a vectorised sum

**Guarantee.** For every pointer `p` and count `n` such that the `4·n` bytes at `p` are readable
(and below `2^48`), every System V call of the clang-compiled `c_sum32` returns without faulting,
restores `RSP + 8`, `RBX RBP R12–R15`, the direction flag and `MXCSR`, leaves memory unchanged
and returns `(p[0] + … + p[n-1]) mod 2^32` in `EAX` (zero-extended into `RAX`), where `p[k]` is
the 32-bit word at `p + 4k`.

**The code.** clang vectorises the loop with SSE2. For `n ≥ 8` it adds 8 words per iteration
into two accumulators (`movdqu (%rdi,%rax,4),%xmm2; paddd %xmm2,%xmm0; movdqu
0x10(%rdi,%rax,4),%xmm2; paddd %xmm2,%xmm1`), so that lane `j` of `XMM0` (`XMM1`) holds the sum
of the words `8i + j` (`8i + 4 + j`); then it adds the two accumulators and folds the four lanes
with `pshufd $0xee`/`paddd`/`pshufd $0x55`/`paddd`, takes lane 0 with `movd`, and finishes the
`n mod 8` remaining words in a scalar loop (`add (%rdi,%rcx,4),%eax`).

**How.** `tail` is the scalar loop (by induction on the words left), `vloop` the vector loop
(by induction on the iterations left; the invariant states the eight lanes as `sumStride`
sums), and `sum32_eight` regroups the lanes into the plain sum.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Amd64.FFI Janus.Spec
open Janus.Arm64 (elem ofElems)

namespace Proof

/-- The scalar loop head `cmp %rcx,%rsi`. -/
abbrev tailHead : Nat := Extracted.entry + 0x6e

/-- The vector loop head `movdqu (%rdi,%rax,4),%xmm2`. -/
abbrev vecHead : Nat := Extracted.entry + 0x30

/-- What `c_sum32` guarantees to a caller. -/
abbrev SumPost (p n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 3 = s.regs 3 ∧ s'.regs 5 = s.regs 5 ∧
    s'.regs 12 = s.regs 12 ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧
    s'.regs 15 = s.regs 15 ∧ s'.df = false ∧ s'.mxcsr = s.mxcsr ∧ s'.fpucw = s.fpucw ∧
    s'.mem = s.mem ∧
    (s'.regs 0).toNat = sum32 s.mem p.toNat n.toNat % 2 ^ 32

/-- The precondition: the arguments, the buffer, and the return address slot. -/
abbrev SumPre (p n : BitVec 64) (s : State) : Prop :=
  s.regs 7 = p ∧ s.regs 6 = n ∧ p.toNat + 4 * n.toNat ≤ 2 ^ 48 ∧
    s.mem.accessible p.toNat (4 * n.toNat) false = true ∧
    (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 4).toNat 8 false = true ∧
    s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.df = false

/-- `S` agrees with `s` on everything `c_sum32` must keep. -/
abbrev Kept (s S : State) : Prop :=
  S.regs 4 = s.regs 4 ∧ S.mem = s.mem ∧ S.regs 3 = s.regs 3 ∧ S.regs 5 = s.regs 5 ∧
    S.regs 12 = s.regs 12 ∧ S.regs 13 = s.regs 13 ∧ S.regs 14 = s.regs 14 ∧
    S.regs 15 = s.regs 15 ∧ S.df = s.df ∧ S.mxcsr = s.mxcsr ∧ S.fpucw = s.fpucw ∧ S.regs 7 = s.regs 7 ∧
    S.regs 6 = s.regs 6

/-- The scalar loop: at `tailHead` with `i` words done and `k` left. -/
theorem tail (p n : BitVec 64) (s : State) (hpre : SumPre p n s) :
    ∀ k (S : State) (i : Nat), i + k = n.toNat →
      S.rip = BitVec.ofNat 64 tailHead → S.regs 1 = BitVec.ofNat 64 i → Kept s S →
      (S.regs 0).toNat = sum32 s.mem p.toNat i % 2 ^ 32 →
      ReachesRet Extracted.program (retAddrOf s) S (SumPost p n s) := by
  obtain ⟨h7, h6, hb, hacc, hsb, hsa, hra, hdf0⟩ := hpre
  have hn : n.toNat < 2 ^ 64 := n.isLt
  intro k
  induction k with
  | zero =>
    intro S i hk hpc hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hfw, hS7, hS6⟩ hs
    have hi : i = n.toNat := by omega
    subst hi
    janus64_run
    janus64_simp [SumPost, hfw]
    simpa using hs
  | succ k ih =>
    intro S i hk hpc hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hfw, hS7, hS6⟩ hs
    janus64_run until [tailHead]
    apply ih _ (i + 1) (by omega) (by janus64_simp) ?_ (by simp only [Kept]; janus64_simp [hfw]) ?_
    · janus64_simp
    · janus64_simp [sum32_succ]
      rw [Nat.mul_comm i 4]
      omega

/-- The accumulators after `k` vector iterations: lane `j` of `XMM0` is the sum of the words
`8i + j`, lane `j` of `XMM1` that of the words `8i + 4 + j` (`i < k`), modulo `2^32`. -/
abbrev Acc (m : Memory) (p k : Nat) (x0 x1 : W128) : Prop :=
  elem x0.toNat 32 0 = sumStride m p 8 0 k % 2 ^ 32 ∧ elem x0.toNat 32 1 = sumStride m p 8 1 k % 2 ^ 32 ∧
  elem x0.toNat 32 2 = sumStride m p 8 2 k % 2 ^ 32 ∧ elem x0.toNat 32 3 = sumStride m p 8 3 k % 2 ^ 32 ∧
  elem x1.toNat 32 0 = sumStride m p 8 4 k % 2 ^ 32 ∧ elem x1.toNat 32 1 = sumStride m p 8 5 k % 2 ^ 32 ∧
  elem x1.toNat 32 2 = sumStride m p 8 6 k % 2 ^ 32 ∧ elem x1.toNat 32 3 = sumStride m p 8 7 k % 2 ^ 32

set_option maxHeartbeats 4000000 in
/-- The vector loop: at `vecHead` with `k` of the `q = n / 8` iterations done (`k < q`). -/
theorem vloop (p n : BitVec 64) (s : State) (hpre : SumPre p n s) :
    ∀ j (S : State) (k : Nat), k + (j + 1) = n.toNat / 8 →
      S.rip = BitVec.ofNat 64 vecHead → S.regs 0 = BitVec.ofNat 64 (8 * k) →
      S.regs 1 = BitVec.ofNat 64 (8 * (n.toNat / 8)) → Kept s S →
      Acc s.mem p.toNat k (S.xmm 0) (S.xmm 1) →
      ReachesRet Extracted.program (retAddrOf s) S (SumPost p n s) := by
  have hpre' := hpre
  obtain ⟨h7, h6, hb, hacc, hsb, hsa, hra, hdf0⟩ := hpre
  have hn : n.toNat < 2 ^ 64 := n.isLt
  intro j
  induction j with
  | zero =>
    intro S k hk hpc hS0 hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hfw, hS7, hS6⟩ hacc'
    janus64_run until [tailHead]
    obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩ := hacc'
    apply tail p n s hpre' (n.toNat - 8 * (k + 1)) _ (8 * (k + 1)) (by omega) (by janus64_simp)
      (by janus64_simp; rw [hk]) (by simp only [Kept]; janus64_simp [hfw])
    janus64_simp
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, sum32_add8, sum32_eight, ← elem_32_zero]
    janus64_simp
    rw [show p.toNat + 4 * (8 * k) = p.toNat + 8 * k * 4 by omega,
      show p.toNat + 4 * (8 * k + 1) = p.toNat + 8 * k * 4 + 4 by omega,
      show p.toNat + 4 * (8 * k + 2) = p.toNat + 8 * k * 4 + 8 by omega,
      show p.toNat + 4 * (8 * k + 3) = p.toNat + 8 * k * 4 + 12 by omega,
      show p.toNat + 4 * (8 * k + 4) = p.toNat + 8 * k * 4 + 16 by omega,
      show p.toNat + 4 * (8 * k + 5) = p.toNat + 8 * k * 4 + 16 + 4 by omega,
      show p.toNat + 4 * (8 * k + 6) = p.toNat + 8 * k * 4 + 16 + 8 by omega,
      show p.toNat + 4 * (8 * k + 7) = p.toNat + 8 * k * 4 + 16 + 12 by omega]
    omega
  | succ j ih =>
    intro S k hk hpc hS0 hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hfw, hS7, hS6⟩ hacc'
    janus64_run until [vecHead]
    apply ih _ (k + 1) (by omega) (by janus64_simp) ?_ (by janus64_simp) (by simp only [Kept]; janus64_simp [hfw]) ?_
    · janus64_simp
      apply BitVec.eq_of_toNat_eq; simp; omega
    · obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩ := hacc'
      simp only [Acc]
      janus64_simp [sumStride]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show p.toNat + 4 * (8 * k) = p.toNat + 8 * k * 4 by omega]; omega
      · rw [show p.toNat + 4 * (8 * k + 1) = p.toNat + 8 * k * 4 + 4 by omega]; omega
      · rw [show p.toNat + 4 * (8 * k + 2) = p.toNat + 8 * k * 4 + 8 by omega]; omega
      · rw [show p.toNat + 4 * (8 * k + 3) = p.toNat + 8 * k * 4 + 12 by omega]; omega
      · rw [show p.toNat + 4 * (8 * k + 4) = p.toNat + 8 * k * 4 + 16 by omega]; omega
      · rw [show p.toNat + 4 * (8 * k + 5) = p.toNat + 8 * k * 4 + 16 + 4 by omega]; omega
      · rw [show p.toNat + 4 * (8 * k + 6) = p.toNat + 8 * k * 4 + 16 + 8 by omega]; omega
      · rw [show p.toNat + 4 * (8 * k + 7) = p.toNat + 8 * k * 4 + 16 + 12 by omega]; omega

theorem and_neg8_nat (x : Nat) (h : x < 2 ^ 64) : x &&& (2 ^ 64 - 8) = 8 * (x / 8) := by
  have e : (2 ^ 64 - 8 : Nat) = (2 ^ 61 - 1) * 2 ^ 3 := by decide
  rw [e, show 8 * (x / 8) = x / 2 ^ 3 * 2 ^ 3 by rw [Nat.mul_comm]]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases h3 : 3 ≤ i
  · have : i - 3 + 3 = i := by omega
    rw [this]
    by_cases h64 : i < 64
    · simp [h3, show i - 3 < 61 by omega]
    · have : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [h3]

/-- `n AND -8` (`and $0xfffffffffffffff8,%rcx`) rounds down to a multiple of 8. -/
theorem and_neg8 (n : BitVec 64) :
    n &&& 18446744073709551608#64 = BitVec.ofNat 64 (8 * (n.toNat / 8)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (18446744073709551608 : Nat) % 2 ^ 64 = 2 ^ 64 - 8 by decide, and_neg8_nat _ n.isLt]
  have := n.isLt
  omega

/-- The callee contract of `c_sum32`. -/
theorem summary (p n : BitVec 64) :
    Summary Extracted.program Extracted.entry (SumPre p n) (SumPost p n) := by
  intro s hpc hpre
  have hpre' := hpre
  obtain ⟨h7, h6, hb, hacc, hsb, hsa, hra, hdf0⟩ := hpre
  have hn : n.toNat < 2 ^ 64 := n.isLt
  janus64_run until [vecHead, tailHead]
  · janus64_simp [SumPost, sum32_zero]
  · apply tail p n s hpre' (n.toNat - 1) _ 1 (by omega) (by janus64_simp) (by janus64_simp)
      (by simp only [Kept]; janus64_simp)
    have e1 : sum32 s.mem p.toNat 1 = s.mem.readLE p.toNat 4 := by simp [sum32, sumStride]
    janus64_simp [e1]
  · apply vloop p n s hpre' (n.toNat / 8 - 1) _ 0 (by omega) (by janus64_simp) (by janus64_simp)
      (by janus64_simp [and_neg8]) (by simp only [Kept]; janus64_simp)
    simp only [Acc]
    janus64_simp [sumStride]

/-- **`c_sum32`.** -/
theorem correctness (p n : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [p, n]
      (fun s => CStack s 0 8 ∧ p.toNat + 4 * n.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible p.toNat (4 * n.toNat) false = true)
      (fun s s' => (s'.regs 0).toNat = sum32 s.mem p.toNat n.toNat % 2 ^ 32 ∧ s'.mem = s.mem) :=
  CEnsures.of_summary (summary p n)
    (fun ret s hret hs ⟨⟨_, _, hnw, hst⟩, hb, hacc⟩ => by
      have h0 : s.regs 7 = p := hs.reg (i := 0) (by simp)
      have h1 : s.regs 6 = n := hs.reg (i := 1) (by simp)
      have hr := hs.ret
      simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add, Program.withExit] at hst hnw hr
      exact ⟨h0, h1, hb, hacc, hnw, Janus.Arm64.Memory.accessible_weaken _ hst,
        by rw [hr]; exact hret.user, hs.df⟩)
    (fun s s' _ h => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hfw, h10, h11⟩ := h
      exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, by rw [h9], hfw⟩, h11, h10⟩)

end Proof
