import Extracted

/-!
# `uint32_t c_dot32(const uint32_t *a, const uint32_t *b, uint64_t n)` (C, amd64, clang -O3 -march=x86-64-v3): an AVX2 dot product

**Guarantee.** For all pointers `a`, `b` and every count `n` such that the `4·n` bytes at `a` and
at `b` are readable (and below `2^48`), every System V call of the clang-compiled `c_dot32`
returns without faulting, restores `RSP + 8`, `RBX RBP R12–R15`, the direction flag and `MXCSR`,
leaves memory unchanged and returns `(a[0]·b[0] + … + a[n-1]·b[n-1]) mod 2^32` in `EAX`
(zero-extended into `RAX`), where `a[k]` is the 32-bit word at `a + 4k` (`dot32`).

**The code.** clang vectorises the loop with AVX2 at three granularities: for `n ≥ 32`, 32
products per iteration (`vmovdqu (%rsi,%rax,4),%ymm4; vpmulld (%rdi,%rax,4),%ymm4,%ymm4;
vpaddd %ymm0,%ymm4,%ymm0`, four times) into four YMM accumulators, so that lane `j` of `YMMr`
holds the sum of the products `32i + 8r + j`; a reduction (`vpaddd` of the accumulators,
`vextracti128 $1`, `vpshufd $0xee`/`$0x55`, `vmovd`); then, if at least 4 words remain, the
epilogue on XMM (`vmovd %eax,%xmm0` — a VEX.128 write that zeroes the rest of `YMM0` — then 4
products per iteration with `vpmulld`/`vpaddd` on XMM and the same reduction); finally a scalar
loop (`imul`/`add`) for the last `n mod 4` words, and `vzeroupper`.

**How.** `tail` (the scalar loop), `eloop`/`eexit` (the XMM epilogue, invariant `EAcc`),
`vloop`/`vexit` (the YMM loop, invariant `Acc`: 32 lanes as `dotStride` sums), `afterRed`
(the three exits of the reduction), each by induction on the iterations left; the lane sums are
regrouped into the dot product by `dot32_split` and `dot32_shift`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Amd64.FFI Janus.Spec
open Janus.Arm64 (elem ofElems)

namespace Proof

/-- The scalar loop head `cmp %rcx,%rdx`. -/
abbrev tailHead : Nat := Extracted.entry + 0x110

/-- The XMM epilogue loop head `vmovdqu (%rsi,%r8,4),%xmm1`. -/
abbrev epiHead : Nat := Extracted.entry + 0xd0

/-- The YMM loop head `vmovdqu (%rsi,%rax,4),%ymm4`. -/
abbrev vecHead : Nat := Extracted.entry + 0x40

/-- After the YMM loop: `vpaddd %ymm0,%ymm1,%ymm0`. -/
abbrev exitHead : Nat := Extracted.entry + 0x8b

/-- After the YMM reduction (`vmovd %xmm0,%eax`): `cmp %rcx,%rdx`. -/
abbrev redHead : Nat := Extracted.entry + 0xb7

/-- After the XMM epilogue loop: `vpshufd $0xee,%xmm0,%xmm1`. -/
abbrev eexitHead : Nat := Extracted.entry + 0xe9

/-- What `c_dot32` guarantees to a caller. -/
abbrev DotPost (p q n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 3 = s.regs 3 ∧ s'.regs 5 = s.regs 5 ∧
    s'.regs 12 = s.regs 12 ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧
    s'.regs 15 = s.regs 15 ∧ s'.df = false ∧ s'.mxcsr = s.mxcsr ∧ s'.mem = s.mem ∧
    (s'.regs 0).toNat = dot32 s.mem p.toNat q.toNat n.toNat % 2 ^ 32

/-- The precondition: the arguments, the two buffers, and the return address slot. -/
abbrev DotPre (p q n : BitVec 64) (s : State) : Prop :=
  s.regs 7 = p ∧ s.regs 6 = q ∧ s.regs 2 = n ∧ p.toNat + 4 * n.toNat ≤ 2 ^ 48 ∧
    q.toNat + 4 * n.toNat ≤ 2 ^ 48 ∧
    s.mem.accessible p.toNat (4 * n.toNat) false = true ∧
    s.mem.accessible q.toNat (4 * n.toNat) false = true ∧
    (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 4).toNat 8 false = true ∧
    s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.df = false

/-- `S` agrees with `s` on everything `c_dot32` must keep. -/
abbrev Kept (s S : State) : Prop :=
  S.regs 4 = s.regs 4 ∧ S.mem = s.mem ∧ S.regs 3 = s.regs 3 ∧ S.regs 5 = s.regs 5 ∧
    S.regs 12 = s.regs 12 ∧ S.regs 13 = s.regs 13 ∧ S.regs 14 = s.regs 14 ∧
    S.regs 15 = s.regs 15 ∧ S.df = s.df ∧ S.mxcsr = s.mxcsr ∧ S.regs 7 = s.regs 7 ∧
    S.regs 6 = s.regs 6 ∧ S.regs 2 = s.regs 2

/-- The scalar loop: at `tailHead` with `i` words done and `k` left. -/
theorem tail (p q n : BitVec 64) (s : State) (hpre : DotPre p q n s) :
    ∀ k (S : State) (i : Nat), i + k = n.toNat →
      S.rip = BitVec.ofNat 64 tailHead → S.regs 1 = BitVec.ofNat 64 i → Kept s S →
      (S.regs 0).toNat = dot32 s.mem p.toNat q.toNat i % 2 ^ 32 →
      ReachesRet Extracted.program (retAddrOf s) S (DotPost p q n s) := by
  obtain ⟨h7, h6, h2, hbp, hbq, haccp, haccq, hsb, hsa, hra, hdf0⟩ := hpre
  have hn : n.toNat < 2 ^ 64 := n.isLt
  intro k
  induction k with
  | zero =>
    intro S i hk hpc hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hS7, hS6, hS2⟩ hs
    have hi : i = n.toNat := by omega
    subst hi
    janus64_run
    janus64_simp [DotPost]
    simpa using hs
  | succ k ih =>
    intro S i hk hpc hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hS7, hS6, hS2⟩ hs
    janus64_run until [tailHead]
    apply ih _ (i + 1) (by omega) (by janus64_simp) ?_ (by simp only [Kept]; janus64_simp) ?_
    · janus64_simp
    · janus64_simp [dot32_succ]
      simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd, Nat.mul_mod_mod, Nat.mod_mul_mod]
      rw [Nat.mul_comm i 4, hs]
      have hA : s.mem.readLE (p.toNat + 4 * i) 4 < 2 ^ 32 := Janus.Arm64.Memory.readLE_lt _ _ _
      have hB : s.mem.readLE (q.toNat + 4 * i) 4 < 2 ^ 32 := Janus.Arm64.Memory.readLE_lt _ _ _
      generalize s.mem.readLE (p.toNat + 4 * i) 4 = A at hA ⊢
      generalize s.mem.readLE (q.toNat + 4 * i) 4 = B at hB ⊢
      have e : B % 2 ^ 32 % 2 ^ 64 = B := by omega
      rw [e, Nat.mul_comm B A]
      generalize A * B = x
      omega


/-- One lane step of the accumulators. -/
theorem lane_step (A B D : Nat) :
    (B * A % 4294967296 + D % 4294967296) % 4294967296 = (D + A * B) % 4294967296 := by
  rw [Nat.mul_comm B A]; generalize A * B = x; omega

/-- The four accumulators after `k` vector iterations: lane `j` of `YMMr` (`r < 4`) is the sum of
the products of the words `32i + 8r + j` (`i < k`), modulo `2^32`. -/
abbrev Acc (m : Memory) (p q k : Nat) (S : State) : Prop :=
  ∀ j, j < 8 → elem (S.ymm 0) 32 j = dotStride m p q 32 j k % 2 ^ 32 ∧
    elem (S.ymm 1) 32 j = dotStride m p q 32 (8 + j) k % 2 ^ 32 ∧
    elem (S.ymm 2) 32 j = dotStride m p q 32 (16 + j) k % 2 ^ 32 ∧
    elem (S.ymm 3) 32 j = dotStride m p q 32 (24 + j) k % 2 ^ 32

/-- `n AND -2^k` rounds down to a multiple of `2^k`. -/
theorem and_neg_pow (x k : Nat) (h : x < 2 ^ 64) (hk : k ≤ 64) :
    x &&& (2 ^ 64 - 2 ^ k) = 2 ^ k * (x / 2 ^ k) := by
  have e : (2 ^ 64 - 2 ^ k : Nat) = (2 ^ (64 - k) - 1) * 2 ^ k := by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel hk]
  rw [e, Nat.mul_comm (2 ^ k)]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hi : k ≤ i
  · have : i - k + k = i := by omega
    rw [this]
    by_cases h64 : i < 64
    · simp [hi, show i - k < 64 - k by omega]
    · have : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [hi]

theorem and_neg4 (n : BitVec 64) : n &&& 18446744073709551612#64 = BitVec.ofNat 64 (4 * (n.toNat / 4)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (18446744073709551612 : Nat) % 2 ^ 64 = 2 ^ 64 - 2 ^ 2 by decide, and_neg_pow _ 2 n.isLt (by decide)]
  have := n.isLt; omega

theorem and_neg32 (n : BitVec 64) : n &&& 18446744073709551584#64 = BitVec.ofNat 64 (32 * (n.toNat / 32)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (18446744073709551584 : Nat) % 2 ^ 64 = 2 ^ 64 - 2 ^ 5 by decide, and_neg_pow _ 5 n.isLt (by decide)]
  have := n.isLt; omega

/-- `test $0x1c,%dl`: bits 4:2 of `n` are clear iff `n mod 32 < 4`. -/
theorem and_1c (x : Nat) : x % 256 &&& 28 = 4 * (x % 32 / 4) := by
  have key : ∀ y, y < 256 → y &&& 28 = 4 * (y % 32 / 4) := by decide +kernel
  rw [key _ (Nat.mod_lt _ (by decide)), Nat.mod_mod_of_dvd _ (by decide)]

theorem dot32_shift (m : Memory) (a b c k : Nat) :
    dot32 m a b (c + k) = dot32 m a b c + dot32 m (a + 4 * c) (b + 4 * c) k := by
  rw [dot32_add, show dot32 m (a + 4 * c) (b + 4 * c) k = dot32 m (a + 4 * c) (b + 4 * c) (0 + k) by rw [Nat.zero_add],
    dot32_add, dot32_zero, Nat.zero_add]
  congr 1
  apply sumN_congr; intro j _
  rw [show a + 4 * (c + j) = a + 4 * c + 4 * (0 + j) by omega, show b + 4 * (c + j) = b + 4 * c + 4 * (0 + j) by omega]

/-- `test $0x1c,%dl` as a statement about `n`. -/
theorem test1c (n : BitVec 64) : (BitVec.setWidth 8 n &&& 28#8 = 0#8) ↔ n.toNat % 32 < 4 := by
  have hk := and_1c n.toNat
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.zero_mod] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.zero_mod]
    omega

/-- A value below `2^32` has zero 32-bit elements above element 0. -/
theorem elem_small (x i : Nat) (hx : x < 2 ^ 32) (hi : 1 ≤ i) : elem x 32 i = 0 := by
  unfold elem
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]

/-- The epilogue's accumulator `XMM0` after `t` iterations from word `c`: lane 0 also holds the
dot product of the first `c` words. -/
abbrev EAcc (m : Memory) (p q c t : Nat) (x : W128) : Prop :=
  elem x.toNat 32 0 = (dot32 m p q c + dotStride m (p + 4 * c) (q + 4 * c) 4 0 t) % 2 ^ 32 ∧
  elem x.toNat 32 1 = dotStride m (p + 4 * c) (q + 4 * c) 4 1 t % 2 ^ 32 ∧
  elem x.toNat 32 2 = dotStride m (p + 4 * c) (q + 4 * c) 4 2 t % 2 ^ 32 ∧
  elem x.toNat 32 3 = dotStride m (p + 4 * c) (q + 4 * c) 4 3 t % 2 ^ 32

theorem lane_step0 (A B C D : Nat) :
    (B * A % 4294967296 + (C + D) % 4294967296) % 4294967296 = (C + (D + A * B)) % 4294967296 := by
  rw [Nat.mul_comm B A]; generalize A * B = x; omega

set_option maxHeartbeats 4000000 in
/-- After the epilogue loop: the reduction, then the scalar loop from word `4·(n / 4)`. -/
theorem eexit (p q n : BitVec 64) (s : State) (hpre : DotPre p q n s) (c T : Nat)
    (hcT : c + 4 * T = 4 * (n.toNat / 4)) :
    ∀ (S : State), S.rip = BitVec.ofNat 64 eexitHead →
      S.regs 1 = BitVec.ofNat 64 (4 * (n.toNat / 4)) → Kept s S →
      EAcc s.mem p.toNat q.toNat c T (S.xmm 0) →
      ReachesRet Extracted.program (retAddrOf s) S (DotPost p q n s) := by
  have hpre' := hpre
  obtain ⟨h7, h6, h2, hbp, hbq, haccp, haccq, hsb, hsa, hra, hdf0⟩ := hpre
  have hn : n.toNat < 2 ^ 64 := n.isLt
  intro S hpc hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hS7, hS6, hS2⟩ ⟨l0, l1, l2, l3⟩
  janus64_run until [tailHead]
  apply tail p q n s hpre' (n.toNat - 4 * (n.toNat / 4)) _ (4 * (n.toNat / 4)) (by omega) (by janus64_simp)
    (by janus64_simp) (by simp only [Kept]; janus64_simp)
  janus64_simp
  rw [← elem_32_zero]
  janus64_simp
  rw [l0, l1, l2, l3, ← hcT, dot32_shift, dot32_split]
  simp only [ExecSSE.sumN, Nat.zero_add]
  omega

set_option maxHeartbeats 4000000 in
/-- The epilogue loop: at `epiHead` with `t` iterations from word `c` done. -/
theorem eloop (p q n : BitVec 64) (s : State) (hpre : DotPre p q n s) (c : Nat) :
    ∀ jj (S : State) (t : Nat), c + 4 * (t + jj + 1) = 4 * (n.toNat / 4) →
      S.rip = BitVec.ofNat 64 epiHead → S.regs 8 = BitVec.ofNat 64 (c + 4 * t) →
      S.regs 1 = BitVec.ofNat 64 (4 * (n.toNat / 4)) → Kept s S →
      EAcc s.mem p.toNat q.toNat c t (S.xmm 0) →
      ReachesRet Extracted.program (retAddrOf s) S (DotPost p q n s) := by
  have hpre' := hpre
  obtain ⟨h7, h6, h2, hbp, hbq, haccp, haccq, hsb, hsa, hra, hdf0⟩ := hpre
  have hn : n.toNat < 2 ^ 64 := n.isLt
  have e0 : ∀ b t, b + (c + 4 * t) * 4 = b + 4 * c + 4 * (4 * t) := by intro b t; omega
  have e1 : ∀ b t, b + (c + 4 * t) * 4 + 4 = b + 4 * c + 4 * (4 * t + 1) := by intro b t; omega
  have e2 : ∀ b t, b + (c + 4 * t) * 4 + 8 = b + 4 * c + 4 * (4 * t + 2) := by intro b t; omega
  have e3 : ∀ b t, b + (c + 4 * t) * 4 + 12 = b + 4 * c + 4 * (4 * t + 3) := by intro b t; omega
  intro jj
  induction jj with
  | zero =>
    intro S t ht hpc hS8 hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hS7, hS6, hS2⟩ ⟨l0, l1, l2, l3⟩
    janus64_run until [eexitHead]
    apply eexit p q n s hpre' c (t + 1) (by omega) _ (by janus64_simp) (by janus64_simp)
      (by simp only [Kept]; janus64_simp)
    simp only [EAcc]
    janus64_simp [dotStride]
    rw [l0, l1, l2, l3, e1, e1, e2, e2, e3, e3, e0, e0]
    exact ⟨lane_step0 _ _ _ _, lane_step _ _ _, lane_step _ _ _, lane_step _ _ _⟩
  | succ jj ih =>
    intro S t ht hpc hS8 hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hS7, hS6, hS2⟩ ⟨l0, l1, l2, l3⟩
    janus64_run until [epiHead]
    apply ih _ (t + 1) (by omega) (by janus64_simp) ?_ (by janus64_simp) (by simp only [Kept]; janus64_simp) ?_
    · janus64_simp
      apply BitVec.eq_of_toNat_eq; simp; omega
    · simp only [EAcc]
      janus64_simp [dotStride]
      rw [l0, l1, l2, l3, e1, e1, e2, e2, e3, e3, e0, e0]
      exact ⟨lane_step0 _ _ _ _, lane_step _ _ _, lane_step _ _ _, lane_step _ _ _⟩

set_option maxHeartbeats 4000000 in
/-- After the reduction of the vector accumulators (`EAX` = the dot product of the first
`32·(n / 32)` words): the return, the scalar loop or the epilogue. -/
theorem afterRed (p q n : BitVec 64) (s : State) (hpre : DotPre p q n s) :
    ∀ (S : State), S.rip = BitVec.ofNat 64 redHead →
      S.regs 1 = BitVec.ofNat 64 (32 * (n.toNat / 32)) → 1 ≤ n.toNat / 32 → Kept s S →
      (S.regs 0).toNat = dot32 s.mem p.toNat q.toNat (32 * (n.toNat / 32)) % 2 ^ 32 →
      ReachesRet Extracted.program (retAddrOf s) S (DotPost p q n s) := by
  have hpre' := hpre
  obtain ⟨h7, h6, h2, hbp, hbq, haccp, haccq, hsb, hsa, hra, hdf0⟩ := hpre
  have hn : n.toNat < 2 ^ 64 := n.isLt
  intro S hpc hS1 hq ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hS7, hS6, hS2⟩ hs
  janus64_run until [epiHead, tailHead]
  · janus64_simp [DotPost]
    rename_i hbr0
    have : n.toNat = 32 * (n.toNat / 32) := by omega
    rw [hs, ← this]
  · rename_i hbr0
    rw [test1c] at hbr
    apply tail p q n s hpre' (n.toNat - (32 * (n.toNat / 32) + 1)) _ (32 * (n.toNat / 32) + 1) (by omega)
      (by janus64_simp) (by janus64_simp) (by simp only [Kept]; janus64_simp)
    janus64_simp [dot32_succ]
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mul_mod_mod, Nat.mod_mul_mod]
    rw [Nat.mul_comm (32 * (n.toNat / 32)) 4, hs]
    have hA : s.mem.readLE (p.toNat + 4 * (32 * (n.toNat / 32))) 4 < 2 ^ 32 := Janus.Arm64.Memory.readLE_lt _ _ _
    have hB : s.mem.readLE (q.toNat + 4 * (32 * (n.toNat / 32))) 4 < 2 ^ 32 := Janus.Arm64.Memory.readLE_lt _ _ _
    generalize s.mem.readLE (p.toNat + 4 * (32 * (n.toNat / 32))) 4 = A at hA ⊢
    generalize s.mem.readLE (q.toNat + 4 * (32 * (n.toNat / 32))) 4 = B at hB ⊢
    have e : B % 2 ^ 32 % 2 ^ 64 = B := by omega
    rw [e, Nat.mul_comm B A]
    generalize A * B = x
    omega
  · rename_i hbr0
    rw [test1c] at hbr
    apply eloop p q n s hpre' (32 * (n.toNat / 32)) ((4 * (n.toNat / 4) - 32 * (n.toNat / 32)) / 4 - 1) _ 0
      (by omega) (by janus64_simp) (by janus64_simp) (by janus64_simp [and_neg4]) (by simp only [Kept]; janus64_simp)
    simp only [EAcc]
    janus64_simp [dotStride]
    have h0 : BitVec.toNat (S.regs 0) % 4294967296 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    refine ⟨?_, elem_small _ _ h0 (by decide), elem_small _ _ h0 (by decide), elem_small _ _ h0 (by decide)⟩
    rw [elem_32_zero, hs]; omega

set_option maxHeartbeats 4000000 in
/-- After the vector loop (`n / 32 ≥ 1` iterations): the reduction. -/
theorem vexit (p q n : BitVec 64) (s : State) (hpre : DotPre p q n s) :
    ∀ (S : State), S.rip = BitVec.ofNat 64 exitHead →
      S.regs 1 = BitVec.ofNat 64 (32 * (n.toNat / 32)) → 1 ≤ n.toNat / 32 → Kept s S →
      Acc s.mem p.toNat q.toNat (n.toNat / 32) S →
      ReachesRet Extracted.program (retAddrOf s) S (DotPost p q n s) := by
  have hpre' := hpre
  obtain ⟨h7, h6, h2, hbp, hbq, haccp, haccq, hsb, hsa, hra, hdf0⟩ := hpre
  have hn : n.toNat < 2 ^ 64 := n.isLt
  intro S hpc hS1 hq ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hS7, hS6, hS2⟩ hacc'
  janus64_run until [redHead]
  apply afterRed p q n s hpre' _ (by janus64_simp) (by janus64_simp) hq (by simp only [Kept]; janus64_simp)
  janus64_simp
  rw [← elem_32_zero]
  janus64_simp
  obtain ⟨a00, a10, a20, a30⟩ := hacc' 0 (by decide)
  obtain ⟨a01, a11, a21, a31⟩ := hacc' 1 (by decide)
  obtain ⟨a02, a12, a22, a32⟩ := hacc' 2 (by decide)
  obtain ⟨a03, a13, a23, a33⟩ := hacc' 3 (by decide)
  obtain ⟨a04, a14, a24, a34⟩ := hacc' 4 (by decide)
  obtain ⟨a05, a15, a25, a35⟩ := hacc' 5 (by decide)
  obtain ⟨a06, a16, a26, a36⟩ := hacc' 6 (by decide)
  obtain ⟨a07, a17, a27, a37⟩ := hacc' 7 (by decide)
  simp only [State.ymm, Nat.reduceAdd] at a00 a10 a20 a30 a01 a11 a21 a31 a02 a12 a22 a32 a03 a13 a23 a33 a04 a14 a24 a34 a05 a15 a25 a35 a06 a16 a26 a36 a07 a17 a27 a37
  rw [a00, a10, a20, a30, a01, a11, a21, a31, a02, a12, a22, a32, a03, a13, a23, a33, a04, a14, a24, a34, a05, a15, a25, a35, a06, a16, a26, a36, a07, a17, a27, a37, dot32_split]
  simp only [ExecSSE.sumN, Nat.zero_add]
  omega

set_option maxHeartbeats 4000000 in
/-- The vector loop: at `vecHead` with `k` of the `n / 32` iterations done (`k < n / 32`). -/
theorem vloop (p q n : BitVec 64) (s : State) (hpre : DotPre p q n s) :
    ∀ jj (S : State) (k : Nat), k + (jj + 1) = n.toNat / 32 →
      S.rip = BitVec.ofNat 64 vecHead → S.regs 0 = BitVec.ofNat 64 (32 * k) →
      S.regs 1 = BitVec.ofNat 64 (32 * (n.toNat / 32)) → Kept s S →
      Acc s.mem p.toNat q.toNat k S →
      ReachesRet Extracted.program (retAddrOf s) S (DotPost p q n s) := by
  have hpre' := hpre
  obtain ⟨h7, h6, h2, hbp, hbq, haccp, haccq, hsb, hsa, hra, hdf0⟩ := hpre
  have hn : n.toNat < 2 ^ 64 := n.isLt
  intro jj
  induction jj with
  | zero =>
    intro S k hk hpc hS0 hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hS7, hS6, hS2⟩ hacc'
    janus64_run until [exitHead]
    apply vexit p q n s hpre' _ (by janus64_simp) (by janus64_simp) (by omega) (by simp only [Kept]; janus64_simp)
    rw [← hk]
    intro j hj
    obtain ⟨a0, a1, a2, a3⟩ := hacc' j hj
    simp only [State.ymm] at a0 a1 a2 a3
    janus64_simp [dotStride, State.ymm]
    rw [a0, a1, a2, a3]
    have e1 : ∀ b, b + 32 * k * 4 + 32 + 4 * j = b + 4 * (32 * k + (8 + j)) := by intro b; omega
    have e2 : ∀ b, b + 32 * k * 4 + 64 + 4 * j = b + 4 * (32 * k + (16 + j)) := by intro b; omega
    have e3 : ∀ b, b + 32 * k * 4 + 96 + 4 * j = b + 4 * (32 * k + (24 + j)) := by intro b; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show q.toNat + 32 * k * 4 + 4 * j = q.toNat + 4 * (32 * k + j) by omega,
        show p.toNat + 32 * k * 4 + 4 * j = p.toNat + 4 * (32 * k + j) by omega]
      exact lane_step _ _ _
    · rw [e1, e1]; exact lane_step _ _ _
    · rw [e2, e2]; exact lane_step _ _ _
    · rw [e3, e3]; exact lane_step _ _ _
  | succ jj ih =>
    intro S k hk hpc hS0 hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hS7, hS6, hS2⟩ hacc'
    janus64_run until [vecHead]
    apply ih _ (k + 1) (by omega) (by janus64_simp) ?_ (by janus64_simp) (by simp only [Kept]; janus64_simp) ?_
    · janus64_simp
      apply BitVec.eq_of_toNat_eq; simp; omega
    · intro j hj
      obtain ⟨a0, a1, a2, a3⟩ := hacc' j hj
      simp only [State.ymm] at a0 a1 a2 a3
      janus64_simp [dotStride, State.ymm]
      rw [a0, a1, a2, a3]
      have e1 : ∀ b, b + 32 * k * 4 + 32 + 4 * j = b + 4 * (32 * k + (8 + j)) := by intro b; omega
      have e2 : ∀ b, b + 32 * k * 4 + 64 + 4 * j = b + 4 * (32 * k + (16 + j)) := by intro b; omega
      have e3 : ∀ b, b + 32 * k * 4 + 96 + 4 * j = b + 4 * (32 * k + (24 + j)) := by intro b; omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show q.toNat + 32 * k * 4 + 4 * j = q.toNat + 4 * (32 * k + j) by omega,
          show p.toNat + 32 * k * 4 + 4 * j = p.toNat + 4 * (32 * k + j) by omega]
        exact lane_step _ _ _
      · rw [e1, e1]; exact lane_step _ _ _
      · rw [e2, e2]; exact lane_step _ _ _
      · rw [e3, e3]; exact lane_step _ _ _

theorem summary (p q n : BitVec 64) :
    Summary Extracted.program Extracted.entry (DotPre p q n) (DotPost p q n) := by
  intro s hpc hpre
  have hpre' := hpre
  obtain ⟨h7, h6, h2, hbp, hbq, haccp, haccq, hsb, hsa, hra, hdf0⟩ := hpre
  have hn : n.toNat < 2 ^ 64 := n.isLt
  janus64_run until [vecHead, epiHead, tailHead]
  · janus64_simp [DotPost, dot32_zero]
  · -- 4 ≤ n < 32: the epilogue from word 0
    apply eloop p q n s hpre' 0 (n.toNat / 4 - 1) _ 0 (by omega) (by janus64_simp) (by janus64_simp)
      (by janus64_simp [and_neg4]) (by simp only [Kept]; janus64_simp)
    simp only [EAcc]
    janus64_simp [dotStride, dot32_zero]
  · -- 32 ≤ n: the vector loop
    apply vloop p q n s hpre' (n.toNat / 32 - 1) _ 0 (by omega) (by janus64_simp) (by janus64_simp)
      (by janus64_simp [and_neg32]) (by simp only [Kept]; janus64_simp)
    intro j hj
    simp [State.ymm, ymmJoin, elem, dotStride, setXmmF]
  · -- 1 ≤ n ≤ 3: the scalar loop
    apply tail p q n s hpre' (n.toNat - 1) _ 1 (by omega) (by janus64_simp) (by janus64_simp)
      (by simp only [Kept]; janus64_simp)
    janus64_simp [dot32_succ, dot32_zero]
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mul_mod_mod, Nat.mod_mul_mod]
    have hA : s.mem.readLE p.toNat 4 < 2 ^ 32 := Janus.Arm64.Memory.readLE_lt _ _ _
    have hB : s.mem.readLE q.toNat 4 < 2 ^ 32 := Janus.Arm64.Memory.readLE_lt _ _ _
    generalize s.mem.readLE p.toNat 4 = A at hA ⊢
    generalize s.mem.readLE q.toNat 4 = B at hB ⊢
    have e : B % 2 ^ 32 % 2 ^ 64 = B := by omega
    rw [e, Nat.mul_comm B A]
    generalize A * B = x
    omega

/-- **`c_dot32`.** -/
theorem correctness (p q n : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [p, q, n]
      (fun s => CStack s 0 8 ∧ p.toNat + 4 * n.toNat ≤ 2 ^ 48 ∧ q.toNat + 4 * n.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible p.toNat (4 * n.toNat) false = true ∧
        s.mem.accessible q.toNat (4 * n.toNat) false = true)
      (fun s s' => (s'.regs 0).toNat = dot32 s.mem p.toNat q.toNat n.toNat % 2 ^ 32 ∧ s'.mem = s.mem) :=
  CEnsures.of_summary (summary p q n)
    (fun ret s hret hs ⟨⟨_, _, hnw, hst⟩, hbp, hbq, haccp, haccq⟩ => by
      have h0 : s.regs 7 = p := hs.reg (i := 0) (by simp)
      have h1 : s.regs 6 = q := hs.reg (i := 1) (by simp)
      have h2 : s.regs 2 = n := hs.reg (i := 2) (by simp)
      have hr := hs.ret
      simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add, Program.withExit] at hst hnw hr
      exact ⟨h0, h1, h2, hbp, hbq, haccp, haccq, hnw, Janus.Arm64.Memory.accessible_weaken _ hst,
        by rw [hr]; exact hret.user, hs.df⟩)
    (fun s s' _ h => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
      exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, by rw [h9]⟩, h11, h10⟩)

end Proof
