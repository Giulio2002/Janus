import Extracted

/-!
# `Dot32(a, b []uint32) uint32` (Go) → `c_dot32` (C, AVX2 by clang -O3 -march=x86-64-v3) → back to Go (amd64)

```go
func Dot32(a, b []uint32) uint32 {
	if len(a) == 0 || len(b) < len(a) {
		return 0
	}
	return uint32(C.c_dot32((*C.uint32_t)(unsafe.Pointer(&a[0])), (*C.uint32_t)(unsafe.Pointer(&b[0])), C.uint64_t(len(a))))
}
```

The C side (`examples/cgo/avx/cavx.c`, compiled with the package's `#cgo CFLAGS: -O3
-march=x86-64-v3` by clang 21.1.8, `CC=clang`) is the AVX2 loop of `CDot32.lean`: 32 `VPMULLD`
products per iteration into four YMM accumulators, an XMM epilogue, a scalar tail.

**Guarantee (`correctness`).** For all slice headers `(pa, la, ca)`, `(pb, lb, cb)` and every Go
call of `example.com/cgo/avx.Dot32` satisfying `GoPre pa la pb lb` — the stack checks fall
through, the stack window (and the argument spill slots above the return address) is writable,
the TLS `g` slot holds `g`, the `4·la` bytes at `pa` and the `4·lb` bytes at `pb` are readable,
below `2^48` and away from the stack window, the `g` struct and the TLS slot; and the cgo globals
hold their static values — every run returns and leaves `0` in `EAX` if `len(b) < len(a)`, and
otherwise `(a[0]·b[0] + … + a[la-1]·b[la-1]) mod 2^32`, for all lengths.

The statement is under the trusted `CgoCall Extracted.program` only: `Dot32`, `_Cfunc_c_dot32`,
the C wrapper and the vectorised C loop are executed by the model.

**How.** `cdot_summary` is the callee contract of `c_dot32` (the proof of `CDot32.lean`);
`wrapper_spec` uses it at the wrapper's `call c_dot32`; `go_spec` is `Dot32` under
`CgoSpec wrapper G E`; `refines` and `correctness` compose them as in `GoSum32.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Spec
  Janus.Amd64.FFI
open Janus.Arm64 (elem ofElems)

namespace Proof

/-! ## The C function `c_dot32` (as in `CDot32.lean`), as a callee summary -/

abbrev cdot : Nat := segAddr Extracted.program "c_dot32"

/-- The scalar loop head `cmp %rcx,%rdx`. -/
abbrev tailHead : Nat := cdot + 0x110

/-- The XMM epilogue loop head `vmovdqu (%rsi,%r8,4),%xmm1`. -/
abbrev epiHead : Nat := cdot + 0xd0

/-- The YMM loop head `vmovdqu (%rsi,%rax,4),%ymm4`. -/
abbrev vecHead : Nat := cdot + 0x40

/-- After the YMM loop: `vpaddd %ymm0,%ymm1,%ymm0`. -/
abbrev exitHead : Nat := cdot + 0x8b

/-- After the YMM reduction (`vmovd %xmm0,%eax`): `cmp %rcx,%rdx`. -/
abbrev redHead : Nat := cdot + 0xb7

/-- After the XMM epilogue loop: `vpshufd $0xee,%xmm0,%xmm1`. -/
abbrev eexitHead : Nat := cdot + 0xe9

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

theorem cdot_summary (p q n : BitVec 64) :
    Summary Extracted.program cdot (DotPre p q n) (DotPost p q n) := by
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

/-- The dot product of `n` words at `a` and `b` is the same in two memories that agree outside
`rs`. -/
theorem dot32_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) (a b : Nat) :
    ∀ n, Outside a (4 * n) rs → Outside b (4 * n) rs → dot32 m' a b n = dot32 m a b n
  | 0, _, _ => rfl
  | n + 1, ha, hb => by
    rw [dot32_succ, dot32_succ,
      dot32_frame h a b n (Outside.of_sub ha (Nat.le_refl _) (by omega)) (Outside.of_sub hb (Nat.le_refl _) (by omega)),
      h.readLE _ _ (Outside.of_sub ha (by omega) (by omega)), h.readLE _ _ (Outside.of_sub hb (by omega) (by omega))]

theorem dot32_congr {m m' : Memory} (a b : Nat) :
    ∀ n, (∀ i, i < n → m'.readLE (a + 4 * i) 4 = m.readLE (a + 4 * i) 4) →
      (∀ i, i < n → m'.readLE (b + 4 * i) 4 = m.readLE (b + 4 * i) 4) →
      dot32 m' a b n = dot32 m a b n
  | 0, _, _ => rfl
  | n + 1, ha, hb => by
    rw [dot32_succ, dot32_succ, dot32_congr a b n (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)),
      ha n (by omega), hb n (by omega)]

theorem writeLE_mod_4 (m : Memory) (a v : Nat) :
    m.writeLE a 4 (v % 4294967296) = m.writeLE a 4 v :=
  Janus.Arm64.Memory.writeLE_mod m a 4 v

/-- The same store, of equal values, on both sides keeps a frame. -/
theorem frame_store {m m' : Memory} {rs : List (Nat × Nat)} {a v v' : Nat} (h : MemFrame m m' rs)
    (hv : v' % 4294967296 = v % 4294967296) : MemFrame (m.writeLE a 4 v) (m'.writeLE a 4 v') rs := by
  rw [← writeLE_mod_4 m, ← writeLE_mod_4 m', hv]; exact h.writeLE_both a 4 _

/-! ## The cgo wrapper -/

abbrev wrapper : Nat := segAddr Extracted.program "_cgo_69258bfe59ad_Cfunc_c_dot32"

/-- The two pointers and the count in the cgo frame at `a`. -/
abbrev frameA (m : Memory) (a : Nat) : Nat := m.readLE a 8
abbrev frameB (m : Memory) (a : Nat) : Nat := m.readLE (a + 8) 8
abbrev frameN (m : Memory) (a : Nat) : Nat := m.readLE (a + 16) 8

def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 8 ∧ a.toNat + 32 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 32 true = true ∧
    (a.toNat + 32 ≤ (t.regs 4).toNat - 4096 ∨ (t.regs 4).toNat + 8 ≤ a.toNat) ∧
    frameA t.mem a.toNat + 4 * frameN t.mem a.toNat ≤ 2 ^ 48 ∧
    t.mem.accessible (frameA t.mem a.toNat) (4 * frameN t.mem a.toNat) false = true ∧
    (frameA t.mem a.toNat + 4 * frameN t.mem a.toNat ≤ (t.regs 4).toNat - 4096 ∨
      (t.regs 4).toNat + 8 ≤ frameA t.mem a.toNat) ∧
    frameB t.mem a.toNat + 4 * frameN t.mem a.toNat ≤ 2 ^ 48 ∧
    t.mem.accessible (frameB t.mem a.toNat) (4 * frameN t.mem a.toNat) false = true ∧
    (frameB t.mem a.toNat + 4 * frameN t.mem a.toNat ≤ (t.regs 4).toNat - 4096 ∨
      (t.regs 4).toNat + 8 ≤ frameB t.mem a.toNat)

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 24) 4
      (dot32 t.mem (frameA t.mem a.toNat) (frameB t.mem a.toNat) (frameN t.mem a.toNat) % 2 ^ 32)) t'.mem
    [((t.regs 4).toNat - 4096, (t.regs 4).toNat)]

theorem wrapper_spec (T a : BitVec 64) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd, hpb, hpa, hpd, hqb, hqa, hqd⟩
  apply ReturnsC.of_reaches
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : t.regs 7 = a := hs.reg (i := 0) (by simp)
  simp only [Amd64.Program.withExit] at h_ret
  simp only [CABI.regSP, frameA, frameB, frameN] at hal hb htop hacc hpb hpa hpd hqb hqa hqd
  have h32 : (t.regs 4 - 32#64).toNat = (t.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h32]; omega
  · janus64_simp [h32]; janus64_disch
  rintro s₁ ⟨-, f₁, rfl⟩
  apply ReturnsC.of_reaches
  janus64_run calls [cdot_summary (BitVec.ofNat 64 (t.mem.readLE a.toNat 8))
    (BitVec.ofNat 64 (t.mem.readLE (a.toNat + 8) 8)) (BitVec.ofNat 64 (t.mem.readLE (a.toNat + 16) 8))]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h32]; omega
  · janus64_simp [h32]; janus64_disch
  rintro s₂ ⟨-, f₂, rfl⟩
  apply ReturnsC.of_reaches
  janus64_run
  simp only [WPost, frameA, frameB, frameN, Nat.reducePow]
  apply frame_store
  · janus_frame
  · rename_i hsum
    rw [hsum, Nat.mod_mod, dot32_frame (rs := [((t.regs 4).toNat - 4096, (t.regs 4).toNat)]) ?hf _ _ _ ?ho ?ho2]
    · janus_frame
    · simp only [outside_cons, outside_nil, and_true]; omega
    · simp only [outside_cons, outside_nil, and_true]; omega

/-! ## The Go side: `Dot32` → `_Cfunc_c_dot32` → `runtime.cgocall` -/

def fnVar : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/avx._Cfunc_c_dot32.abi0" + 0x2d)

def alwaysFalse : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/avx._Cfunc_c_dot32.abi0" + 0x46)

/-- At the `cgocall`: the frame `RBX` and the two buffers it points at are Go memory the runtime
leaves alone. -/
def G (s : State) : Prop :=
  (s.regs 3).toNat + 32 ≤ 2 ^ 48 ∧ GoKept s (s.regs 3).toNat 32 true ∧
    frameA s.mem (s.regs 3).toNat + 4 * frameN s.mem (s.regs 3).toNat ≤ 2 ^ 48 ∧
    GoKept s (frameA s.mem (s.regs 3).toNat) (4 * frameN s.mem (s.regs 3).toNat) false ∧
    frameB s.mem (s.regs 3).toNat + 4 * frameN s.mem (s.regs 3).toNat ≤ 2 ^ 48 ∧
    GoKept s (frameB s.mem (s.regs 3).toNat) (4 * frameN s.mem (s.regs 3).toNat) false

def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 3).toNat + 24) 4
    (dot32 s.mem (frameA s.mem (s.regs 3).toNat) (frameB s.mem (s.regs 3).toNat)
      (frameN s.mem (s.regs 3).toNat) % 2 ^ 32)

/-- The Go caller's obligations. -/
def GoPre (pa la pb lb : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 48 ∧ StackWritable s 88 40 ∧ TlsG s ∧
  pa.toNat + 4 * la.toNat ≤ 2 ^ 48 ∧ s.mem.accessible pa.toNat (4 * la.toNat) false = true ∧
  pb.toNat + 4 * lb.toNat ≤ 2 ^ 48 ∧ s.mem.accessible pb.toNat (4 * lb.toNat) false = true ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 = 0 ∧
  Outside (s.regs 14).toNat 456 [((s.regs 4).toNat - 88, (s.regs 4).toNat + 40)] ∧
  Outside (s.fsBase.toNat - 8) 8 [((s.regs 4).toNat - 88, (s.regs 4).toNat + 40)] ∧
  Outside fnVar 8 [((s.regs 4).toNat - 88, (s.regs 4).toNat + 40)] ∧
  Outside alwaysFalse 1 [((s.regs 4).toNat - 1112, (s.regs 4).toNat + 40),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)] ∧
  Outside pa.toNat (4 * la.toNat) [((s.regs 4).toNat - 1112, (s.regs 4).toNat + 40),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)] ∧
  Outside pb.toNat (4 * lb.toNat) [((s.regs 4).toNat - 1112, (s.regs 4).toNat + 40),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)]

/-- What `Dot32` returns. -/
abbrev DotRes (pa la pb lb : BitVec 64) (s : State) : Nat :=
  if lb.toNat < la.toNat then 0 else dot32 s.mem pa.toNat pb.toNat la.toNat % 2 ^ 32

set_option maxHeartbeats 8000000 in
theorem go_spec (pa la ca pb lb cb : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [pa, la, ca, pb, lb, cb]
      (GoPre pa la pb lb) (fun s s' => (s'.regs 0).toNat = DotRes pa la pb lb s) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, htop, hst⟩, ⟨hfs, hfsr, hfsg⟩, hpb, hpa, hqb, hqa, hfa, hfv, haa,
    hav, hdg, hdt, hdf, hda, hdp, hdq⟩
  apply ReturnsC.of_reaches
  janus64_intro hs
  janus_eval_nat h_fv : fnVar
  janus_eval_nat h_af : alwaysFalse
  rw [h_fv] at hfa hfv hdf
  rw [h_af] at haa hav hda
  simp only [outside_cons, outside_nil, and_true, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG, stackguard0, stackguard0Offset] at *
  have hfsa : (s.fsBase + BitVec.ofNat 64 18446744073709551608).toNat = s.fsBase.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h32 : (s.regs 4 - 32#64).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h80 : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run [hfsa]
  · simp [DotRes, hbr, dot32_zero]
  rotate_left
  · rename_i hnz hlt
    simp only [DotRes]
    rw [if_pos (by omega)]
  rename_i hnz hle
  refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
  · simp only [G, GoKept, frameA, frameB, frameN, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
      cgoStackScratch, gStructSize, outside_cons, outside_nil, and_true]
    janus64_simp [h32, h80]
    repeat' apply And.intro
    all_goals try omega
    · janus64_disch
    · exact Janus.Arm64.Memory.accessible_sub _ hqa (Or.inl rfl) (Nat.le_refl _) (by omega)
  rintro s' ⟨-, m, ⟨regs, fl, xm, yh, fs, mx, zh, kr, rfl, h4, h5, h14, h15, ⟨⟨hfs1, hfs2⟩, hfsr', hfsg'⟩, -⟩, hmf⟩
  simp only [E, frameA, frameB, frameN, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
    Janus.Amd64.GoABI.regFP, Janus.Amd64.GoABI.xmmZero, cgoStackScratch, gStructSize, setRegF,
    ↓reduceIte, Nat.reduceEqDiff, h32, h80] at hmf h4 h5 h14 h15 hfs1 hfs2 hfsr' hfsg'
  have hfsa' : (fs + BitVec.ofNat 64 18446744073709551608).toNat = fs.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [hmf.accessible] at hfsr'
  simp only [Janus.Arm64.Memory.accessible_writeLE] at hfsr'
  apply ReturnsC.of_reaches
  janus64_run [h4, h5, h14, h15, hfsa', hfsg']
  -- the slices were read through the stack stores of `Dot32` and `_Cfunc_c_dot32`
  refine ⟨rfl, ?_⟩
  simp only [DotRes]
  rw [if_neg (by omega)]
  refine congrArg (· % 4294967296) ?_
  clear hmf
  apply dot32_congr
  · intro i hi
    janus64_simp
  · intro i hi
    janus64_simp


/-! ## Composition -/

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · rintro s t ret ⟨hb, ⟨hacc, hout⟩, hpb, ⟨hpacc, hpout⟩, hqb, hqacc, hqout⟩ he
    have hsep := he.stackSep _ _ _ hacc
    have hpsep := he.stackSep _ _ _ hpacc
    have hqsep := he.stackSep _ _ _ hqacc
    have hk : ∀ o, o + 8 ≤ 24 → t.mem.readLE ((s.regs 3).toNat + o) 8 = s.mem.readLE ((s.regs 3).toNat + o) 8 :=
      fun o ho => he.kept _ 8 ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by omega) (by omega),
        Outside.of_sub hout (by omega) (by omega)⟩
    have hk0 := hk 0 (by omega)
    have hk1 := hk 8 (by omega)
    have hk2 := hk 16 (by omega)
    simp only [Nat.add_zero] at hk0
    simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep hpsep hqsep
    simp only [WPre, frameA, frameB, frameN] at hpb hpacc hpout hpsep hqb hqacc hqout hqsep ⊢
    rw [hk0, hk1, hk2]
    exact ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩, by omega, hpb,
      he.keptAcc _ _ _ ⟨hpacc, hpout⟩, by omega, hqb, he.keptAcc _ _ _ ⟨hqacc, hqout⟩, by omega⟩
  · intro s _; rfl
  · rintro s t ret t' ⟨hb, ⟨hacc, hout⟩, hpb, ⟨hpacc, hpout⟩, hqb, hqacc, hqout⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by
      simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep ⊢; omega)
    simp only [Janus.Arm64.Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Janus.Arm64.Memory.bytes_writeLE, Janus.Arm64.Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 3).toNat ≤ c → c + n ≤ (s.regs 3).toNat + 32 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    split
    · have e0 := hk _ 8 (Nat.le_refl _) (by omega)
      have e1 := hk ((s.regs 3).toNat + 8) 8 (by omega) (by omega)
      have e2 := hk ((s.regs 3).toNat + 16) 8 (by omega) (by omega)
      simp only [frameA, frameB, frameN] at hpb hpacc hpout hqb hqacc hqout ⊢
      rw [e0, e1, e2, dot32_congr _ _ _
        (fun i hi => he.kept _ 4 ⟨Janus.Arm64.Memory.accessible_sub _ hpacc (Or.inl rfl) (by omega) (by omega),
          Outside.of_sub hpout (by omega) (by omega)⟩)
        (fun i hi => he.kept _ 4 ⟨Janus.Arm64.Memory.accessible_sub _ hqacc (Or.inl rfl) (by omega) (by omega),
          Outside.of_sub hqout (by omega) (by omega)⟩)]
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, _⟩ b _ hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`Dot32` end to end.** -/
theorem correctness (pa la ca pb lb cb : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [pa, la, ca, pb, lb, cb]
      (GoPre pa la pb lb) (fun s s' => (s'.regs 0).toNat = DotRes pa la pb lb s) :=
  (go_spec pa la ca pb lb cb).refine refines

end Proof
