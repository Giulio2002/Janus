import Extracted

/-!
# `Sum32(xs []int32) int32` (Go) → `c_sum32` (C, vectorised by clang -O2) → back to Go (amd64)

```go
func Sum32(xs []int32) int32 {
	if len(xs) == 0 {
		return 0
	}
	return int32(C.c_sum32((*C.int32_t)(unsafe.Pointer(&xs[0])), C.uint64_t(len(xs))))
}
```

The C side (`examples/cgo/vec/cvec.c`, the whole cgo package and the runtime's C built with
`CC=clang`, `-g -O2`, clang 21.1.8) is the SSE2 loop of `CSum32.lean`: two `PADDD` accumulators
over 8 words per iteration, a `PSHUFD`/`PADDD` fold, a scalar tail.

**Guarantee (`correctness`).** For every slice header `(ptr, len, cap)` and every Go call of
`example.com/cgo/vec.Sum32` satisfying `GoPre ptr len` — the stack checks fall through, the stack
window (and the spill slot above the return address) is writable, the TLS `g` slot holds `g`, the
`4·len` bytes at `ptr` are readable, below `2^48` and away from the stack window, the `g` struct
and the TLS slot; and the cgo globals hold their static values — every run returns and leaves
`(xs[0] + … + xs[len-1]) mod 2^32` in `EAX` (zero-extended into `RAX`), for every length.

The statement is under the trusted `CgoCall Extracted.program` only: `Sum32`, `_Cfunc_c_sum32`,
the C wrapper and the vectorised C loop are executed by the model.

**How.** `csum_summary` is the callee contract of `c_sum32` (as in `CSum32.lean`);
`wrapper_spec` uses it at the wrapper's `call c_sum32`; `go_spec` is `Sum32` under
`CgoSpec wrapper G E`; `refines` and `correctness` compose them as in `GoSum.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Spec
  Janus.Amd64.FFI
open Janus.Arm64 (elem ofElems)

namespace Proof

/-! ## The C function `c_sum32` (as in `CSum32.lean`), as a callee summary -/

abbrev csum : Nat := segAddr Extracted.program "c_sum32"

/-- The scalar loop head `cmp %rcx,%rsi`. -/
abbrev tailHead : Nat := csum + 0x6e

/-- The vector loop head `movdqu (%rdi,%rax,4),%xmm2`. -/
abbrev vecHead : Nat := csum + 0x30

/-- What `c_sum32` guarantees to a caller. -/
abbrev SumPost (p n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 3 = s.regs 3 ∧ s'.regs 5 = s.regs 5 ∧
    s'.regs 12 = s.regs 12 ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧
    s'.regs 15 = s.regs 15 ∧ s'.df = false ∧ s'.mxcsr = s.mxcsr ∧ s'.mem = s.mem ∧
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
    S.regs 15 = s.regs 15 ∧ S.df = s.df ∧ S.mxcsr = s.mxcsr ∧ S.regs 7 = s.regs 7 ∧
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
    intro S i hk hpc hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hS7, hS6⟩ hs
    have hi : i = n.toNat := by omega
    subst hi
    janus64_run
    janus64_simp [SumPost]
    simpa using hs
  | succ k ih =>
    intro S i hk hpc hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hS7, hS6⟩ hs
    janus64_run until [tailHead]
    apply ih _ (i + 1) (by omega) (by janus64_simp) ?_ (by simp only [Kept]; janus64_simp) ?_
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
    intro S k hk hpc hS0 hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hS7, hS6⟩ hacc'
    janus64_run until [tailHead]
    obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩ := hacc'
    apply tail p n s hpre' (n.toNat - 8 * (k + 1)) _ (8 * (k + 1)) (by omega) (by janus64_simp)
      (by janus64_simp; rw [hk]) (by simp only [Kept]; janus64_simp)
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
    intro S k hk hpc hS0 hS1 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf, hmx, hS7, hS6⟩ hacc'
    janus64_run until [vecHead]
    apply ih _ (k + 1) (by omega) (by janus64_simp) ?_ (by janus64_simp) (by simp only [Kept]; janus64_simp) ?_
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
theorem csum_summary (p n : BitVec 64) :
    Summary Extracted.program csum (SumPre p n) (SumPost p n) := by
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

/-- The sum of `n` 32-bit words at `p` is the same in two memories that agree outside `rs`. -/
theorem sum32_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) (p : Nat) :
    ∀ n, Outside p (4 * n) rs → sum32 m' p n = sum32 m p n
  | 0, _ => rfl
  | n + 1, ho => by
    rw [sum32_succ, sum32_succ, sum32_frame h p n (Outside.of_sub ho (Nat.le_refl _) (by omega)),
      h.readLE _ _ (Outside.of_sub ho (by omega) (by omega))]

theorem sum32_congr {m m' : Memory} (p : Nat) :
    ∀ n, (∀ i, i < n → m'.readLE (p + 4 * i) 4 = m.readLE (p + 4 * i) 4) →
      sum32 m' p n = sum32 m p n
  | 0, _ => rfl
  | n + 1, h => by
    rw [sum32_succ, sum32_succ, sum32_congr p n fun i hi => h i (by omega), h n (by omega)]

theorem writeLE_mod_4 (m : Memory) (a v : Nat) :
    m.writeLE a 4 (v % 4294967296) = m.writeLE a 4 v :=
  Janus.Arm64.Memory.writeLE_mod m a 4 v

/-- The same store, of equal values, on both sides keeps a frame. -/
theorem frame_store {m m' : Memory} {rs : List (Nat × Nat)} {a v v' : Nat} (h : MemFrame m m' rs)
    (hv : v' % 4294967296 = v % 4294967296) : MemFrame (m.writeLE a 4 v) (m'.writeLE a 4 v') rs := by
  rw [← writeLE_mod_4 m, ← writeLE_mod_4 m', hv]; exact h.writeLE_both a 4 _

/-! ## The cgo wrapper -/

abbrev wrapper : Nat := segAddr Extracted.program "_cgo_d97cf7e811b4_Cfunc_c_sum32"

/-- The slice pointer and length in the cgo frame at `a`. -/
abbrev frameP (m : Memory) (a : Nat) : Nat := m.readLE a 8
abbrev frameN (m : Memory) (a : Nat) : Nat := m.readLE (a + 8) 8

def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 8 ∧ a.toNat + 24 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 24 true = true ∧
    (a.toNat + 24 ≤ (t.regs 4).toNat - 4096 ∨ (t.regs 4).toNat + 8 ≤ a.toNat) ∧
    frameP t.mem a.toNat + 4 * frameN t.mem a.toNat ≤ 2 ^ 48 ∧
    t.mem.accessible (frameP t.mem a.toNat) (4 * frameN t.mem a.toNat) false = true ∧
    (frameP t.mem a.toNat + 4 * frameN t.mem a.toNat ≤ (t.regs 4).toNat - 4096 ∨
      (t.regs 4).toNat + 8 ≤ frameP t.mem a.toNat)

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 16) 4
      (sum32 t.mem (frameP t.mem a.toNat) (frameN t.mem a.toNat) % 2 ^ 32)) t'.mem
    [((t.regs 4).toNat - 4096, (t.regs 4).toNat)]

theorem wrapper_spec (T a : BitVec 64) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd, hpb, hpa, hpd⟩
  apply ReturnsC.of_reaches
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : t.regs 7 = a := hs.reg (i := 0) (by simp)
  simp only [Amd64.Program.withExit] at h_ret
  simp only [CABI.regSP, frameP, frameN] at hal hb htop hacc hpb hpa hpd
  have h32 : (t.regs 4 - 32#64).toNat = (t.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h32]; omega
  · janus64_simp [h32]; janus64_disch
  rintro s₁ ⟨-, f₁, rfl⟩
  apply ReturnsC.of_reaches
  janus64_run calls [csum_summary (BitVec.ofNat 64 (t.mem.readLE a.toNat 8))
    (BitVec.ofNat 64 (t.mem.readLE (a.toNat + 8) 8))]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h32]; omega
  · janus64_simp [h32]; janus64_disch
  rintro s₂ ⟨-, f₂, rfl⟩
  apply ReturnsC.of_reaches
  janus64_run
  simp only [WPost, frameP, frameN, Nat.reducePow]
  apply frame_store
  · janus_frame
  · rename_i hsum
    rw [hsum, Nat.mod_mod, sum32_frame (rs := [((t.regs 4).toNat - 4096, (t.regs 4).toNat)]) ?hf _ _ ?ho]
    · janus_frame
    · simp only [outside_cons, outside_nil, and_true]; omega

/-! ## The Go side: `Sum32` → `_Cfunc_c_sum32` → `runtime.cgocall` -/

def fnVar : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/vec._Cfunc_c_sum32.abi0" + 0x2d)

def alwaysFalse : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/vec._Cfunc_c_sum32.abi0" + 0x46)

/-- At the `cgocall`: the frame `RBX` and the slice it points at are Go memory the runtime leaves
alone. -/
def G (s : State) : Prop :=
  (s.regs 3).toNat + 24 ≤ 2 ^ 48 ∧ GoKept s (s.regs 3).toNat 24 true ∧
    frameP s.mem (s.regs 3).toNat + 4 * frameN s.mem (s.regs 3).toNat ≤ 2 ^ 48 ∧
    GoKept s (frameP s.mem (s.regs 3).toNat) (4 * frameN s.mem (s.regs 3).toNat) false

def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 3).toNat + 16) 4
    (sum32 s.mem (frameP s.mem (s.regs 3).toNat) (frameN s.mem (s.regs 3).toNat) % 2 ^ 32)

def GoPre (ptr len : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 40 ∧ StackWritable s 80 16 ∧ TlsG s ∧
  ptr.toNat + 4 * len.toNat ≤ 2 ^ 48 ∧ s.mem.accessible ptr.toNat (4 * len.toNat) false = true ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 = 0 ∧
  Outside (s.regs 14).toNat 456 [((s.regs 4).toNat - 80, (s.regs 4).toNat + 16)] ∧
  Outside (s.fsBase.toNat - 8) 8 [((s.regs 4).toNat - 80, (s.regs 4).toNat + 16)] ∧
  Outside fnVar 8 [((s.regs 4).toNat - 80, (s.regs 4).toNat + 16)] ∧
  Outside alwaysFalse 1 [((s.regs 4).toNat - 1104, (s.regs 4).toNat + 16),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)] ∧
  Outside ptr.toNat (4 * len.toNat) [((s.regs 4).toNat - 1104, (s.regs 4).toNat + 16),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)]

set_option maxHeartbeats 2000000 in
theorem go_spec (ptr len cap : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [ptr, len, cap] (GoPre ptr len)
      (fun s s' => (s'.regs 0).toNat = sum32 s.mem ptr.toNat len.toNat % 2 ^ 32) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, htop, hst⟩, ⟨hfs, hfsr, hfsg⟩, hpb, hpa, hfa, hfv, haa, hav, hdg,
    hdt, hdf, hda, hdp⟩
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
  have h80 : (s.regs 4 - 80#64).toNat = (s.regs 4).toNat - 80 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run [hfsa]
  · simp [sum32_zero]
  refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
  · simp only [G, GoKept, frameP, frameN, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
      cgoStackScratch, gStructSize, outside_cons, outside_nil, and_true]
    janus64_simp [h32, h80]
    refine ⟨by omega, ⟨?_, by omega, by omega, by omega, by omega⟩, by omega, hpa, by omega, by omega,
      by omega, by omega⟩
    janus64_disch
  rintro s' ⟨-, m, ⟨regs, fl, xm, yh, fs, mx, zh, kr, rfl, h4, h5, h14, h15, ⟨⟨hfs1, hfs2⟩, hfsr', hfsg'⟩, -⟩, hmf⟩
  simp only [E, frameP, frameN, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
    Janus.Amd64.GoABI.regFP, Janus.Amd64.GoABI.xmmZero, cgoStackScratch, gStructSize, setRegF,
    ↓reduceIte, Nat.reduceEqDiff, h32, h80] at hmf h4 h5 h14 h15 hfs1 hfs2 hfsr' hfsg'
  have hfsa' : (fs + BitVec.ofNat 64 18446744073709551608).toNat = fs.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [hmf.accessible] at hfsr'
  simp only [Janus.Arm64.Memory.accessible_writeLE] at hfsr'
  apply ReturnsC.of_reaches
  janus64_run [h4, h5, h14, h15, hfsa', hfsg']
  -- the slice was read through the stack stores of `Sum` and `_Cfunc_c_sum`
  refine ⟨rfl, congrArg (· % 4294967296) ?_⟩
  apply sum32_congr
  intro i hi
  clear hmf
  janus64_simp


/-! ## Composition -/

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · rintro s t ret ⟨hb, ⟨hacc, hout⟩, hpb, hpacc, hpout⟩ he
    have hsep := he.stackSep _ _ _ hacc
    have hpsep := he.stackSep _ _ _ hpacc
    have hk0 := he.kept _ 8 ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (Nat.le_refl _) (by omega),
      Outside.of_sub hout (Nat.le_refl _) (by omega)⟩
    have hk1 := he.kept ((s.regs 3).toNat + 8) 8 ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by omega)
      (by omega), Outside.of_sub hout (by omega) (by omega)⟩
    simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep hpsep
    simp only [WPre, frameP, frameN] at hpb hpacc hpout hpsep ⊢
    rw [hk0, hk1]
    exact ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩, by omega, hpb,
      he.keptAcc _ _ _ ⟨hpacc, hpout⟩, by omega⟩
  · intro s _; rfl
  · rintro s t ret t' ⟨hb, ⟨hacc, hout⟩, hpb, hpacc, hpout⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by
      simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep ⊢; omega)
    simp only [Janus.Arm64.Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Janus.Arm64.Memory.bytes_writeLE, Janus.Arm64.Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 3).toNat ≤ c → c + n ≤ (s.regs 3).toNat + 24 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    split
    · have e0 := hk _ 8 (Nat.le_refl _) (by omega)
      have e1 := hk ((s.regs 3).toNat + 8) 8 (by omega) (by omega)
      simp only [frameP, frameN] at hpb hpacc hpout ⊢
      rw [e0, e1, sum32_congr _ _ fun i hi =>
        he.kept _ 4 ⟨Janus.Arm64.Memory.accessible_sub _ hpacc (Or.inl rfl) (by omega) (by omega),
          Outside.of_sub hpout (by omega) (by omega)⟩]
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, _⟩ b _ hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`Sum32` end to end.** -/
theorem correctness (ptr len cap : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [ptr, len, cap]
      (GoPre ptr len) (fun s s' => (s'.regs 0).toNat = sum32 s.mem ptr.toNat len.toNat % 2 ^ 32) :=
  (go_spec ptr len cap).refine refines

end Proof
