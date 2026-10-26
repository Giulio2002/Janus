import Janus
import Extracted

/-! `example.com/basic/avx512.Search64(p *byte, nq int, c byte) int` on amd64: the index of the
first of the `8·nq` bytes at `p` equal to `c` (`0 ≤ nq ≤ 8`), or 64 if there is none, with
AVX-512.

```go
func Search64(p *byte, nq int, c byte) int { return search64(p, nq, c) }
```

`search64` is Go assembly (ABI0, `examples/basic/avx512/avx512_amd64.s`):

```
MOVL $1, BX ; SHLL CX, BX ; DECL BX ; KMOVB BX, K1      // K1 = the nq low qwords
VMOVDQU64.Z (SI), K1, Z0                               // masked, zeroing load: nq qwords read
VPBROADCASTB AX, Z1                                    // c in every byte
SHLQ $3, CX ; MOVQ $-1, DX ; BZHIQ CX, DX, DX ; KMOVQ DX, K3   // K3 = the 8·nq low bytes
VPCMPEQB Z1, Z0, K3, K2                                // K2 = equality mask under K3
KMOVQ K2, AX ; TZCNTQ AX, AX ; VZEROUPPER
```

**Guarantee.** For every `nq ≤ 8`, every pointer `p` with the `8·nq` bytes at `p` readable and
outside the stack window, and every `c`: every call whose stack-growth check falls through returns
`firstIdx s.mem p (c mod 256) (8·nq)` if some byte matches, else 64. Only the `8·nq` bytes need
to be readable: the masked load accesses only the selected qwords (fault suppression, which the
oracle checks on hardware with operands straddling the end of its buffer). The model also asks for
the whole 64-byte operand below `2^47` (conservative, `docs/SOUNDNESS.md`).

**How.** One symbolic run per `nq` (`janus64_cases`); `search_result` turns the mask the run
leaves (`VPCMPEQB` of the zero-masked load against the broadcast byte, under the byte mask) into
`eqMask` (`eq_of_bits`, `eqMask_bit`), and `ctz_eqMask` its `TZCNT` into the first index. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Tactic
open Janus.Arm64 (elem ofElems)

/-- The index of the first of the `n` bytes at `a` equal to `c`, `n` if none. -/
def firstIdx (m : Janus.Arm64.Memory) (a c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if m.readLE a 1 = c then 0 else 1 + firstIdx m (a + 1) c n

/-- The `n`-bit mask whose bit `i` is set iff the byte at `a + i` is `c`. -/
def eqMask (m : Janus.Arm64.Memory) (a c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if m.readLE a 1 = c then 1 else 0) + 2 * eqMask m (a + 1) c n

theorem ctzNat_zero : ∀ j, ctzNat j 0 = j
  | 0 => rfl
  | j + 1 => by simp [ctzNat, ctzNat_zero j]; omega

theorem ctzNat_le : ∀ n x, ctzNat n x ≤ n
  | 0, _ => Nat.le_refl _
  | n + 1, x => by
    have := ctzNat_le n (x / 2)
    simp only [ctzNat]; split <;> omega

/-- `TZCNT` (over `n + j` bits) of the equality mask of `n` bytes: the first index, or `n + j`
if there is none. -/
theorem ctz_eqMask (m : Janus.Arm64.Memory) (c j : Nat) : ∀ n a,
    ctzNat (n + j) (eqMask m a c n) = if firstIdx m a c n < n then firstIdx m a c n else n + j
  | 0, a => by simp [eqMask, firstIdx, ctzNat_zero]
  | n + 1, a => by
    rw [show n + 1 + j = (n + j) + 1 by omega]
    simp only [eqMask, firstIdx, ctzNat]
    by_cases hc : m.readLE a 1 = c
    · simp only [hc, ↓reduceIte]
      have : (1 + 2 * eqMask m (a + 1) c n) % 2 = 1 := by omega
      simp [this]
    · simp only [hc, ↓reduceIte]
      have h1 : (0 + 2 * eqMask m (a + 1) c n) % 2 = 0 := by omega
      have h2 : (0 + 2 * eqMask m (a + 1) c n) / 2 = eqMask m (a + 1) c n := by omega
      simp only [h1, h2, show ¬ (0 = 1) by decide, ↓reduceIte]
      rw [ctz_eqMask m c j n (a + 1)]
      split <;> split <;> omega

/-- Bit `i` of `eqMask`: the byte comparison, for `i < n`; zero above. -/
theorem eqMask_bit (m : Janus.Arm64.Memory) (c : Nat) : ∀ n a i,
    elem (eqMask m a c n) 1 i = if i < n ∧ m.readLE (a + i) 1 = c then 1 else 0
  | 0, a, i => by simp [eqMask, elem]
  | n + 1, a, i => by
    simp only [eqMask]
    rcases i with _ | i
    · simp only [elem, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.pow_one, Nat.add_zero]
      split <;> split <;> omega
    · have := eqMask_bit m c n (a + 1) i
      simp only [elem, Nat.pow_one, Nat.one_mul] at this ⊢
      rw [show 2 ^ (i + 1) = 2 * 2 ^ i by rw [Nat.pow_succ, Nat.mul_comm], ← Nat.div_div_eq_div_mul,
        show ((if m.readLE a 1 = c then 1 else 0) + 2 * eqMask m (a + 1) c n) / 2 = eqMask m (a + 1) c n by
          split <;> omega, this, show a + 1 + i = a + (i + 1) by omega]
      split <;> split <;> omega

theorem pow_sub_one_bit (n j : Nat) : (2 ^ n - 1) / 2 ^ j % 2 = if j < n then 1 else 0 := by
  have h := Nat.testBit_two_pow_sub_one n j
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow] at h
  by_cases hj : j < n
  · simp only [hj, decide_true, ↓reduceIte] at h ⊢
    have := Nat.mod_two_eq_zero_or_one ((2 ^ n - 1) / 2 ^ j)
    rcases this with h0 | h1
    · simp [h0] at h
    · exact h1
  · simp only [hj, decide_false, ↓reduceIte] at h ⊢
    have := Nat.mod_two_eq_zero_or_one ((2 ^ n - 1) / 2 ^ j)
    rcases this with h0 | h1
    · exact h0
    · simp [h1] at h

theorem eq_of_bits {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : ∀ j < 64, elem x 1 j = elem y 1 j) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 64
  · have := h j hj
    simp only [elem, Nat.one_mul, Nat.pow_one] at this
    rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two,
      Nat.one_and_eq_mod_two, this]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem eqMask_lt (m : Janus.Arm64.Memory) (c : Nat) : ∀ n a, eqMask m a c n < 2 ^ n
  | 0, _ => by simp [eqMask]
  | n + 1, a => by
    have := eqMask_lt m c n (a + 1)
    simp only [eqMask, Nat.pow_succ]; split <;> omega

/-- `search64`'s equality mask for `nq` qwords, as `janus64_run` leaves it, is `eqMask` of the
`8·nq` bytes, and its `TZCNT` the first index (64 if none). -/
theorem search_result (m : Janus.Arm64.Memory) (p c nq : Nat) (hn : nq ≤ 8) :
    ctzNat 64 (ofElems 1 64 fun j =>
      (decide ((2 ^ (8 * nq) - 1) / 2 ^ j % 2 = 1) &&
        decide (((elem (ofElems 64 8 fun i => if (2 ^ nq - 1) / 2 ^ i % 2 = 1 then
            elem (ofElems 64 8 fun i => if (2 ^ nq - 1) / 2 ^ i % 2 = 1 then elem (m.readLE p 64) 64 i else 0) 64 i
            else 0) 8 j : Nat) : Int) = ((elem (ofElems 8 64 fun _ => c % 256) 8 j : Nat) : Int))).toNat) % 2 ^ 64 =
      if firstIdx m p (c % 256) (8 * nq) < 8 * nq then firstIdx m p (c % 256) (8 * nq) else 64 := by
  have hA : (ofElems 1 64 fun j =>
      (decide ((2 ^ (8 * nq) - 1) / 2 ^ j % 2 = 1) &&
        decide (((elem (ofElems 64 8 fun i => if (2 ^ nq - 1) / 2 ^ i % 2 = 1 then
            elem (ofElems 64 8 fun i => if (2 ^ nq - 1) / 2 ^ i % 2 = 1 then elem (m.readLE p 64) 64 i else 0) 64 i
            else 0) 8 j : Nat) : Int) = ((elem (ofElems 8 64 fun _ => c % 256) 8 j : Nat) : Int))).toNat) =
      eqMask m p (c % 256) (8 * nq) := by
    apply eq_of_bits (ofElems_lt 1 64 _)
      (Nat.lt_of_lt_of_le (eqMask_lt m _ _ _) (Nat.pow_le_pow_right (by decide) (by omega)))
    intro j hj
    rw [elem_ofElems _ hj, eqMask_bit, pow_sub_one_bit]
    have hq : j / 8 < 8 := by omega
    have hz : elem (ofElems 64 8 fun i => if (2 ^ nq - 1) / 2 ^ i % 2 = 1 then
            elem (ofElems 64 8 fun i => if (2 ^ nq - 1) / 2 ^ i % 2 = 1 then elem (m.readLE p 64) 64 i else 0) 64 i
            else 0) 8 j = if j / 8 < nq then m.readLE (p + j) 1 else 0 := by
      have hl := elem_lane (x := (ofElems 64 8 fun i => if (2 ^ nq - 1) / 2 ^ i % 2 = 1 then
            elem (ofElems 64 8 fun i => if (2 ^ nq - 1) / 2 ^ i % 2 = 1 then elem (m.readLE p 64) 64 i else 0) 64 i
            else 0)) (e := 8) (k := 8) (j := j / 8) (i := j % 8) (by omega)
      rw [show 8 * (j / 8) + j % 8 = j by omega] at hl
      rw [← hl, show (8 : Nat) * 8 = 64 from rfl, elem_ofElems _ hq, pow_sub_one_bit, elem_ofElems _ hq,
        pow_sub_one_bit]
      by_cases hjq : j / 8 < nq
      · simp only [hjq, ↓reduceIte, Nat.mod_mod]
        rw [Nat.mod_eq_of_lt (elem_lt _ _ _)]
        have h1 := elem_lane (x := m.readLE p 64) (e := 8) (k := 8) (j := j / 8) (i := j % 8) (by omega)
        rw [show 8 * (j / 8) + j % 8 = j by omega] at h1
        rw [h1]
        have h2 := elem_readLE m (a := p) (n := 64) (k := 1) (i := j) (by omega)
        simpa using h2
      · simp [hjq, elem]
    rw [hz, elem_ofElems _ hj]
    by_cases hjn : j < 8 * nq
    · have hjq : j / 8 < nq := by omega
      simp only [hjn, hjq, ↓reduceIte, decide_true, Bool.true_and, Nat.mod_mod]
      by_cases he : m.readLE (p + j) 1 = c % 256
      · simp [he]
      · have h' : ((m.readLE (p + j) 1 : Nat) : Int) ≠ ((c % 256 : Nat) : Int) := fun h => he (Int.ofNat_inj.mp h)
        simp only [h', he, decide_false, and_false, ↓reduceIte, Bool.toNat_false, Nat.zero_mod]
    · simp [hjn]
  rw [hA, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (ctzNat_le 64 _) (by decide))]
  have := ctz_eqMask m (c % 256) (64 - 8 * nq) (8 * nq) p
  rw [show 8 * nq + (64 - 8 * nq) = 64 by omega] at this
  exact this


set_option maxHeartbeats 8000000 in
theorem correctness (p nq c : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, nq, c]
      (fun s => nq.toNat ≤ 8 ∧ Buffer s p (8 * nq.toNat) false ∧ p.toNat + 64 ≤ 2 ^ 47 ∧ StackGuardOK s 0 ∧
        StackWritable s 64 8 ∧ TlsG s ∧
        ((s.regs 4).toNat + 8 ≤ p.toNat ∨ p.toNat + 64 ≤ (s.regs 4).toNat - 64) ∧
        ((s.regs 4).toNat + 8 ≤ s.fsBase.toNat - 8 ∨ s.fsBase.toNat ≤ (s.regs 4).toNat - 64))
      (fun s s' => (s'.regs 0).toNat =
        if firstIdx s.mem p.toNat (c.toNat % 256) (8 * nq.toNat) < 8 * nq.toNat then
          firstIdx s.mem p.toNat (c.toNat % 256) (8 * nq.toNat)
        else 64) := by
  intro ret hret s hs ⟨hnq, ⟨hpb, hp⟩, hcan, hg, ⟨hle, hnw, hacc⟩, htls, hd, hdt⟩
  obtain ⟨n, hn, rfl⟩ : ∃ n, n < 9 ∧ nq = BitVec.ofNat 64 n :=
    ⟨nq.toNat, by omega, by simp⟩
  have hnn : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  rw [hnn] at hp hpb ⊢
  janus64_intro hs
  have hfsa := htls.addr
  have hfs := htls.base
  have hfsr := htls.readable
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  have hcan' : ¬ (140737488355328 < p.toNat + 64) := by omega
  have hq0 : 8 ≤ 8 * n → s.mem.accessible p.toNat 8 false = true :=
    fun h => Janus.Arm64.Memory.accessible_mono _ hp (by omega) (by omega)
  have hq : ∀ off, off + 8 ≤ 8 * n → s.mem.accessible (p.toNat + off) 8 false = true :=
    fun off h => Janus.Arm64.Memory.accessible_mono _ hp (by omega) (by omega)
  janus64_cases hn
  · janus64_run [hfsa, hcan', hq0, hq]
    refine ⟨⟨?_, rfl⟩, ?_⟩
    · rw [htls.g]; simp [regG]
    exact search_result s.mem p.toNat c.toNat 0 (by decide)
  · janus64_run [hfsa, hcan', hq0, hq]
    refine ⟨⟨?_, rfl⟩, ?_⟩
    · rw [htls.g]; simp [regG]
    exact search_result s.mem p.toNat c.toNat 1 (by decide)
  · janus64_run [hfsa, hcan', hq0, hq]
    refine ⟨⟨?_, rfl⟩, ?_⟩
    · rw [htls.g]; simp [regG]
    exact search_result s.mem p.toNat c.toNat 2 (by decide)
  · janus64_run [hfsa, hcan', hq0, hq]
    refine ⟨⟨?_, rfl⟩, ?_⟩
    · rw [htls.g]; simp [regG]
    exact search_result s.mem p.toNat c.toNat 3 (by decide)
  · janus64_run [hfsa, hcan', hq0, hq]
    refine ⟨⟨?_, rfl⟩, ?_⟩
    · rw [htls.g]; simp [regG]
    exact search_result s.mem p.toNat c.toNat 4 (by decide)
  · janus64_run [hfsa, hcan', hq0, hq]
    refine ⟨⟨?_, rfl⟩, ?_⟩
    · rw [htls.g]; simp [regG]
    exact search_result s.mem p.toNat c.toNat 5 (by decide)
  · janus64_run [hfsa, hcan', hq0, hq]
    refine ⟨⟨?_, rfl⟩, ?_⟩
    · rw [htls.g]; simp [regG]
    exact search_result s.mem p.toNat c.toNat 6 (by decide)
  · janus64_run [hfsa, hcan', hq0, hq]
    refine ⟨⟨?_, rfl⟩, ?_⟩
    · rw [htls.g]; simp [regG]
    exact search_result s.mem p.toNat c.toNat 7 (by decide)
  · janus64_run [hfsa, hcan', hq0, hq]
    refine ⟨⟨?_, rfl⟩, ?_⟩
    · rw [htls.g]; simp [regG]
    exact search_result s.mem p.toNat c.toNat 8 (by decide)

end Proof
