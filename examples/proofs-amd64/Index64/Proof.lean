import Janus
import Extracted

/-! `example.com/basic/avx.Index64(p *[64]byte, c byte) int` on amd64: the index of the first
byte of `*p` equal to `c` (64 if none), with AVX2 on YMM.

```go
func Index64(p *[64]byte, c byte) int { return indexByte64(p, c) }
```

`indexByte64` is Go assembly (ABI0, `examples/basic/avx/avx_amd64.s`): `c` is moved into `XMM0`
by `VMOVD` (a VEX.128 write: bits 255:32 of `YMM0` become zero) and broadcast to the 32 bytes of
`YMM0` (`VPBROADCASTB`); each 32-byte half of `*p` is compared with it straight from memory
(`VPCMPEQB (SI), Y0, Y1`) and turned into a 32-bit mask (`VPMOVMSKB`); the two masks are joined
into a 64-bit one (`SHLQ $32`, `ORQ`) and `TZCNTQ` counts its trailing zeros (64 for an all-zero
mask, so no sentinel bit is needed); `VZEROUPPER` before returning.

**Guarantee.** For every pointer `p` to 64 readable bytes outside the stack window and every
`c`, every call whose stack-growth check falls through returns `firstIdx s.mem p (c mod 256) 64`:
the least `i < 64` with `p[i] = c`, or 64 if there is none.

**How.** `msb_cmpeq_repl` (with `cmpeqBytes_comm`): the `VPMOVMSKB` of a `VPCMPEQB` against the
broadcast byte is the equality mask `eqMask`; `eqMask_add` joins the two halves;
`tzcnt_eqMask`: `TZCNT` of the mask is `firstIdx`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- The index of the first of the `n` bytes at `a` equal to `c`, `n` if none. -/
def firstIdx (m : Janus.Arm64.Memory) (a c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if m.readLE a 1 = c then 0 else 1 + firstIdx m (a + 1) c n


theorem firstIdx_le (m : Janus.Arm64.Memory) (c : Nat) : ∀ n a, firstIdx m a c n ≤ n
  | 0, _ => Nat.le_refl _
  | n + 1, a => by
    have := firstIdx_le m c n (a + 1)
    simp only [firstIdx]; split <;> omega

/-- The `n`-bit mask whose bit `i` is set iff the byte at `a + i` is `c`. -/
def eqMask (m : Janus.Arm64.Memory) (a c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if m.readLE a 1 = c then 1 else 0) + 2 * eqMask m (a + 1) c n

theorem eqMask_lt (m : Janus.Arm64.Memory) (c : Nat) : ∀ n a, eqMask m a c n < 2 ^ n
  | 0, _ => by simp [eqMask]
  | n + 1, a => by
    have := eqMask_lt m c n (a + 1)
    simp only [eqMask, Nat.pow_succ]; split <;> omega

theorem eqMask_add (m : Janus.Arm64.Memory) (c : Nat) : ∀ j k a,
    eqMask m a c (j + k) = eqMask m a c j + 2 ^ j * eqMask m (a + j) c k
  | 0, k, a => by simp [eqMask]
  | j + 1, k, a => by
    rw [show j + 1 + k = (j + k) + 1 by omega]
    simp only [eqMask, eqMask_add m c j k (a + 1), Nat.pow_succ, show a + 1 + j = a + (j + 1) by omega]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ j)]; omega

theorem msbBytes_step (k E Z : Nat) (hE : E < 256) :
    msbBytes (k + 1) (E + 256 * Z) = E / 128 + 2 * msbBytes k Z := by
  simp only [msbBytes]
  rw [show (E + 256 * Z) % 256 = E by omega, show (E + 256 * Z) / 256 = Z by omega]

theorem cmpeqBytes_step (k b x A B : Nat) (hb : b < 256) (hx : x < 256) :
    cmpeqBytes (k + 1) (b + 256 * A) (x + 256 * B) = (if b = x then 255 else 0) + 256 * cmpeqBytes k A B := by
  simp only [cmpeqBytes]
  rw [show (b + 256 * A) % 256 = b by omega, show (b + 256 * A) / 256 = A by omega,
    show (x + 256 * B) % 256 = x by omega, show (x + 256 * B) / 256 = B by omega]

/-- `PMOVMSKB` of `PCMPEQB` against `k` copies of `x`: the equality mask of the bytes. -/
theorem msb_cmpeq_repl (m : Janus.Arm64.Memory) (x : Nat) (hx : x < 256) : ∀ k a,
    msbBytes k (cmpeqBytes k (m.readLE a k) (replBytes k x)) = eqMask m a x k
  | 0, _ => rfl
  | k + 1, a => by
    have hb := (m.bytes a).isLt
    have hr : m.readLE a 1 = (m.bytes a).toNat := by simp [Janus.Arm64.Memory.readLE]
    rw [Janus.Arm64.Memory.readLE, replBytes, cmpeqBytes_step _ _ _ _ _ hb hx,
      msbBytes_step _ _ _ (by split <;> omega), msb_cmpeq_repl m x hx k (a + 1), eqMask, hr]
    split <;> rfl

/-- `BSF` of the mask with a sentinel bit `k`: the first index. -/
theorem ctz_eqMask (m : Janus.Arm64.Memory) (c : Nat) : ∀ k j a, k ≤ j →
    ctzNat (j + 1) (eqMask m a c k + 2 ^ k) = firstIdx m a c k
  | 0, j, a, _ => by simp [eqMask, firstIdx, ctzNat]
  | k + 1, j, a, h => by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [eqMask, firstIdx]
    rw [ctzNat]
    by_cases hc : m.readLE a 1 = c
    · simp only [hc, ↓reduceIte]
      have : (1 + 2 * eqMask m (a + 1) c k + 2 ^ (k + 1)) % 2 = 1 := by rw [Nat.pow_succ]; omega
      simp [this]
    · simp only [hc, ↓reduceIte]
      have h1 : (0 + 2 * eqMask m (a + 1) c k + 2 ^ (k + 1)) % 2 = 0 := by rw [Nat.pow_succ]; omega
      have h2 : (0 + 2 * eqMask m (a + 1) c k + 2 ^ (k + 1)) / 2 = eqMask m (a + 1) c k + 2 ^ k := by
        rw [Nat.pow_succ]; omega
      simp only [h1, h2, show ¬ (0 = 1) by decide, ↓reduceIte]
      rw [ctz_eqMask m c k j (a + 1) (by omega)]

/-- `PCMPEQB` is symmetric. -/
theorem cmpeqBytes_comm : ∀ k a b, cmpeqBytes k a b = cmpeqBytes k b a
  | 0, _, _ => rfl
  | k + 1, a, b => by
    simp only [cmpeqBytes, cmpeqBytes_comm k (a / 256) (b / 256)]
    by_cases h : a % 256 = b % 256
    · simp [h]
    · simp [h, Ne.symm h]

/-- `TZCNT` of the equality mask: the first index (`k` if none). -/
theorem tzcnt_eqMask (m : Janus.Arm64.Memory) (c : Nat) : ∀ k a,
    ctzNat k (eqMask m a c k) = firstIdx m a c k
  | 0, a => rfl
  | k + 1, a => by
    simp only [eqMask, firstIdx, ctzNat]
    by_cases hc : m.readLE a 1 = c
    · simp only [hc, ↓reduceIte]
      have : (1 + 2 * eqMask m (a + 1) c k) % 2 = 1 := by omega
      simp [this]
    · simp only [hc, ↓reduceIte]
      have h1 : (0 + 2 * eqMask m (a + 1) c k) % 2 = 0 := by omega
      have h2 : (0 + 2 * eqMask m (a + 1) c k) / 2 = eqMask m (a + 1) c k := by omega
      simp only [h1, h2, show ¬ (0 = 1) by decide, ↓reduceIte]
      rw [tzcnt_eqMask m c k (a + 1)]

theorem ctzNat_le : ∀ n x, ctzNat n x ≤ n
  | 0, _ => Nat.le_refl _
  | n + 1, x => by
    have := ctzNat_le n (x / 2)
    simp only [ctzNat]; split <;> omega

theorem replBytes_lt (x : Nat) (hx : x < 256) : ∀ k, replBytes k x < 256 ^ k
  | 0 => by simp [replBytes]
  | k + 1 => by
    have := replBytes_lt x hx k
    simp only [replBytes, Nat.pow_succ]; omega

set_option maxHeartbeats 3000000 in
theorem correctness (p c : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, c]
      (fun s => Buffer s p 64 false ∧ StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ TlsG s ∧
        ((s.regs 4).toNat + 8 ≤ p.toNat ∨ p.toNat + 64 ≤ (s.regs 4).toNat - 40) ∧
        ((s.regs 4).toNat + 8 ≤ s.fsBase.toNat - 8 ∨ s.fsBase.toNat ≤ (s.regs 4).toNat - 40))
      (fun s s' => (s'.regs 0).toNat = firstIdx s.mem p.toNat (c.toNat % 256) 64) := by
  intro ret hret s hs ⟨⟨hpb, hp⟩, hg, ⟨hle, hnw, hacc⟩, htls, hd, hdt⟩
  janus64_intro hs
  have hfsa := htls.addr
  have hfs := htls.base
  have hfsr := htls.readable
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run [hfsa]
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · rw [htls.g]; simp [regG]
  have hx : c.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have hr : replBytes 32 (c.toNat % 256) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      replBytes 32 (c.toNat % 256) :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (replBytes_lt _ hx 32) (by decide))
  rw [hr, cmpeqBytes_comm 32 (replBytes 32 _), cmpeqBytes_comm 32 (replBytes 32 _), msb_cmpeq_repl _ _ hx,
    msb_cmpeq_repl _ _ hx]
  have hA := eqMask_lt s.mem (c.toNat % 256) 32 p.toNat
  have hB := eqMask_lt s.mem (c.toNat % 256) 32 (p.toNat + 32)
  have hsplit := eqMask_add s.mem (c.toNat % 256) 32 32 p.toNat
  simp only [show (32 : Nat) + 32 = 64 by rfl] at hsplit
  rw [← tzcnt_eqMask, hsplit]
  generalize eqMask s.mem p.toNat (c.toNat % 256) 32 = A at hA ⊢
  generalize eqMask s.mem (p.toNat + 32) (c.toNat % 256) 32 = B at hB ⊢
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (ctzNat_le 64 _) (by decide))]
  apply congrArg (ctzNat 64)
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show A < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show B < 2 ^ 64 by omega),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show B * 2 ^ 32 < 2 ^ 64 by omega),
    Nat.or_comm A, Nat.mul_comm B, ← Nat.two_pow_add_eq_or_of_lt (show A < 2 ^ 32 by omega)]
  omega

end Proof
