import Janus
import Extracted

/-! `example.com/basic/sse.Index32(p *[32]byte, c byte) int` on amd64: the index of the first
byte of `*p` equal to `c` (32 if none), with SSE2 `PCMPEQB`/`PMOVMSKB`.

```go
func Index32(p *[32]byte, c byte) int { return indexByte32(p, c) }
```

`indexByte32` is Go assembly (ABI0, `examples/basic/sse/sse_amd64.s`), called directly with its
arguments on the stack: `c` is broadcast to all 16 bytes of `X0` (`MOVQ AX, X0; PUNPCKLBW X0, X0;
PSHUFLW $0, X0, X0; PUNPCKLQDQ X0, X0`), each 16-byte half of `*p` is compared with it (`MOVOU`,
`PCMPEQB`) and turned into a 16-bit mask (`PMOVMSKB`); the two masks are joined (`SHLQ $16`,
`ORQ`), bit 32 is set as a sentinel (`BTSQ $32`) and `BSFQ` finds the lowest set bit.

**Guarantee.** For every pointer `p` to 32 readable bytes outside the stack window and every
`c`, every call whose stack-growth check falls through returns `firstIdx s.mem p (c mod 256) 32`:
the least `i < 32` with `p[i] = c`, or 32 if there is none.

**How.** `msb_cmpeq_repl`: the `PMOVMSKB` of a `PCMPEQB` against the broadcast byte is the
equality mask `eqMask`; `ctz_eqMask`: `BSF` of the mask with the sentinel bit is `firstIdx`;
`bcast_lo`, `unpckl64_self`, `repl16`: the broadcast. -/

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

/-- The broadcast of `PUNPCKLBW`/`PSHUFLW $0` (the low word four times, the upper quadword of
the source, here 0). -/
theorem bcast_lo (u : Nat) (hu : u < 65536) :
    (u % 340282366920938463463374607431768211456 / 1 % 65536 +
          65536 * (u % 340282366920938463463374607431768211456 / 1 % 65536) +
        4294967296 * (u % 340282366920938463463374607431768211456 / 1 % 65536) +
      281474976710656 * (u % 340282366920938463463374607431768211456 / 1 % 65536) +
      u % 340282366920938463463374607431768211456 / 18446744073709551616 * 18446744073709551616) %
      340282366920938463463374607431768211456 = 281479271743489 * u := by
  rw [Nat.mod_eq_of_lt (show u < 340282366920938463463374607431768211456 by omega), Nat.div_one,
    Nat.mod_eq_of_lt hu, Nat.div_eq_of_lt (show u < 18446744073709551616 by omega)]
  omega

theorem unpackLo_self (x : Nat) (hx : x < 256) : unpackLoBytes 8 x x = 257 * x := by
  simp only [unpackLoBytes]
  have : x / 256 = 0 := by omega
  simp only [this, Nat.zero_mod, Nat.zero_div]
  omega

/-- `PUNPCKLQDQ x, x`: the low quadword twice. -/
theorem unpckl64_self (v : Nat) (hv : v < 2 ^ 64) :
    ExecSSE.pintOp (.unpckl 64) v v = v + 18446744073709551616 * v := by
  simp only [ExecSSE.pintOp, ExecSSE.lanes, Janus.Arm64.ofElems, Janus.Arm64.elem]
  simp
  omega

theorem repl16 (x : Nat) (hx : x < 256) : replBytes 16 x =
    (281479271743489 * (257 * x) + 18446744073709551616 * (281479271743489 * (257 * x))) %
      340282366920938463463374607431768211456 := by
  simp only [replBytes]; omega

set_option maxHeartbeats 3000000 in
theorem correctness (p c : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, c]
      (fun s => Buffer s p 32 false ∧ StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ TlsG s ∧
        ((s.regs 4).toNat + 8 ≤ p.toNat ∨ p.toNat + 32 ≤ (s.regs 4).toNat - 40) ∧
        ((s.regs 4).toNat + 8 ≤ s.fsBase.toNat - 8 ∨ s.fsBase.toNat ≤ (s.regs 4).toNat - 40))
      (fun s s' => (s'.regs 0).toNat = firstIdx s.mem p.toNat (c.toNat % 256) 32) := by
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
  janus64_run [hfsa, BitVec.toNat_or, Nat.or_eq_zero_iff, BitVec.natCast_eq_ofNat]
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · rw [htls.g]; simp [regG]
  have hx : c.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have hB : c.toNat % 256 % 4294967296 % 340282366920938463463374607431768211456 = c.toNat % 256 := by omega
  rw [hB, unpackLo_self _ hx, bcast_lo _ (by omega), unpckl64_self _ (by omega), ← repl16 _ hx,
    msb_cmpeq_repl _ _ hx, msb_cmpeq_repl _ _ hx]
  have hA := eqMask_lt s.mem (c.toNat % 256) 16 p.toNat
  have hB' := eqMask_lt s.mem (c.toNat % 256) 16 (p.toNat + 16)
  have hsplit := eqMask_add s.mem (c.toNat % 256) 16 16 p.toNat
  simp only [show (16 : Nat) + 16 = 32 by rfl] at hsplit
  generalize eqMask s.mem p.toNat (c.toNat % 256) 16 = A at hA hsplit ⊢
  generalize eqMask s.mem (p.toNat + 16) (c.toNat % 256) 16 = B at hB' hsplit ⊢
  simp only [show (2 : Nat) ^ 16 = 65536 by rfl] at hA hB' hsplit
  rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show B < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show B * 65536 < 18446744073709551616 by omega),
    Nat.or_comm A, Nat.mul_comm B, show (65536 : Nat) = 2 ^ 16 by rfl,
    ← Nat.two_pow_add_eq_or_of_lt (show A < 2 ^ 16 by omega),
    show (4294967296 : Nat) = 2 ^ 32 by rfl,
    Nat.or_two_pow_eq_add_of_lt (show 2 ^ 16 * B + A < 2 ^ 32 by omega),
    show 2 ^ 16 * B + A = eqMask s.mem p.toNat (c.toNat % 256) 32 by rw [hsplit]; omega,
    ctz_eqMask s.mem _ 32 63 p.toNat (by omega)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (firstIdx_le s.mem (c.toNat % 256) 32 p.toNat) (by decide))

end Proof
