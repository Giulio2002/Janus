import Janus
import Extracted

/-! `example.com/basic.Equal64(a, b *[64]byte) bool` on amd64: `bytes.Equal(a[:], b[:])`,
which the compiler lowers to a call of `runtime.memequal(a, b, 64)`.

```
CMPQ SP, 16(R14) ; JBE morestack ; PUSHQ BP ; MOVQ SP, BP ; SUBQ $0x18, SP
TESTB AL, (AX) ; TESTB AL, (BX)          // nil checks
MOVL $0x40, CX ; CALL runtime.memequal
ADDQ $0x18, SP ; POPQ BP ; RET
```

`runtime.memequal` returns 1 at once when `a = b`; otherwise it jumps to `memeqbody`
(`internal/bytealg/equal_amd64.s`), which for 64 bytes or more reads
`internal/cpu.X86.HasAVX2` and, when it is 1, runs `hugeloop_avx2` once:

```
VMOVDQU (SI), Y0 ; VMOVDQU (DI), Y1 ; VMOVDQU 32(SI), Y2 ; VMOVDQU 32(DI), Y3
VPCMPEQB Y1, Y0, Y4 ; VPCMPEQB Y2, Y3, Y5 ; VPAND Y4, Y5, Y6 ; VPMOVMSKB Y6, DX
ADDQ $64, SI ; ADDQ $64, DI ; SUBQ $64, BX ; CMPL DX, $0xffffffff ; JEQ hugeloop_avx2
VZEROUPPER ; XORQ AX, AX ; RET                       // a byte differs: false
```

and otherwise the SSE loop `hugeloop` once (four 16-byte `MOVDQU` pairs, `PCMPEQB`, three
`PAND`, `PMOVMSKB`, `CMPL DX, $0xffff`). With all 64 bytes equal either loop goes round once
more, finds `BX = 0 < 64` (the AVX2 one executes `VZEROUPPER`) and compares the last 8 bytes
again with scalar loads (`leftover`: `MOVQ -8(SI)(BX*1)`, `CMPQ`, `SETEQ AL`). The feature byte
lives in `.noptrbss` (Go sets it at start-up from `CPUID`), so the precondition makes it
readable; the theorem holds for every value of it, so both the AVX2 and the SSE path are
proved. The proof turns the mask tests into byte equality with `avx2_mask_eq`, `mask16_test`,
`msbBytes_land` and `msbBytes_cmpeq` (`Janus.Amd64.TacticAVX`). -/

namespace Proof

attribute [local irreducible] Janus.Amd64.msbBytes Janus.Amd64.cmpeqBytes
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `internal/cpu.X86.HasAVX2` (`internal/cpu.X86+68`, `.noptrbss`) in this binary. -/
def hasAVX2 : Nat := 0x579264

/-- `leftover` compares the last 8 bytes again; they are equal when the last 16 are. -/
theorem last8 (m : Memory) (a b : Nat) (h : m.readLE (a + 48) 16 = m.readLE (b + 48) 16) :
    (18446744073709551616 - m.readLE (b + 56) 8 + m.readLE (a + 56) 8) % 18446744073709551616 = 0 := by
  have := congrArg (· / 256 ^ 8) h
  simp only [Janus.Arm64.Memory.readLE_div _ _ _ _ (show 8 ≤ 16 by decide), Nat.reduceSub] at this
  rw [show a + 56 = a + 48 + 8 by omega, show b + 56 = b + 48 + 8 by omega, this]
  have := Janus.Arm64.Memory.readLE_lt m (b + 48 + 8) 8
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `Equal64(a, b)` returns `true` (`AL = 1`) exactly when the 64 bytes at `a` equal the 64
bytes at `b`, and `false` (`AL = 0`) otherwise, whatever the CPU-feature byte `HasAVX2` says:
with `HasAVX2 = 1` `memeqbody` compares 32 bytes at a time with `VPCMPEQB`/`VPMOVMSKB`,
otherwise 16 at a time with `PCMPEQB`/`PMOVMSKB`. Both arrays and the feature byte must be
readable, and none of them may overlap the 40 bytes below `RSP` that the function and its call
write before the comparison. -/
theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s a 64 false ∧
        Buffer s b 64 false ∧
        (a.toNat + 64 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat ≤ a.toNat) ∧
        (b.toNat + 64 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat ≤ b.toNat) ∧
        s.mem.accessible hasAVX2 1 false = true ∧
        (hasAVX2 + 1 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat ≤ hasAVX2))
      (fun s s' => (s'.regs 0).setWidth 8 = if valueAt s a 64 = valueAt s b 64 then 1 else 0) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hg, ⟨hle, hnw, hacc⟩, ⟨ha48, ha⟩, ⟨hb48, hb⟩, hda, hdb, hav, hdav⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr hda hdb
  simp only [hasAVX2, regSP] at hav hdav
  simp only [valueAt]
  have ha' := a.isLt
  have hb' := b.isLt
  janus64_run
  · -- `a = b`: `memequal` returns 1 without reading
    have hab : a.toNat = b.toNat := by
      generalize a.toNat = x at *; generalize b.toNat = y at *; omega
    have hq : s.mem.readLE a.toNat 64 = s.mem.readLE b.toNat 64 := by rw [hab]
    simp only [hq, ite_true]
  all_goals have hm : ∀ x n, s.mem.readLE x n % 256 ^ n = s.mem.readLE x n := fun x n =>
    Janus.Arm64.Memory.readLE_mod _ _ _ _ (Nat.le_refl _)
  -- 64 bytes are equal iff their two 32-byte halves, or their four 16-byte quarters, are
  all_goals have h64 : s.mem.readLE a.toNat 64 = s.mem.readLE b.toNat 64 ↔ _ :=
    readLE_eq_halves s.mem a.toNat b.toNat 32
  all_goals have h32 : s.mem.readLE a.toNat 32 = s.mem.readLE b.toNat 32 ↔ _ :=
    readLE_eq_halves s.mem a.toNat b.toNat 16
  all_goals have h32' : s.mem.readLE (a.toNat + 32) 32 = s.mem.readLE (b.toNat + 32) 32 ↔ _ :=
    readLE_eq_halves s.mem (a.toNat + 32) (b.toNat + 32) 16
  all_goals rw [show a.toNat + 32 + 16 = a.toNat + 48 by omega,
    show b.toNat + 32 + 16 = b.toNat + 48 by omega] at h32'
  -- the last 8 bytes, compared again by `leftover`
  all_goals have e8 := last8 s.mem a.toNat b.toNat
  · -- AVX2: one round of `hugeloop_avx2` with an all-ones mask, then `leftover`
    obtain ⟨h1, h2⟩ := (avx2_mask_eq _ _ _ _).1 hbr
    rw [hm, hm] at h1 h2
    have hq := h64.2 ⟨h1, h2.symm⟩
    simp only [e8 (h32'.1 h2.symm).2, hq, ite_true]
  · -- AVX2: a byte differs, the mask is not all ones: `XORQ AX, AX`
    have hne : ¬ s.mem.readLE a.toNat 64 = s.mem.readLE b.toNat 64 := by
      intro h
      obtain ⟨h1, h2⟩ := h64.1 h
      exact hbr ((avx2_mask_eq _ _ _ _).2 ⟨by rw [hm, hm, h1], by rw [hm, hm, h2]⟩)
    simp only [hne, ite_false]
  · -- SSE (`HasAVX2 ≠ 1`): one round of `hugeloop` with an all-ones mask, then `leftover`
    have key := (mask16_test _).1 hbr
    rw [msbBytes_land, msbBytes_mod_16, msbBytes_mod_16, msbBytes_land, msbBytes_land,
      msbBytes_cmpeq, msbBytes_cmpeq, msbBytes_cmpeq, msbBytes_cmpeq, hm, hm, hm, hm, hm, hm,
      hm, hm] at key
    obtain ⟨⟨k1, k2⟩, k3, k4⟩ := key
    have hq := h64.2 ⟨h32.2 ⟨k1, k2⟩, h32'.2 ⟨k3, k4⟩⟩
    simp only [e8 k4, hq, ite_true]
  · -- SSE: a byte differs
    have hne : ¬ s.mem.readLE a.toNat 64 = s.mem.readLE b.toNat 64 := by
      intro h
      obtain ⟨h1, h2⟩ := h64.1 h
      obtain ⟨k1, k2⟩ := h32.1 h1
      obtain ⟨k3, k4⟩ := h32'.1 h2
      apply hbr
      rw [mask16_test, msbBytes_land, msbBytes_mod_16, msbBytes_mod_16, msbBytes_land,
        msbBytes_land, msbBytes_cmpeq, msbBytes_cmpeq, msbBytes_cmpeq, msbBytes_cmpeq, hm, hm, hm,
        hm, hm, hm, hm, hm]
      exact ⟨⟨k1, k2⟩, k3, k4⟩
    simp only [hne, ite_false]

end Proof
