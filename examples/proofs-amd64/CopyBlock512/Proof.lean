import Janus
import Extracted

/-! `example.com/basic.CopyBlock512(dst, src *[64]uint64)` on amd64: `copy(dst[:], src[:])`,
which the compiler lowers to a call of `runtime.memmove(dst, src, 512)` (skipped when
`dst = src`).

```
CMPQ SP, 16(R14) ; JBE morestack ; PUSHQ BP ; MOVQ SP, BP ; SUBQ $0x18, SP
TESTB AL, (AX) ; TESTB AL, (BX)          // nil checks
CMPQ BX, AX ; JEQ done ; MOVL $0x200, CX ; CALL runtime.memmove
done: ADDQ $0x18, SP ; POPQ BP ; RET
```

`runtime.memmove` (Go 1.26, `runtime/memmove_amd64.s`) is executed in full. Above 256 bytes it
reads `runtime.memmoveBits`, which Go sets at start-up: bit 0 (`avxSupported`) when the CPU has
AVX, bit 1 (`repmovsPreferred`) on Intel CPUs with ERMS and FSRM. With bit 0 set every path
(`memmoveBits = 1` directly; otherwise through the forward or the backward-overlap check)
reaches `avxUnaligned`. For disjoint arrays that is the forward copy:

* the last 128 bytes of `src` are loaded into `X5`–`X12` (`MOVDQU`) and the first 32 into `Y4`
  (`VMOVDQU`);
* `DI` is rounded up to the next 32-byte boundary, `dst + r` with `r = 32 - dst mod 32`
  (`ANDQ $-32, DI ; ADDQ $32, DI`), and the body `[r, r + 384)` is copied by `gobble_128_loop`:
  four `VMOVDQU` loads and four 32-byte-aligned `VMOVDQA` stores per iteration, three
  iterations for every `r ∈ [1, 32]`;
* the head (`VMOVDQU Y4, (R10)`), `VZEROUPPER`, and the tail (eight `MOVDQU` stores) are
  stored last. They overlap the body, with the same bytes.

`avx_copy` proves this from `avxEntry` for every destination alignment; the overlapping stores
are resolved byte by byte (`copied_writes`, `Janus.Amd64.TacticAVX`), and the `VMOVDQA`
alignment checks by `land_align32`/`align32_add_mod`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

attribute [local irreducible] Janus.Arm64.Memory.readLE

/-- `runtime.memmoveBits` (`.noptrbss`) in this binary. -/
def memmoveBits : Nat := 0x578ab0

/-- `memmove`: `avxUnaligned`, the AVX path. -/
def avxEntry : Nat := 0x47d9aa
/-- `CopyBlock512`: the instruction after `CALL runtime.memmove`. -/
def retSite : Nat := 0x4899c5

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `memmove`'s AVX path from `avxUnaligned`, for 512 bytes from `c` to `d` (disjoint): it
returns to `retSite` with `RSP` popped, `RBP`, `R14` and `X15` unchanged, the 512 bytes at `d`
equal to the old 512 bytes at `c`, and no other byte changed. The destination needs no
alignment. -/
theorem avx_copy (ret : Nat) (hret : RetAddr Extracted.program ret) (Q : Outcome → Prop)
    (t : State) (d c : Nat) (h_rip : t.rip = BitVec.ofNat 64 avxEntry)
    (h7 : t.regs 7 = BitVec.ofNat 64 d) (h6 : t.regs 6 = BitVec.ofNat 64 c)
    (h3 : t.regs 3 = 512#64) (hd : d + 512 ≤ 2 ^ 48) (hc : c + 512 ≤ 2 ^ 48)
    (hdc : d + 512 ≤ c ∨ c + 512 ≤ d)
    (hacc : t.mem.accessible d 512 true = true) (hcacc : t.mem.accessible c 512 false = true)
    (hR : t.mem.accessible (t.regs 4).toNat 8 false = true)
    (hRd : d + 512 ≤ (t.regs 4).toNat ∨ (t.regs 4).toNat + 8 ≤ d)
    (hra : t.mem.readLE (t.regs 4).toNat 8 = retSite)
    (hk : ∀ t', t'.rip = BitVec.ofNat 64 retSite → t'.regs 4 = t.regs 4 + 8 →
      t'.regs 5 = t.regs 5 → t'.regs 14 = t.regs 14 → t'.xmm 15 = t.xmm 15 →
      t'.mem.readLE d 512 = t.mem.readLE c 512 → t'.mem.regions = t.mem.regions →
      (∀ x, x < d ∨ d + 512 ≤ x → t'.mem.bytes x = t.mem.bytes x) →
      Reaches (Extracted.program.withExit ret) t' Q) :
    Reaches (Extracted.program.withExit ret) t Q := by
  simp only [avxEntry, retSite] at *
  have hR' := (t.regs 4).isLt
  have hand : BitVec.ofNat 64 d &&& 18446744073709551584#64 = BitVec.ofNat 64 (d - d % 32) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega), land_align32 _ (by omega)]
    omega
  have hsub : ∀ x y : Nat, y ≤ x → x < 2 ^ 64 → BitVec.ofNat 64 x - BitVec.ofNat 64 y = BitVec.ofNat 64 (x - y) :=
    fun x y h1 h2 => BitVec.ofNat_sub_ofNat_of_le x y (by omega) h1
  janus64_run [hand, BitVec.ofNat_add_ofNat, hsub, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_false, Bool.or_eq_true, decide_eq_true_eq] until [4757957]
  refine hk _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setXmmF])
    ?_ (by simp only [Janus.Arm64.Memory.regions_writeLE]) ?_
  · apply readLE_of_bytes
    intro i hi
    copied_writes
  · intro x hx
    repeat (refine cb_skip (by omega) ?_)
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `CopyBlock512(dst, src)` leaves the 512 bytes at `dst` equal to the 512 bytes that were at
`src`, on a CPU where Go detected AVX (`memmoveBits` has bit 0 set; `repmovsPreferred` may be
either). The arrays must be accessible (`dst` writable) and disjoint from each other, `dst`
must not overlap the frame or the return address (`[RSP - 40, RSP + 8)`), `src` not the frame
(`[RSP - 40, RSP)`), and the feature byte must be readable and overlap neither the frame nor
`dst`. -/
theorem correctness (dst src : BitVec 64) :
    Ensures Extracted.program Extracted.entry [dst, src]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s dst 512 true ∧
        Buffer s src 512 false ∧ Disjoint dst 512 src 512 ∧
        (dst.toNat + 512 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ dst.toNat) ∧
        (src.toNat + 512 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat ≤ src.toNat) ∧
        s.mem.accessible memmoveBits 1 false = true ∧ s.mem.readLE memmoveBits 1 % 2 = 1 ∧
        (memmoveBits + 1 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat ≤ memmoveBits) ∧
        (dst.toNat + 512 ≤ memmoveBits ∨ memmoveBits + 1 ≤ dst.toNat))
      (fun s s' => valueAt s' dst 512 = valueAt s src 512) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hg, ⟨hle, hnw, hacc⟩, ⟨hdw, hd⟩, ⟨hsw, hsa⟩, hds, hdd, hsd, hmb, hmb1, hmbd, hmbd'⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr hdd hsd
  simp only [memmoveBits, regSP, Disjoint] at hmb hmb1 hmbd hmbd' hds
  simp only [valueAt]
  have hdl := dst.isLt
  have hsl := src.isLt
  have hsp := (s.regs 4).isLt
  have e40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run until [0x47d9aa]
  all_goals
    refine avx_copy ret hret _ _ dst.toNat src.toNat rfl (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    simp (config := { decide := true }) only [setRegF, ↓reduceIte, e40,
      Janus.Arm64.Memory.accessible_writeLE]
  all_goals first
    | exact hdw
    | exact hsa
    | exact accessible_sub hacc (by decide) (by omega) (by omega)
    | omega
    | (rw [Janus.Arm64.Memory.readLE_writeLE_self]; rfl)
    | skip
  all_goals
    -- back in `CopyBlock512` after the call: `ADDQ $0x18, SP ; POPQ BP ; RET`
    intro t' hrip h4' h5' h14' hx' hcp hreg hout
    simp only [retSite] at hrip
    have hbp : t'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
      rw [Janus.Arm64.Memory.readLE_congr (m' := _) (fun i hi => hout _ (by omega)),
        readLE_writeLE_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (s.regs 5).isLt]
    have hrt : t'.mem.readLE (s.regs 4).toNat 8 = ret := by
      rw [Janus.Arm64.Memory.readLE_congr (m' := _) (fun i hi => hout _ (by omega)),
        readLE_writeLE_disjoint _ _ (by omega), readLE_writeLE_disjoint _ _ (by omega), h_ret]
    have hacc' : t'.mem.accessible ((s.regs 4).toNat - 40) (40 + 8) true = true := by
      rw [Janus.Arm64.Memory.accessible_congr hreg]; simpa using hacc
    rw [readLE_writeLE_disjoint _ _ (by omega), readLE_writeLE_disjoint _ _ (by omega)] at hcp
    janus64_run

end Proof
