import Janus
import Extracted

/-! `crypto/internal/fips140/aes.encryptBlockAsm(nr int, xk *uint32, dst, src *byte)` on amd64
(Go assembly, ABI0): one block of AES encryption with AES-NI (`PXOR` of round key 0, `nr - 1`
`AESENC`, one `AESENCLAST`, the round keys loaded from `xk` with `MOVUPS`).

**Guarantee** (`correctness`). For `nr ∈ {10, 12, 14}`, every key schedule of `4(nr + 1)` words
readable at `xk`, every readable `src` and writable `dst` (not overlapping the return-address
slot; `src` and `dst` may be the same block), the call returns and writes exactly
`Janus.Spec.AES.cipher nr w in` to `dst` — FIPS-197's `Cipher` (§5.1, written independently of the
ISA model in `Janus/Spec/AES.lean`) with `w` the words at `xk` and `in` the 16 bytes at `src` —
and nothing else. `corollaryAES128`: when the words at `xk` are FIPS-197's `KeyExpansion` of a
key, `dst = AES-128(key, src)`. `corollaryFIPS197`: the appendix C.1 vector through the machine
code (`fips197_C1` is checked by the kernel). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec.AES

set_option maxHeartbeats 3000000 in
theorem correctness (nr xk dst src : BitVec 64) (hnr : nr = 10#64 ∨ nr = 12#64 ∨ nr = 14#64) :
    Ensures0 Extracted.program Extracted.entry [nr, xk, dst, src] 0
      (fun s => Buffer s xk (16 * (nr.toNat + 1)) false ∧ Buffer s src 16 false ∧
        Buffer s dst 16 true ∧ Disjoint dst 16 (s.regs 4) 8)
      (fun s s' => s'.mem.readLE dst.toNat 16 =
          cipher nr.toNat (schedule s.mem xk.toNat (4 * (nr.toNat + 1))) (s.mem.readLE src.toNat 16) ∧
        Janus.Spec.OnlyWrites s.mem s'.mem dst.toNat 16) := by
  intro ret hret s hs ⟨⟨hxb, hx⟩, ⟨hsb, hsa⟩, ⟨hdb, hda⟩, hdisj⟩
  janus64_intro0 hs
  simp only [Disjoint] at hdisj
  rcases hnr with rfl | rfl | rfl <;> simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul] at hx hxb ⊢ <;>
    janus64_run <;>
    simp only [cipher, rounds, round, aesenc_eq, aesenclast_eq, addRoundKey, BitVec.toNat_xor,
      BitVec.toNat_ofNat, Janus.Tactic.readLE_mod_16, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero,
      Nat.mul_zero, Nat.reducePow] <;>
    simp (disch := decide) only [roundKey_schedule, Nat.reduceMul, Nat.add_zero, true_and] <;>
    exact Janus.Spec.onlyWrites_writeLE _ (Janus.Spec.onlyWrites_refl _ _ _) (by omega) (by omega)

/-- **AES-128.** If the 44 words at `xk` are the FIPS-197 key expansion of `key` (what
`crypto/aes.NewCipher` stores there through `expandKeyAsm`), `encryptBlockAsm(10, xk, dst, src)`
writes `AES-128(key, src)` to `dst`. -/
theorem corollaryAES128 (key : Nat) (xk dst src : BitVec 64) :
    Ensures0 Extracted.program Extracted.entry [10#64, xk, dst, src] 0
      (fun s => Buffer s xk 176 false ∧ Buffer s src 16 false ∧ Buffer s dst 16 true ∧
        Disjoint dst 16 (s.regs 4) 8 ∧
        ∀ i, i < 44 → s.mem.readLE (xk.toNat + 4 * i) 4 = (keyExpansion 4 10 key).getD i 0)
      (fun s s' => s'.mem.readLE dst.toNat 16 = aes128 key (s.mem.readLE src.toNat 16)) :=
  (correctness 10#64 xk dst src (Or.inl rfl)).mono (fun _ ⟨a, b, c, d, _⟩ => ⟨a, b, c, d⟩)
    fun s _ ⟨_, _, _, _, hw⟩ ⟨h, _⟩ => by
      rw [h, aes128, ← schedule_eq s.mem xk.toNat 44 _ (length_keyExpansion 4 10 key (by decide)) hw]
      rfl

/-- **The FIPS-197 appendix C.1 vector**, through the machine code: with the expanded key of
`000102...0f` at `xk` and the block `00112233...ff` at `src`, the call writes
`69c4e0d86a7b0430d8cdb78070b4c55a` to `dst` (`fips197_C1`, checked by the kernel). -/
theorem corollaryFIPS197 (xk dst src : BitVec 64) :
    Ensures0 Extracted.program Extracted.entry [10#64, xk, dst, src] 0
      (fun s => Buffer s xk 176 false ∧ Buffer s src 16 false ∧ Buffer s dst 16 true ∧
        Disjoint dst 16 (s.regs 4) 8 ∧
        (∀ i, i < 44 → s.mem.readLE (xk.toNat + 4 * i) 4 = (keyExpansion 4 10 (countKey 16)).getD i 0) ∧
        s.mem.readLE src.toNat 16 = plainC)
      (fun _ s' => s'.mem.readLE dst.toNat 16 = ofBytes [0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04,
        0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5, 0x5a]) :=
  (corollaryAES128 (countKey 16) xk dst src).mono (fun _ ⟨a, b, c, d, e, _⟩ => ⟨a, b, c, d, e⟩)
    fun _ _ ⟨_, _, _, _, _, hp⟩ h => by rw [h, hp, fips197_C1]

end Proof
