import Janus
import Extracted

/-! `runtime.memhash32(p unsafe.Pointer, h uintptr) uintptr` on amd64: as `Memhash64`, with the 4
data bytes inserted at dword 2 (`PINSRD $2, (AX), X0`) and `memhash32Fallback` on CPUs without
AES-NI. The result is `Janus.Spec.MemHash.aesHash32` (three FIPS-197 rounds) or
`fallbackHash32`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `runtime.useAeshash` (the `CMPB` at the entry). -/
def useAes : Nat := ripTarget Extracted.program Extracted.entry
/-- `runtime.aeskeysched` (the first `AESENC`, at offset 20). -/
def keys : Nat := ripTarget Extracted.program (Extracted.entry + 20)
/-- `runtime.hashkey` (the first instruction of `memhash32Fallback`, `hashkey[1]`, minus 8). -/
def hashkey : Nat := ripTarget Extracted.program (segAddr Extracted.program "runtime.memhash32Fallback") - 8

theorem correctness (p h : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, h]
      (fun s => StackWritable s 0 8 ∧ s.mem.accessible useAes 1 false = true ∧
        s.mem.accessible keys 48 false = true ∧ s.mem.accessible hashkey 16 false = true ∧
        Buffer s p 4 false)
      (fun s s' => results 1 s' = [BitVec.ofNat 64 (if s.mem.readLE useAes 1 ≠ 0 then
        Janus.Spec.MemHash.aesHash32 (s.mem.readLE keys 16) (s.mem.readLE (keys + 16) 16)
          (s.mem.readLE (keys + 32) 16) h.toNat (s.mem.readLE p.toNat 4)
        else Janus.Spec.MemHash.fallbackHash32 (s.mem.readLE hashkey 8) (s.mem.readLE (hashkey + 8) 8)
          h.toNat (s.mem.readLE p.toNat 4))]) := by
  intro ret hret s hs hpre
  simp only [useAes, keys, hashkey] at *
  janus64_addrs
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, hua, hk, hhk, hpb, hp⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  have hv := Janus.Arm64.Memory.readLE_lt s.mem p.toNat 4
  janus64_run
  · -- runtime.useAeshash = 0: memhash32Fallback
    rw [ite_eq_left (Janus.Spec.MemHash.readLE1_eq_zero hbr)]
    first | with_reducible congr 1 | congr 1
    simp only [Janus.Spec.MemHash.mix_bv, Janus.Spec.MemHash.fallbackHash32_eq, BitVec.toNat_ofNat,
      BitVec.toNat_xor, BitVec.toNat_setWidth, Janus.Spec.MemHash.readLE8_mod,
      Janus.Spec.MemHash.readLE4_mod, Janus.Spec.MemHash.readLE_mod64 _ _ 4 (by decide)]
    rw [Nat.mod_eq_of_lt (Janus.Spec.MemHash.mix_lt _ _
      (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Janus.Spec.MemHash.readLE_lt64 _ _ 4 (by decide)) h.isLt) (Janus.Spec.MemHash.readLE_lt64 _ _ 8 (by decide)))
      (Nat.xor_lt_two_pow (Janus.Spec.MemHash.readLE_lt64 _ _ 8 (by decide)) (Janus.Spec.MemHash.readLE_lt64 _ _ 4 (by decide))))]
  · rw [ite_eq_right (Janus.Spec.MemHash.readLE1_ne_zero hbr)]
    first | with_reducible congr 1 | congr 1
    simp only [Janus.Spec.MemHash.pinsrd_2 _ _ h.isLt, Janus.Spec.MemHash.pinsrd_2' _ _ h.isLt, Janus.Spec.MemHash.pinsrd_2_eq _ _ h.isLt, Janus.Spec.MemHash.setWidth_ofNat_128,
      Janus.Spec.AES.aesenc_eq, Janus.Spec.MemHash.aesHash32, Janus.Spec.MemHash.round']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.mod_mod]

end Proof
