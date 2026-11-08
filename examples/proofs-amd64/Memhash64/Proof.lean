import Janus
import Extracted

/-! `runtime.memhash64(p unsafe.Pointer, h uintptr) uintptr` on amd64 (Go assembly, ABIInternal:
`AX = p`, `BX = h`): the hash of every 8-byte map key.

```
CMPB runtime·useAeshash(SB), $0 ; JEQ noaes
MOVQ BX, X0 ; PINSRQ $1, (AX), X0
AESENC runtime·aeskeysched+0(SB), X0 ; AESENC ...+16(SB), X0 ; AESENC ...+32(SB), X0
MOVQ X0, AX ; RET
noaes: JMP runtime·memhash64Fallback(SB)
```

**Guarantee.** For every `p` with 8 readable bytes and every seed `h`, with the runtime's
`useAeshash`, `aeskeysched` (48 bytes) and `hashkey` (16 bytes) readable, the call returns
`Janus.Spec.MemHash.aesHash64 k0 k1 k2 h v` (three FIPS-197 AES rounds keyed by the three
16-byte round keys of `aeskeysched`, on the seed in the low and the data in the high quadword,
low quadword returned) when `useAeshash ≠ 0` (every CPU with AES-NI), and
`fallbackHash64 hashkey[0] hashkey[1] h v` (`memhash64Fallback`) otherwise. The AES path goes
through `Janus.Spec.AES.aesenc_eq`: `AESENC` is the FIPS-197 round. In terms of
`Janus.Contracts.Hash.HashModel`, `mem64 = aesHash64 k0 k1 k2` for the process key schedule.
Every address (`useAeshash`, `aeskeysched`, `hashkey`) is read off the code (`ripTarget`). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `runtime.useAeshash` (the `CMPB` at the entry). -/
def useAes : Nat := ripTarget Extracted.program Extracted.entry
/-- `runtime.aeskeysched` (the first `AESENC`, at offset 21). -/
def keys : Nat := ripTarget Extracted.program (Extracted.entry + 21)
/-- `runtime.hashkey` (the first instruction of `memhash64Fallback`, `hashkey[1]`, minus 8). -/
def hashkey : Nat := ripTarget Extracted.program (segAddr Extracted.program "runtime.memhash64Fallback") - 8

theorem correctness (p h : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, h]
      (fun s => StackWritable s 0 8 ∧ s.mem.accessible useAes 1 false = true ∧
        s.mem.accessible keys 48 false = true ∧ s.mem.accessible hashkey 16 false = true ∧
        Buffer s p 8 false)
      (fun s s' => results 1 s' = [BitVec.ofNat 64 (if s.mem.readLE useAes 1 ≠ 0 then
        Janus.Spec.MemHash.aesHash64 (s.mem.readLE keys 16) (s.mem.readLE (keys + 16) 16)
          (s.mem.readLE (keys + 32) 16) h.toNat (s.mem.readLE p.toNat 8)
        else Janus.Spec.MemHash.fallbackHash64 (s.mem.readLE hashkey 8) (s.mem.readLE (hashkey + 8) 8)
          h.toNat (s.mem.readLE p.toNat 8))]) := by
  intro ret hret s hs hpre
  simp only [useAes, keys, hashkey] at *
  janus64_addrs
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, hua, hk, hhk, hpb, hp⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  have hv := Janus.Arm64.Memory.readLE_lt s.mem p.toNat 8
  janus64_run
  · -- runtime.useAeshash = 0: memhash64Fallback
    rw [ite_eq_left (Janus.Spec.MemHash.readLE1_eq_zero hbr)]
    first | with_reducible congr 1 | congr 1
    simp only [Janus.Spec.MemHash.mix_bv, Janus.Spec.MemHash.fallbackHash64_eq, BitVec.toNat_ofNat,
      BitVec.toNat_xor, Janus.Spec.MemHash.readLE8_mod]
    rw [Nat.mod_eq_of_lt (Janus.Spec.MemHash.mix_lt _ _
      (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Janus.Spec.MemHash.readLE_lt64 _ _ 8 (by decide)) h.isLt) (Janus.Spec.MemHash.readLE_lt64 _ _ 8 (by decide)))
      (Nat.xor_lt_two_pow (Janus.Spec.MemHash.readLE_lt64 _ _ 8 (by decide)) (Janus.Spec.MemHash.readLE_lt64 _ _ 8 (by decide))))]
  · rw [ite_eq_right (Janus.Spec.MemHash.readLE1_ne_zero hbr)]
    first | with_reducible congr 1 | congr 1
    simp only [Janus.Spec.MemHash.pinsrq_hi, Janus.Spec.MemHash.pinsrq_hi', Janus.Spec.MemHash.pinsrq_hi_eq, Janus.Spec.MemHash.setWidth_ofNat_128,
      Janus.Spec.AES.aesenc_eq, Janus.Spec.MemHash.aesHash64, Janus.Spec.MemHash.round']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.mod_mod]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def p : BitVec 64 := 0x30800#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
def h : BitVec 64 := 7#64

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then p else if r_ = 3 then h else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := ⟨wmem64.bytes, wmem64.regions ++ [⟨useAes, 1, false⟩, ⟨keys, 48, false⟩, ⟨hashkey, 16, false⟩]⟩ }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [p, h] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ s.mem.accessible useAes 1 false = true ∧
        s.mem.accessible keys 48 false = true ∧ s.mem.accessible hashkey 16 false = true ∧
        Buffer s p 8 false) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Amd64.Program.DataLoaded]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (p : BitVec 64) (h : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [p, h] s ∧ (StackWritable s 0 8 ∧ s.mem.accessible useAes 1 false = true ∧
        s.mem.accessible keys 48 false = true ∧ s.mem.accessible hashkey 16 false = true ∧
        Buffer s p 8 false) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ results 1 s' = [BitVec.ofNat 64 (if s.mem.readLE useAes 1 ≠ 0 then
        Janus.Spec.MemHash.aesHash64 (s.mem.readLE keys 16) (s.mem.readLE (keys + 16) 16)
          (s.mem.readLE (keys + 32) 16) h.toNat (s.mem.readLE p.toNat 8)
        else Janus.Spec.MemHash.fallbackHash64 (s.mem.readLE hashkey 8) (s.mem.readLE (hashkey + 8) 8)
          h.toNat (s.mem.readLE p.toNat 8))]) :=
  ⟨ret, s0, p, h, hret, setup, hpre, correctness p h ret hret s0 setup hpre⟩

end Witness

end Proof
