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

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def nr : BitVec 64 := 0xa#64
def xk : BitVec 64 := 0x30800#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
def dst : BitVec 64 := 0x30b00#64
def src : BitVec 64 := 0x30a00#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
theorem hnr : nr = 10#64 ∨ nr = 12#64 ∨ nr = 14#64 := by decide

def s0 : State :=
  { regs := fun r_ => if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := ⟨fun a => if a = 294920 then 10#8 else if a = 294929 then 8#8 else if a = 294930 then 3#8 else if a = 294937 then 11#8 else if a = 294938 then 3#8 else if a = 294945 then 10#8 else if a = 294946 then 3#8 else wmem64.bytes a, wmem64.regions ++ []⟩ } -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
theorem setup : CallSetup0 (Extracted.program.withExit ret) Extracted.entry [nr, xk, dst, src] 0 s0 :=
  ⟨rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> (simp only [List.getElem_cons_zero, List.getElem_cons_succ]; decide), by unfold FrameOK; decide, rfl⟩
set_option maxRecDepth 100000 in
theorem hpre : (fun s => Buffer s xk (16 * (nr.toNat + 1)) false ∧ Buffer s src 16 false ∧
        Buffer s dst 16 true ∧ Disjoint dst 16 (s.regs 4) 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Amd64.Program.DataLoaded]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (nr : BitVec 64) (xk : BitVec 64) (dst : BitVec 64) (src : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup0 (Extracted.program.withExit ret) Extracted.entry [nr, xk, dst, src] 0 s ∧ (nr = 10#64 ∨ nr = 12#64 ∨ nr = 14#64) ∧ (Buffer s xk (16 * (nr.toNat + 1)) false ∧ Buffer s src 16 false ∧
        Buffer s dst 16 true ∧ Disjoint dst 16 (s.regs 4) 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn0 s s' ∧ s'.mem.readLE dst.toNat 16 =
          cipher nr.toNat (schedule s.mem xk.toNat (4 * (nr.toNat + 1))) (s.mem.readLE src.toNat 16) ∧
        Janus.Spec.OnlyWrites s.mem s'.mem dst.toNat 16) :=
  ⟨ret, s0, nr, xk, dst, src, hret, setup, hnr, hpre, correctness nr xk dst src hnr ret hret s0 setup hpre⟩

/-- The FIPS-197 C.1 call state: `s0` with the 176 bytes of the expanded key of `000102...0f` at `xk`
and the block `00112233...ff` at `src`. -/
def ksNat : Nat := (List.range 44).foldr (fun i acc => (keyExpansion 4 10 (countKey 16)).getD i 0 + 2 ^ 32 * acc) 0

def s1 : State := { s0 with mem := ((s0.mem.writeLE xk.toNat 176 ksNat).writeLE src.toNat 16 plainC) }

theorem setup1 : CallSetup0 (Extracted.program.withExit ret) Extracted.entry [10#64, xk, dst, src] 0 s1 :=
  ⟨rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> (simp only [List.getElem_cons_zero, List.getElem_cons_succ]; decide), by unfold FrameOK; decide, rfl⟩

set_option maxRecDepth 100000 in
theorem hpre1 : (fun s => Buffer s xk 176 false ∧ Buffer s src 16 false ∧ Buffer s dst 16 true ∧
        Disjoint dst 16 (s.regs 4) 8 ∧
        (∀ i, i < 44 → s.mem.readLE (xk.toNat + 4 * i) 4 = (keyExpansion 4 10 (countKey 16)).getD i 0) ∧
        s.mem.readLE src.toNat 16 = plainC) s1 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Amd64.Program.DataLoaded]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

/-- The hypotheses of `corollaryAES128` (for the key `countKey 16`) hold together, and the call returns. -/
theorem corollaryAES128 : ∃ (ret : Nat) (s : State) (key : Nat) (xk : BitVec 64) (dst : BitVec 64) (src : BitVec 64),
    RetAddr Extracted.program ret ∧
    CallSetup0 (Extracted.program.withExit ret) Extracted.entry [10#64, xk, dst, src] 0 s ∧
    (Buffer s xk 176 false ∧ Buffer s src 16 false ∧ Buffer s dst 16 true ∧
        Disjoint dst 16 (s.regs 4) 8 ∧
        ∀ i, i < 44 → s.mem.readLE (xk.toNat + 4 * i) 4 = (keyExpansion 4 10 key).getD i 0) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn0 s s' ∧ s'.mem.readLE dst.toNat 16 = aes128 key (s.mem.readLE src.toNat 16)) :=
  ⟨ret, s1, countKey 16, xk, dst, src, hret, setup1, (let ⟨a, b, c, d, e, _⟩ := hpre1; ⟨a, b, c, d, e⟩),
    Proof.corollaryAES128 (countKey 16) xk dst src ret hret s1 setup1 (let ⟨a, b, c, d, e, _⟩ := hpre1; ⟨a, b, c, d, e⟩)⟩

/-- The hypotheses of `corollaryFIPS197` hold together, and the call returns. -/
theorem corollaryFIPS197 : ∃ (ret : Nat) (s : State) (xk : BitVec 64) (dst : BitVec 64) (src : BitVec 64),
    RetAddr Extracted.program ret ∧
    CallSetup0 (Extracted.program.withExit ret) Extracted.entry [10#64, xk, dst, src] 0 s ∧
    (Buffer s xk 176 false ∧ Buffer s src 16 false ∧ Buffer s dst 16 true ∧
        Disjoint dst 16 (s.regs 4) 8 ∧
        (∀ i, i < 44 → s.mem.readLE (xk.toNat + 4 * i) 4 = (keyExpansion 4 10 (countKey 16)).getD i 0) ∧
        s.mem.readLE src.toNat 16 = plainC) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn0 s s' ∧ s'.mem.readLE dst.toNat 16 = ofBytes [0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04,
        0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5, 0x5a]) :=
  ⟨ret, s1, xk, dst, src, hret, setup1, hpre1, Proof.corollaryFIPS197 xk dst src ret hret s1 setup1 hpre1⟩

end Witness

end Proof
