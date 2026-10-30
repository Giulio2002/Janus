import Extracted

/-!
# `A64Crc32(crc uint32, p []byte) uint32`: CRC-32 through `hash/crc32`'s arm64 CRC32X/W/H/B kernel

**Guarantee.** For every `crc`, every slice `p` (pointer, length `n`, capacity) and every Go call
state `s` of `example.com/basic.A64Crc32` such that
* the stack-growth prologue falls through (`GuardOK s 0`), `SP` is aligned and the bytes from
  120 below to 24 above `SP` are writable (the frames of `A64Crc32` and of the ABI wrapper
  `hash/crc32.ieeeUpdate`, the argument block of `hash/crc32.ieeeUpdate.abi0`, and the spill
  slot of `p` in the caller's argument area),
* `n < 2^63` (a Go length), the `n` bytes at `p` are readable and do not overlap that stack
  window,

the call returns (never faulting or panicking), obeys the ABI, and returns in `W0` the CRC-32 of
the `n` bytes continuing from `crc`: `crc32IEEE`, the textbook reflected CRC with polynomial
`0xEDB88320`, initial and final inversion (zlib's `crc32(crc, buf, n)`, Go's
`crc32.Update(crc, crc32.IEEETable, p)`), computed one byte at a time by eight register shifts
(`Janus.Arm64.CRC.update`). This holds for every length.

**What this covers.** `A64Crc32` is `^ieeeUpdate(^crc, p)` with `ieeeUpdate` linked to
`hash/crc32`'s own assembly (`//go:linkname`): exactly what `crc32.Update` runs on a CPU with the
CRC32 instructions once its one-time initialisation is done. The proof executes the Go function,
the ABIInternal-to-ABI0 wrapper and the assembly instruction by instruction from the extracted
words: the 16-byte loop (`LDP.P` + two `CRC32X`, `loop`) and the 8/4/2/1-byte tail (`TBZ`,
post-indexed loads, `CRC32X`/`CRC32W`/`CRC32H`/`CRC32B`, `tail`, all 16 remainders). The
instructions' semantics is the ASL transcription `crc32Op` (`Janus.Arm64.Crypto`); that it is
the bytewise CRC is proved once for all inputs in `Janus.Arm64.CryptoLemmas` (`crc32Op_eq_update`).
-/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
namespace Proof

set_option linter.unusedSimpArgs false
/-- The loop head `CMP $16, R11` of `hash/crc32.ieeeUpdate.abi0` (offset `0xc`). Code addresses
are evaluated from the extraction (`janus_eval%`), so a relinked binary needs no edit. -/
abbrev head : Nat := janus_eval% (segAddr Extracted.program "hash/crc32.ieeeUpdate.abi0" + 0xc)

/-- The return address into the ABI wrapper `hash/crc32.ieeeUpdate` (after its `BL`, offset `0x20`),
as a numeral evaluated from the extraction (a macro, so `janus_run` sees a literal). -/
local macro "wrapRet" : term =>
  `(janus_eval% (segAddr Extracted.program "hash/crc32.ieeeUpdate" + 0x20))

/-- The return address into `A64Crc32` (after its `BL`, offset `0x24`), as a numeral. -/
local macro "crcRet" : term => `(janus_eval% (Extracted.entry + 0x24))
abbrev R : Nat := 0xEDB88320

/-- `X < 2^32` for the CRC register terms of the tail. -/
macro "crc_lt" : tactic => `(tactic| repeat (first
  | (with_reducible assumption)
  | (with_reducible exact crc32Op_lt _ _ _ _)
  | (with_reducible apply CRC.update_lt (by decide))))

theorem readLE_mod_of_le (m : Memory) (a n M : Nat) (h : 256 ^ n ≤ M) : m.readLE a n % M = m.readLE a n :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Memory.readLE_lt m a n) h)

theorem crc32Op_mod (C : Bool) (size acc val M : Nat) (h : 2 ^ 32 ≤ M) :
    crc32Op C size acc val % M = crc32Op C size acc val :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (crc32Op_lt C size acc val) h)

theorem not_mod32 (x : Nat) (hx : x < 2 ^ 32) :
    (~~~BitVec.ofNat 64 x).toNat % 4294967296 = x ^^^ 4294967295 := by
  rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega),
    show (4294967296 : Nat) = 2 ^ 32 from rfl, show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl,
    show 2 ^ 64 - 1 - x = 2 ^ 64 - (x + 1) by omega]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_succ (by omega), Nat.testBit_xor,
    Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 32
  · simp [hj, show j < 64 by omega]
  · simp [hj, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (show 32 ≤ j by omega)))]

set_option maxHeartbeats 4000000 in
theorem tail (crc p n cap : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hlen : n.toNat < 2 ^ 63)
    (hp : s.mem.accessible p.toNat n.toNat false = true) (hp' : p.toNat + n.toNat ≤ 2 ^ 48)
    (hb : 120 ≤ s.sp.toNat) (ha : s.sp.toNat + 24 ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0)
    (hw : s.mem.accessible (s.sp.toNat - 120) (120 + 24) true = true)
    (hd : p.toNat + n.toNat ≤ s.sp.toNat - 120 ∨ s.sp.toNat - 120 + 144 ≤ p.toNat) :
    ∀ (S : State) (i acc : Nat), n.toNat - 16 * i < 16 → 16 * i ≤ n.toNat →
      acc = CRC.update R s.mem ((crc.toNat % 2 ^ 32) ^^^ 0xFFFFFFFF) p.toNat (16 * i) →
      S.pc = BitVec.ofNat 64 head → S.regs 9 = BitVec.ofNat 64 acc →
      S.regs 13 = BitVec.ofNat 64 (p.toNat + 16 * i) → S.regs 11 = BitVec.ofNat 64 (n.toNat - 16 * i) →
      S.regs 30 = BitVec.ofNat 64 wrapRet → S.regs 29 = s.sp - 120#64 → S.sp = s.sp - 112#64 →
      S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
      S.mem = (((((((((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
                                          (BitVec.toNat (s.regs 29))).writeLE
                                      (BitVec.toNat s.sp + 16) 8 p.toNat).writeLE
                                  (BitVec.toNat s.sp - 112) 8 crcRet).writeLE
                              (BitVec.toNat s.sp - 120) 8 (BitVec.toNat s.sp - 56)).writeLE
                          (BitVec.toNat s.sp - 32) 8 p.toNat).writeLE
                      (BitVec.toNat s.sp - 104) 4 (~~~crc).toNat).writeLE
                  (BitVec.toNat s.sp - 96) 8 p.toNat).writeLE
              (BitVec.toNat s.sp - 88) 8 n.toNat).writeLE
          (BitVec.toNat s.sp - 80) 8 cap.toNat →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat % 2 ^ 32 =
          CRC.update R s.mem ((crc.toNat % 2 ^ 32) ^^^ 0xFFFFFFFF) p.toNat n.toNat ^^^ 0xFFFFFFFF) := by
  intro S i acc hq hi hacc hpc h9 h13 h11 h30 h29 hsp h28 h18 hm
  generalize hk : n.toNat - 16 * i = r at h11 hq
  have hA : acc < 2 ^ 32 := hacc ▸ CRC.update_lt (by decide) _ _ _ _
    (Nat.xor_lt_two_pow (Nat.mod_lt _ (by decide)) (by decide))
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨
      r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by omega
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i by omega]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (1) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (2) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (2 + (1)) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (4) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (4 + (1)) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (4 + (2)) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (4 + (2 + (1))) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (8) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (8 + (1)) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (8 + (2)) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (8 + (2 + (1))) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (8 + (4)) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (8 + (4 + (1))) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (8 + (4 + (2))) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
  · janus_run
    try simp (disch := decide) only [readLE_mod_of_le, crc32Op_mod, Nat.mod_eq_of_lt hA]
    rw [not_mod32 _ (by crc_lt)]
    try simp (disch := crc_lt) only [crc32Op_64, crc32Op_32, crc32Op_16, crc32Op_8, Bool.false_eq_true, ite_false]
    refine congrArg (· ^^^ 4294967295) ?_
    rw [hacc]
    rw [show n.toNat = 16 * i + (8 + (4 + (2 + (1)))) by omega]
    simp only [CRC.update_add, Nat.add_assoc]
set_option maxHeartbeats 4000000 in
theorem loop (crc p n cap : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hlen : n.toNat < 2 ^ 63)
    (hp : s.mem.accessible p.toNat n.toNat false = true) (hp' : p.toNat + n.toNat ≤ 2 ^ 48)
    (hb : 120 ≤ s.sp.toNat) (ha : s.sp.toNat + 24 ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0)
    (hw : s.mem.accessible (s.sp.toNat - 120) (120 + 24) true = true)
    (hd : p.toNat + n.toNat ≤ s.sp.toNat - 120 ∨ s.sp.toNat - 120 + 144 ≤ p.toNat) :
    ∀ q (S : State) (i acc : Nat), n.toNat - 16 * i < 16 * (q + 1) → 16 * i ≤ n.toNat →
      acc = CRC.update R s.mem ((crc.toNat % 2 ^ 32) ^^^ 0xFFFFFFFF) p.toNat (16 * i) →
      S.pc = BitVec.ofNat 64 head → S.regs 9 = BitVec.ofNat 64 acc →
      S.regs 13 = BitVec.ofNat 64 (p.toNat + 16 * i) → S.regs 11 = BitVec.ofNat 64 (n.toNat - 16 * i) →
      S.regs 30 = BitVec.ofNat 64 wrapRet → S.regs 29 = s.sp - 120#64 → S.sp = s.sp - 112#64 →
      S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
      S.mem = (((((((((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
                                          (BitVec.toNat (s.regs 29))).writeLE
                                      (BitVec.toNat s.sp + 16) 8 p.toNat).writeLE
                                  (BitVec.toNat s.sp - 112) 8 crcRet).writeLE
                              (BitVec.toNat s.sp - 120) 8 (BitVec.toNat s.sp - 56)).writeLE
                          (BitVec.toNat s.sp - 32) 8 p.toNat).writeLE
                      (BitVec.toNat s.sp - 104) 4 (~~~crc).toNat).writeLE
                  (BitVec.toNat s.sp - 96) 8 p.toNat).writeLE
              (BitVec.toNat s.sp - 88) 8 n.toNat).writeLE
          (BitVec.toNat s.sp - 80) 8 cap.toNat →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat % 2 ^ 32 =
          CRC.update R s.mem ((crc.toNat % 2 ^ 32) ^^^ 0xFFFFFFFF) p.toNat n.toNat ^^^ 0xFFFFFFFF) := by
  intro q
  induction q with
  | zero =>
    intro S i acc hq
    exact tail crc p n cap ret hret s hlen hp hp' hb ha hal hw hd S i acc (by omega)
  | succ q ih =>
    intro S i acc hq hi hacc hpc h9 h13 h11 h30 h29 hsp h28 h18 hm
    by_cases hr : n.toNat - 16 * i < 16
    · exact tail crc p n cap ret hret s hlen hp hp' hb ha hal hw hd S i acc hr hi hacc hpc h9 h13 h11
        h30 h29 hsp h28 h18 hm
    have hA : acc < 2 ^ 32 := hacc ▸ CRC.update_lt (by decide) _ _ _ _
      (Nat.xor_lt_two_pow (Nat.mod_lt _ (by decide)) (by decide))
    have hacc' : crc32Op false 64
        (crc32Op false 64 (acc % 4294967296) (s.mem.readLE (p.toNat + 16 * i) 8) % 18446744073709551616 %
          4294967296) (s.mem.readLE (p.toNat + 16 * i + 8) 8) =
        CRC.update R s.mem ((crc.toNat % 2 ^ 32) ^^^ 0xFFFFFFFF) p.toNat (16 * (i + 1)) := by
      rw [Nat.mod_eq_of_lt hA, crc32Op_mod _ _ _ _ _ (by decide), crc32Op_mod _ _ _ _ _ (by decide),
        crc32Op_64 _ _ _ _ hA, crc32Op_64 _ _ _ _ (by crc_lt), show 16 * (i + 1) = 16 * i + (8 + 8) by omega,
        CRC.update_add, CRC.update_add, hacc]
      simp only [Nat.add_assoc, Bool.false_eq_true, ite_false]
    janus_run until [head]
    apply ih _ (i + 1) _ (by omega) (by omega) rfl
    all_goals janus_simp [hacc']
    all_goals first
      | omega
      | (apply BitVec.eq_of_toNat_eq
         simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
         omega)

/-- CRC-32 (the IEEE 802.3 / zlib / `hash/crc32.IEEE` polynomial, reflected `0xEDB88320`) of the
`n` bytes at `p`, continuing from `crc`: zlib's `crc32(crc, buf, n)`, Go's
`crc32.Update(crc, crc32.IEEETable, buf)`. -/
def crc32IEEE (m : Memory) (crc p n : Nat) : Nat :=
  CRC.update 0xEDB88320 m (crc ^^^ 0xFFFFFFFF) p n ^^^ 0xFFFFFFFF

theorem not_mod32' (x : BitVec 64) : (~~~x).toNat % 2 ^ 32 = x.toNat % 2 ^ 32 ^^^ 4294967295 := by
  have := not_mod32 (x.toNat % 2 ^ 32) (Nat.mod_lt _ (by decide))
  rw [← this]
  simp only [BitVec.toNat_not, BitVec.toNat_ofNat]
  omega

theorem not_mod32'' (x : BitVec 64) :
    (18446744073709551615 - x.toNat) % 4294967296 = x.toNat % 4294967296 ^^^ 4294967295 := by
  have := not_mod32' x
  simp only [BitVec.toNat_not] at this
  exact this

theorem update_zero (m : Memory) (c p : Nat) : CRC.update R m c p 0 = c := rfl

set_option maxHeartbeats 4000000 in
/-- **The theorem.** -/
theorem correctness (crc p n cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [crc, p, n, cap]
      (fun s => GuardOK s 0 ∧ StackOK s 120 24 ∧ n.toNat < 2 ^ 63 ∧ Ptr s.mem p n.toNat false ∧
        Disjoint p.toNat n.toNat (s.sp.toNat - 120) 144)
      (fun s s' => (s'.regs 0).toNat % 2 ^ 32 = crc32IEEE s.mem (crc.toNat % 2 ^ 32) p.toNat n.toNat) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hlen, ⟨hp, hp'⟩, hd⟩
  janus_intro hs
  simp only [Disjoint] at hd
  janus_run until [head]
  exact loop crc p n cap ret hret s hlen hp hp' hb ha hal hw hd (n.toNat / 16) _ 0 _ (by omega) (by omega) rfl
    (by janus_simp) (by janus_simp [update_zero]; rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, not_mod32']) (by janus_simp) (by janus_simp <;> simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)

end Proof
