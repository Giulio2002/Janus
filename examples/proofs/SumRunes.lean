import Extracted

/-!
# `SumRunes(s string) uint64` sums the code points `for range s` yields (arm64)

**Guarantee.** For every string `s = (p, n)` and every Go call state of
`example.com/basic.SumRunes` with the stack guard 48 bytes below `SP` (so neither SumRunes' nor
`runtime.decoderune`'s stack check grows the stack), the stack window `[SP-4144, SP+24)` writable,
the string readable and outside the window, and `g`'s guard word outside it: the call returns,
obeys the ABI, and `X0` is `sumRunes (bytes of s)`: the sum, modulo `2^64`, of the runes Go's
`for range` produces, with U+FFFD for every invalid UTF-8 sequence (`Janus/Spec/String.lean`,
checked against the Go runtime in `JanusTests/String.lean`).

In two layers. `correctness` proves SumRunes from `decoderune`'s contract alone (`RtContract …
decoderuneSpec`, `Janus/Contracts/String.lean`), for every `rt` the window, string and guard word
are outside. `decoderune_meets` proves that the runtime's own code (extracted with SumRunes) meets
that contract for every `rt` and `H`; `runtime_correctness` combines the two, so nothing is
assumed, and `Witness` gives a concrete call state meeting the precondition.
`decoderune_satisfiable` is the contract's own witness.

**How.** `decoderune_meets` is one symbolic run over the 25 paths of `decoderune` (the bounds
checks, the three sequence lengths and their continuation-byte checks, the overlong, surrogate and
range checks); at each return the machine's rune is a mask-and-shift expression over the loaded
bytes (the field lemmas `r2`, `r3`, `r4`) and `decodeRune` is restated arithmetically
(`decodeRune_eq_arith`). `loop` is the invariant at the loop head (`cmp x1, x2`): `X3` plus the sum of the runes
from index `X2` on is the result, and memory differs from the prologue's only in `rt`,
`decoderune`'s window and the saved accumulator (`MemFrame`). One iteration either takes an
ASCII byte inline (`hasc`) or calls `decoderune` through its contract (`step_sum` with
`rangeStep`); the induction is on the bytes left.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
namespace Proof

/-! ## `runtime.decoderune`, from its code -/

/-- `runtime.decoderune`'s address. -/
def decAddr : Nat := segAddr Extracted.program "runtime.decoderune"

/-- Go's masked slice index (`AND Xd, Xk, (Xk - Xn) ASR #63`, Spectre hardening of `s[k:]`): `k`
when `k < n`. -/
theorem and_sshr_sub (a b : BitVec 64) (h : a.toNat < b.toNat) (hb : b.toNat < 2 ^ 63) :
    a.toNat &&& ((a - b).sshiftRight 63).toNat = a.toNat := by
  have hneg : (a - b).msb = true := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_sub]; simp only [decide_eq_true_eq]; omega
  have : (a - b).sshiftRight 63 = BitVec.allOnes 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_allOnes, hi, decide_true]
    split
    · rename_i h2
      obtain rfl : i = 0 := by omega
      simpa [BitVec.msb_eq_getLsbD_last] using hneg
    · simpa [hi] using hneg
  rw [this, BitVec.toNat_allOnes, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt a.isLt]

theorem bv_and63 (b : Nat) (h : b < 256) : (BitVec.ofNat 64 b &&& 63#64).toNat = b % 64 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b < 2^64)]
  exact Nat.and_two_pow_sub_one_eq_mod b 6
theorem bv_and31 (b : Nat) (h : b < 256) : (BitVec.ofNat 64 b &&& 31#64).toNat = b % 32 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b < 2^64)]
  exact Nat.and_two_pow_sub_one_eq_mod b 5
theorem bv_shl (x : BitVec 64) (i : Nat) (h : x.toNat * 2 ^ i < 2 ^ 64) : (x <<< i).toNat = x.toNat * 2 ^ i := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

set_option maxRecDepth 10000 in
theorem ubfiz12_4 : ∀ b, b < 256 →
    (BitVec.ofNat 64 b).rotateRight 52 &&& 61440#64 &&& 65535#64 = BitVec.ofNat 64 (b % 16 * 4096) := by
  decide +kernel
set_option maxRecDepth 10000 in
theorem ubfiz18_3 : ∀ b, b < 256 →
    (BitVec.ofNat 64 b).rotateRight 46 &&& 1835008#64 &&& 2097151#64 = BitVec.ofNat 64 (b % 8 * 262144) := by
  decide +kernel

theorem r2 (b0 b1 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) :
    (BitVec.ofNat 64 b1 &&& 63#64 ||| (BitVec.ofNat 64 b0 &&& 31#64) <<< 6).toNat = b0 % 32 * 64 + b1 % 64 := by
  rw [BitVec.toNat_or, bv_shl _ _ (by rw [bv_and31 _ h0]; omega), bv_and31 _ h0, bv_and63 _ h1]
  exact or_low' (b0 % 32) (b1 % 64) 6 (by omega)

theorem r3 (b0 b1 b2 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) :
    ((BitVec.ofNat 64 b0).rotateRight 52 &&& 61440#64 &&& 65535#64 ||| (BitVec.ofNat 64 b1 &&& 63#64) <<< 6 |||
      BitVec.ofNat 64 b2 &&& 63#64).toNat = b0 % 16 * 4096 + b1 % 64 * 64 + b2 % 64 := by
  rw [ubfiz12_4 b0 h0, BitVec.toNat_or, BitVec.toNat_or, bv_shl _ _ (by rw [bv_and63 _ h1]; omega),
    bv_and63 _ h1, bv_and63 _ h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show b0 % 16 * 4096 < 2 ^ 64 by omega)]
  rw [show b0 % 16 * 4096 = (b0 % 16 * 2 ^ 6) * 2 ^ 6 by omega, mul_or_mul, or_low _ _ 6 (by omega),
    or_low _ _ 6 (by omega)]
  omega

theorem r4 (b0 b1 b2 b3 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) :
    (BitVec.ofNat 64 b3 &&& 63#64 ||| ((BitVec.ofNat 64 b0).rotateRight 46 &&& 1835008#64 &&& 2097151#64 |||
      (BitVec.ofNat 64 b1 &&& 63#64) <<< 12 ||| (BitVec.ofNat 64 b2 &&& 63#64) <<< 6)).toNat =
      b0 % 8 * 262144 + b1 % 64 * 4096 + b2 % 64 * 64 + b3 % 64 := by
  rw [ubfiz18_3 b0 h0, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or,
    bv_shl _ _ (by rw [bv_and63 _ h1]; omega), bv_shl _ _ (by rw [bv_and63 _ h2]; omega),
    bv_and63 _ h1, bv_and63 _ h2, bv_and63 _ h3, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show b0 % 8 * 262144 < 2 ^ 64 by omega)]
  have e1 : b0 % 8 * 262144 ||| b1 % 64 * 2 ^ 12 = b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 := by
    have := or_mul_low (b0 % 8) (b1 % 64) 6 12 (by omega)
    simpa using this
  have e2 : b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 ||| b2 % 64 * 2 ^ 6 =
      b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 + b2 % 64 * 2 ^ 6 := by
    have := or_mul_low (b0 % 8 * 64 + b1 % 64) (b2 % 64) 6 6 (by omega)
    rw [show (b0 % 8 * 64 + b1 % 64) * 2 ^ (6 + 6) = b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 by omega] at this
    exact this
  have e3 : b3 % 64 ||| b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 + b2 % 64 * 2 ^ 6 =
      b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 + b2 % 64 * 2 ^ 6 + b3 % 64 := by
    have := or_low' (b0 % 8 * 4096 + b1 % 64 * 64 + b2 % 64) (b3 % 64) 6 (by omega)
    rw [show (b0 % 8 * 4096 + b1 % 64 * 64 + b2 % 64) * 2 ^ 6 = b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 + b2 % 64 * 2 ^ 6 by omega] at this
    exact this
  rw [e1, e2, e3]

set_option maxHeartbeats 20000000 in
theorem decoderune_meets (rt : List (Nat × Nat)) (stack : Nat) (H : RtReady) (hst : 24 ≤ stack) :
    RtContract Extracted.program decAddr rt stack H decoderuneSpec := by
  rintro s hpc ⟨⟨hra, hrb, hal, hsb, -, hsa, hacc⟩, ⟨⟨hpb, hrd⟩, hk⟩, hout, hg, -⟩
  obtain ⟨⟨hg1, hg2, hg3⟩, -⟩ := (hg : GuardOK s 0 ∧ _)
  simp only [decoderuneSpec, argWords, wordsFrom_succ, wordsFrom_zero, arg, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd, Nat.zero_add, List.mem_cons, List.not_mem_nil, or_false, forall_eq, calleeStack,
    outside_cons, outside_nil, and_true] at hpb hrd hk hout ⊢
  simp only [decoderuneSpec] at hacc hsa ⊢
  have h1i : (s.regs 1).toInt = ((s.regs 1).toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have h2i : (s.regs 2).toInt = ((s.regs 2).toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  by_cases hn0 : 0 < (s.regs 1).toNat
  · have hr := hrd hn0
    janus_run [h1i, h2i, and_sshr_sub]
    all_goals (apply RtPost.intro <;> (try rfl) <;> (try simp only [setReg_apply]; done))
    all_goals (try (simp only [calleeStack, List.append_nil, List.nil_append, decoderuneSpec, Bool.false_eq_true, ite_false]; janus_frame))
    all_goals (simp only [argWords, wordsFrom_succ, wordsFrom_zero, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceAdd, Nat.zero_add, setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    all_goals
      try simp only [h1i, h2i] at *
      try clear h1i h2i
      have hb0 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat) 1
      have hb1 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat + 1) 1
      have hb2 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat + 2) 1
      have hb3 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat + 3) 1
      simp only [Nat.pow_one] at hb0 hb1 hb2 hb3
      rw [decodeRune_eq_arith]; unfold decodeRuneA
      simp only [strBytes_length, isCont, byteAt_strBytes', ← Nat.add_assoc,
        Bool.and_eq_true, decide_eq_true_eq]
      try simp (disch := first | omega | decide |
          (simp (disch := omega) only [r2, r3, r4, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega))
        only [r2, r3, r4, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_add,
        BitVec.toNat_sub, sub_flags_nv32, toInt32_of_lt, Nat.reducePow, Nat.reduceMod] at *
      try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.or_eq_true, beq_iff_eq, Bool.not_eq_false, Bool.and_eq_false_iff, Bool.not_eq_false'] at *
      try clear hacc
      try clear hg2
      try clear hr
      try clear hrd
      try clear hout
      try clear hpc
      try clear hg
      try clear hra
      try clear hrb
      try clear hsa
      try simp (disch := omega) only [if_pos, if_neg]
      first | omega | (simp only [true_and, and_true]; omega)
  · janus_run [h1i, h2i, and_sshr_sub]
    all_goals (apply RtPost.intro <;> (try rfl) <;> (try simp only [setReg_apply]; done))
    all_goals (try (simp only [calleeStack, List.append_nil, List.nil_append, decoderuneSpec, Bool.false_eq_true, ite_false]; janus_frame))
    all_goals (simp only [argWords, wordsFrom_succ, wordsFrom_zero, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceAdd, Nat.zero_add, setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    all_goals
      try simp only [h1i, h2i] at *
      try clear h1i h2i
      have hb0 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat) 1
      have hb1 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat + 1) 1
      have hb2 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat + 2) 1
      have hb3 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat + 3) 1
      simp only [Nat.pow_one] at hb0 hb1 hb2 hb3
      rw [decodeRune_eq_arith]; unfold decodeRuneA
      simp only [strBytes_length, isCont, byteAt_strBytes', ← Nat.add_assoc,
        Bool.and_eq_true, decide_eq_true_eq]
      try simp (disch := first | omega | decide |
          (simp (disch := omega) only [r2, r3, r4, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega))
        only [r2, r3, r4, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_add,
        BitVec.toNat_sub, sub_flags_nv32, toInt32_of_lt, Nat.reducePow, Nat.reduceMod] at *
      try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.or_eq_true, beq_iff_eq, Bool.not_eq_false, Bool.and_eq_false_iff, Bool.not_eq_false'] at *
      try clear hacc
      try clear hg2
      try clear hr
      try clear hrd
      try clear hout
      try clear hpc
      try clear hg
      try clear hra
      try clear hrb
      try clear hsa
      try simp (disch := omega) only [if_pos, if_neg]
      first | omega | (simp only [true_and, and_true]; omega)
/-- The witness call state: `Janus.Contracts.Sat`'s, at `runtime.decoderune`, with the empty
string and `k = 0`. -/
def ds0 : State := { Janus.Contracts.Sat.wstate (Janus.Contracts.Sat.args []) with
  pc := BitVec.ofNat 64 decAddr }

/-- **The contract is satisfiable, by the runtime's own code**: `correctness` is the
implementation, and `ds0` meets the precondition. -/
theorem decoderune_satisfiable : ∃ (rt : List (Nat × Nat)) (H : RtReady),
    RtContract Extracted.program decAddr rt 24 H decoderuneSpec ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 decAddr ∧ RtPre rt 24 H decoderuneSpec s := by
  have ha : ∀ j, arg (argWords ds0 3) j = 0 := fun j => Janus.Contracts.Sat.args_zero 3 j (by decide)
  refine ⟨[], fun _ _ _ _ => True, decoderune_meets [] 24 _ (Nat.le_refl _), ds0, rfl, ?_, ?_, ?_, ?_, by simp [decoderuneSpec]⟩
  · have hw : Janus.Contracts.Sat.wmem.accessible (Janus.Contracts.Sat.wsp - 0x2000) 0x2100 true = true := by decide
    simp only [CallOK, ds0, Janus.Contracts.Sat.wstate, decoderuneSpec, Janus.Contracts.Sat.wret,
      Janus.Contracts.Sat.wsp, BitVec.toNat_ofNat, ite_true, ite_false, Nat.reduceEqDiff]
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
    exact Memory.accessible_mono _ hw (by simp [Janus.Contracts.Sat.wsp]) (by simp [Janus.Contracts.Sat.wsp])
  · show StrIn _ (arg (argWords ds0 3) 0) (arg (argWords ds0 3) 1) ∧ arg (argWords ds0 3) 2 < 2 ^ 63
    rw [ha 0, ha 1, ha 2]
    exact ⟨⟨by decide, by simp⟩, by decide⟩
  · show ∀ r ∈ [(arg (argWords ds0 3) 0, arg (argWords ds0 3) 1)], Outside r.1 r.2 _
    rw [ha 0, ha 1]
    simp [Janus.Contracts.Sat.outside_zero]
  · show GuardOK ds0 0 ∧ Outside _ 8 _
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    simp only [calleeStack, ds0, Janus.Contracts.Sat.wstate, outside_cons, outside_nil]
    decide

/-! ## SumRunes -/


abbrev head : Nat := Extracted.entry + 0x38

/-- The memory after the prologue's stores. -/
def M0 (s : State) (ret : Nat) (p n : BitVec 64) : Memory :=
  (((s.mem.writeLE (s.sp.toNat - 48) 8 ret).writeLE (s.sp.toNat - 56) 8 (s.regs 29).toNat).writeLE
    (s.sp.toNat + 16) 8 n.toNat).writeLE (s.sp.toNat + 8) 8 p.toNat

/-- What the loop may change besides `rt`: `decoderune`'s stack window and spill slots, and the
saved accumulator. -/
def R (s : State) : List (Nat × Nat) := [(s.sp.toNat - 4144, s.sp.toNat - 56), (s.sp.toNat - 40, s.sp.toNat - 8)]

/-- `SXTW` of a word whose low half is a non-negative `int32`. -/
theorem sxtw_small (x : BitVec 64) (h : x.toNat % 2 ^ 32 < 2 ^ 31) :
    ((if x.getLsbD 31 = true then 18446744073709551615#64 else 0#64) &&& 18446744069414584320#64 |||
      x.rotateRight 0 &&& 4294967295#64 &&& 4294967295#64) = BitVec.ofNat 64 (x.toNat % 2 ^ 32) := by
  have h31 : x.getLsbD 31 = false := by
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
    simp only [decide_eq_false_iff_not]
    have : x.toNat / 2 ^ 31 % 2 = x.toNat % 2 ^ 32 / 2 ^ 31 := by omega
    omega
  rw [h31]
  apply BitVec.eq_of_toNat_eq
  simp only [Bool.false_eq_true, ite_false, BitVec.zero_and, BitVec.zero_or, BitVec.toNat_and,
    BitVec.toNat_ofNat]
  have hr : x.rotateRight 0 = x := by simp [BitVec.rotateRight, BitVec.rotateRightAux]
  have e : x.toNat &&& 4294967295 = x.toNat % 4294967296 := Nat.and_two_pow_sub_one_eq_mod x.toNat 32
  rw [hr]
  simp only [show (4294967295 : Nat) % 2 ^ 64 = 4294967295 from rfl, e]
  have e2 : x.toNat % 4294967296 &&& 4294967295 = x.toNat % 4294967296 % 4294967296 :=
    Nat.and_two_pow_sub_one_eq_mod _ 32
  rw [e2]
  omega

theorem toInt_setWidth32_readLE1 (m : Memory) (a : Nat) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE a 1))).toInt = (m.readLE a 1 : Int) := by
  have hb := Memory.readLE_lt m a 1
  simp only [Nat.pow_one] at hb
  rw [toInt32_of_lt _ (by simp; omega)]
  simp; omega

theorem toInt_127 : (127#32).toInt = 127 := by decide

theorem toNat_setWidth32_readLE1 (m : Memory) (a : Nat) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE a 1))).toNat = m.readLE a 1 := by
  have hb := Memory.readLE_lt m a 1
  simp only [Nat.pow_one] at hb
  simp; omega

/-- One iteration of the range loop: the rune it adds and the index it moves to. -/
theorem step_sum (bs : List Nat) (k a r k' : Nat) (hk : k < bs.length) (hs : rangeStep bs k = (r, k')) :
    ((a + r) % 2 ^ 64 + (runesFrom bs k').sum) % 2 ^ 64 = (a + (runesFrom bs k).sum) % 2 ^ 64 := by
  rw [runesFrom_of_lt bs k hk, hs]
  simp only [List.sum_cons]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem loop (rt : List (Nat × Nat)) (H : RtReady) (p n : BitVec 64)
    (hdec : RtContract Extracted.program decAddr
      rt 4096 H decoderuneSpec) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 48 < s.sp.toNat)
    (hal : s.sp.toNat % 16 = 0) (hb : 4144 ≤ s.sp.toNat) (ha : s.sp.toNat + 24 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 4144) (4144 + 24) true = true)
    (hout : Outside (s.sp.toNat - 4144) 4168 rt) (hgr : Outside ((s.regs 28).toNat + 16) 8 rt)
    (hgs : (s.regs 28).toNat + 24 ≤ s.sp.toNat - 4144 ∨ s.sp.toNat + 24 ≤ (s.regs 28).toNat + 16)
    (hp1 : p.toNat + n.toNat ≤ 2 ^ 48) (hp2 : 0 < n.toNat → s.mem.accessible p.toNat n.toNat false = true)
    (hpr : Outside p.toNat n.toNat rt)
    (hps : p.toNat + n.toNat ≤ s.sp.toNat - 4144 ∨ s.sp.toNat + 24 ≤ p.toNat)
    (hn : n.toNat < 2 ^ 63) (hra : ret % 4 = 0 ∧ ret < 2 ^ 48) :
    ∀ fuel (S : State) (T : Nat),
      ((S.regs 3).toNat + (runesFrom (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat).sum) % 2 ^ 64 = T →
      n.toNat - (S.regs 2).toNat ≤ fuel → (S.regs 2).toNat ≤ n.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = p → S.regs 1 = n →
      S.sp = s.sp - 48#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 56#64 → S.regs 18 = s.regs 18 →
      MemFrame (M0 s ret p n) S.mem (rt ++ R s) →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat = T) := by
  intro fuel
  induction fuel with
  | zero =>
    intro S T hT hf hk hpc h0 h1 hsp h28 h29 h18 hfr
    simp only [M0, R] at hfr
    janus_run
    rw [← hT, runesFrom_of_le _ _ (by simp; omega)]
    simp [Nat.mod_eq_of_lt (S.regs 3).isLt]
  | succ fuel ih =>
    intro S T hT hf hk hpc h0 h1 hsp h28 h29 h18 hfr
    have hfr0 := hfr
    have hbs : strBytes S.mem p.toNat n.toNat = strBytes s.mem p.toNat n.toNat := by
      rw [strBytes_of_frame hfr (by
        simp only [R, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpr, by omega, by omega⟩)]
      simp only [M0]
      rw [strBytes_writeLE _ _ _ _ _ _ (by omega), strBytes_writeLE _ _ _ _ _ _ (by omega),
        strBytes_writeLE _ _ _ _ _ _ (by omega), strBytes_writeLE _ _ _ _ _ _ (by omega)]
    simp only [M0, R] at hfr
    by_cases hkn : (S.regs 2).toNat = n.toNat
    · janus_run
      rw [← hT, runesFrom_of_le _ _ (by simp; omega)]
      simp [Nat.mod_eq_of_lt (S.regs 3).isLt]
    · have hr := hp2 (by omega)
      by_cases hasc : s.mem.readLE (p.toNat + (S.regs 2).toNat) 1 < 128
      · all_goals
          janus_run [false_implies, implies_true, List.not_mem_nil, forall_const, sub_flags_nv32,
            toInt_setWidth32_readLE1, toInt_127, toNat_setWidth32_readLE1] until [head] calls [hdec]
        all_goals
          apply ih
          all_goals (try (janus_simp; done))
          all_goals (try (janus_simp; omega))
        all_goals
          have hb := Memory.readLE_lt s.mem (p.toNat + (S.regs 2).toNat) 1
          simp only [Nat.pow_one] at hb
          try simp (disch := first | omega | decide |
              (simp (disch := omega) only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega))
            only [sub_flags_nv32, toInt32_of_lt, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
              Nat.reduceMod] at hbr
          try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
            beq_iff_eq, Bool.and_eq_false_iff, Bool.not_eq_false'] at hbr
        all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
        all_goals (try simp only [callRegs_apply, Nat.reduceEqDiff, ↓reduceIte, getD_cons_zero,
          getD_cons_lit, Nat.reduceSub, Nat.reduceAdd, or_self, or_false, false_or])
        all_goals
          have hkl : (S.regs 2).toNat < (strBytes s.mem p.toNat n.toNat).length := by simp; omega
          have hd1 := decodeRune_snd (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat
          have hd2 := decodeRune_snd_le_length _ _ hkl
          simp only [strBytes_length] at hd2
          have hd3 := decodeRune_fst_le (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat
          have hby := byteAt_strBytes s.mem p.toNat n.toNat (S.regs 2).toNat (by simp at hkl; omega)
          simp only [maxRune] at hd3
          have hfw : MemFrame (M0 s ret p n) (S.mem.writeLE (s.sp.toNat - 16) 8 (S.regs 3).toNat) (rt ++ R s) :=
            hfr0.writeLE _ (r := (s.sp.toNat - 40, s.sp.toNat - 8)) (by simp [R]) (by omega) (by omega)
          try rw [hbs] at *
        all_goals first
          | (simpa [M0, R] using hfr0)
          | (refine MemFrame.trans hfw hfl ?_
             intro a k' h
             simp only [R, outside_append, outside_cons, outside_nil, and_true] at h ⊢
             obtain ⟨hrt, h2, h3⟩ := h
             exact ⟨⟨hrt, h2, h3⟩, by omega, by omega⟩)
          | (obtain ⟨-, hr1⟩ := hpost; omega)
          | (obtain ⟨hr0, hr1⟩ := hpost
             have hrs : rangeStep (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat =
                 decodeRune (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat := by
               unfold rangeStep; rw [if_neg (by omega)]
             rw [sxtw_small _ (by omega), ← hT, BitVec.toNat_add, BitVec.toNat_ofNat, hr1,
               Nat.mod_eq_of_lt (by omega : (BitVec.toNat _ % 2 ^ 32) < 2 ^ 64)]
             rw [show BitVec.toNat _ % 2 ^ 32 = (decodeRune (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat).1 from hr0]
             exact step_sum _ _ _ _ _ hkl (by rw [hrs]))
          | (have hrs : rangeStep (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat =
                 (s.mem.readLE (p.toNat + (S.regs 2).toNat) 1, (S.regs 2).toNat + 1) := by
               unfold rangeStep; rw [hby, if_pos (by omega)]
             rw [sxtw_small _ (by simp; omega), ← hT, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
               BitVec.toNat_add]
             simp only [BitVec.toNat_ofNat]
             rw [Nat.mod_eq_of_lt (by omega : (S.regs 2).toNat + 1 % 2 ^ 64 < 2 ^ 64)]
             have := step_sum _ _ (S.regs 3).toNat _ _ hkl hrs
             rw [show (s.mem.readLE (p.toNat + (S.regs 2).toNat) 1 % 2 ^ 64 % 2 ^ 32) % 2 ^ 64 =
               s.mem.readLE (p.toNat + (S.regs 2).toNat) 1 by omega]
             simpa using this)

      · all_goals
          janus_run [false_implies, implies_true, List.not_mem_nil, forall_const, sub_flags_nv32,
            toInt_setWidth32_readLE1, toInt_127, toNat_setWidth32_readLE1] until [head] calls [hdec]
        all_goals
          apply ih
          all_goals (try (janus_simp; done))
          all_goals (try (janus_simp; omega))
        all_goals
          rename_i hfl hpost
          have hb := Memory.readLE_lt s.mem (p.toNat + (S.regs 2).toNat) 1
          simp only [Nat.pow_one] at hb
          try simp (disch := first | omega | decide |
              (simp (disch := omega) only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega))
            only [sub_flags_nv32, toInt32_of_lt, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
              Nat.reduceMod] at hbr
          try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
            beq_iff_eq, Bool.and_eq_false_iff, Bool.not_eq_false'] at hbr
        all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
        all_goals (try simp only [callRegs_apply, Nat.reduceEqDiff, ↓reduceIte, getD_cons_zero,
          getD_cons_lit, Nat.reduceSub, Nat.reduceAdd, or_self, or_false, false_or])
        all_goals
          have hkl : (S.regs 2).toNat < (strBytes s.mem p.toNat n.toNat).length := by simp; omega
          have hd1 := decodeRune_snd (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat
          have hd2 := decodeRune_snd_le_length _ _ hkl
          simp only [strBytes_length] at hd2
          have hd3 := decodeRune_fst_le (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat
          have hby := byteAt_strBytes s.mem p.toNat n.toNat (S.regs 2).toNat (by simp at hkl; omega)
          simp only [maxRune] at hd3
          have hfw : MemFrame (M0 s ret p n) (S.mem.writeLE (s.sp.toNat - 16) 8 (S.regs 3).toNat) (rt ++ R s) :=
            hfr0.writeLE _ (r := (s.sp.toNat - 40, s.sp.toNat - 8)) (by simp [R]) (by omega) (by omega)
          try rw [hbs] at *
        all_goals first
          | (simpa [M0, R] using hfr0)
          | (refine MemFrame.trans hfw hfl ?_
             intro a k' h
             simp only [R, outside_append, outside_cons, outside_nil, and_true] at h ⊢
             obtain ⟨hrt, h2, h3⟩ := h
             exact ⟨⟨hrt, h2, h3⟩, by omega, by omega⟩)
          | (obtain ⟨-, hr1⟩ := hpost; omega)
          | (obtain ⟨hr0, hr1⟩ := hpost
             have hrs : rangeStep (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat =
                 decodeRune (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat := by
               unfold rangeStep; rw [if_neg (by omega)]
             rw [sxtw_small _ (by omega), ← hT, BitVec.toNat_add, BitVec.toNat_ofNat, hr1,
               Nat.mod_eq_of_lt (by omega : (BitVec.toNat _ % 2 ^ 32) < 2 ^ 64)]
             rw [show BitVec.toNat _ % 2 ^ 32 = (decodeRune (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat).1 from hr0]
             exact step_sum _ _ _ _ _ hkl (by rw [hrs]))
          | (have hrs : rangeStep (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat =
                 (s.mem.readLE (p.toNat + (S.regs 2).toNat) 1, (S.regs 2).toNat + 1) := by
               unfold rangeStep; rw [hby, if_pos (by omega)]
             rw [sxtw_small _ (by simp; omega), ← hT, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
               BitVec.toNat_add]
             simp only [BitVec.toNat_ofNat]
             rw [Nat.mod_eq_of_lt (by omega : (S.regs 2).toNat + 1 % 2 ^ 64 < 2 ^ 64)]
             have := step_sum _ _ (S.regs 3).toNat _ _ hkl hrs
             rw [show (s.mem.readLE (p.toNat + (S.regs 2).toNat) 1 % 2 ^ 64 % 2 ^ 32) % 2 ^ 64 =
               s.mem.readLE (p.toNat + (S.regs 2).toNat) 1 by omega]
             simpa using this)


/-- The precondition. -/
def Pre (rt : List (Nat × Nat)) (p n : BitVec 64) (s : State) : Prop :=
  GuardOK s 48 ∧ StackOK s 4144 24 ∧ Outside (s.sp.toNat - 4144) 4168 rt ∧
    Outside ((s.regs 28).toNat + 16) 8 rt ∧
    ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 4144 ∨ s.sp.toNat + 24 ≤ (s.regs 28).toNat + 16) ∧
    StrIn s.mem p.toNat n.toNat ∧ Outside p.toNat n.toNat rt ∧
    (p.toNat + n.toNat ≤ s.sp.toNat - 4144 ∨ s.sp.toNat + 24 ≤ p.toNat)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem correctness (rt : List (Nat × Nat)) (H : RtReady) (p n : BitVec 64)
    (hdec : RtContract Extracted.program decAddr
      rt 4096 H decoderuneSpec) :
    Ensures Extracted.program Extracted.entry [p, n] (Pre rt p n)
      (fun s s' => (s'.regs 0).toNat = sumRunes (strBytes s.mem p.toNat n.toNat)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hout, hgr, hgs, ⟨hp1, hp2⟩, hpr, hps⟩
  janus_intro hs
  have hra : ret % 4 = 0 ∧ ret < 2 ^ 48 := ⟨hret.aligned, by have := hret.user; omega⟩
  janus_run until [head]
  refine loop rt H p n hdec ret hret s hg1 hg2 (by omega) hal hb ha hw hout hgr hgs hp1 hp2 hpr hps
    (by omega) hra n.toNat _ _ (by simp [setReg, sumRunes, runes]) (by simp [setReg]) (by simp [setReg]) (by janus_simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) ?_
  simp only [M0, R]
  exact MemFrame.refl _ _

/-- **SumRunes, with the runtime's own `decoderune`**: nothing assumed. -/
theorem runtime_correctness (p n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, n] (Pre [] p n)
      (fun s s' => (s'.regs 0).toNat = sumRunes (strBytes s.mem p.toNat n.toNat)) :=
  correctness [] (fun _ _ _ _ => True) p n (decoderune_meets [] 4096 _ (by decide))

/-! ## Non-vacuity -/

namespace Witness

open Janus.Contracts.Sat

def ret : Nat := wret
set_option maxRecDepth 100000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [0, 0] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases i with _ | _ | i <;> simp [s0] at h ⊢ <;> omega⟩

theorem pre : Pre [] 0 0 s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, ?_⟩,
    by simp [outside_nil], by simp [outside_nil], by decide, ⟨by decide, by simp⟩, by simp [outside_nil], by decide⟩
  have hw : wmem.accessible (wsp - 0x2000) 0x2100 true = true := by decide
  exact Memory.accessible_mono _ hw (by decide) (by decide)

/-- All hypotheses of `runtime_correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0, 0] s ∧ Pre [] 0 0 s :=
  ⟨ret, s0, hret, setup, pre⟩

/-- The witness call returns, with the conclusion of `runtime_correctness`. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = sumRunes (strBytes s0.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat) :=
  runtime_correctness 0 0 ret hret s0 setup pre

end Witness

end Proof
