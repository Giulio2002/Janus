import Janus
import Extracted

/-!
# `RuneLen(s string) int` on amd64: `len([]rune(s))`

**Guarantee.** As for arm64 (`examples/proofs/RuneLen.lean`): for every string `s = (p, n)` in
`RAX, RBX` and every Go call state with the stack guard 96 bytes below `RSP`, the stack window
`[RSP-4176, RSP+24)` writable, the string readable and outside the window and `g`'s guard word
outside it, the call returns, obeys the ABI, and `RAX` is `countRunes (bytes of s)`.

In three layers, all from the binary's code: `decoderune_meets` (as in
`examples/proofs-amd64/SumRunes`), `countrunes_meets` (the loop of `runtime.countrunes` through
`decoderune`'s contract) and `correctness_of_contract` (RuneLen through `countrunes`' contract);
`correctness` combines them, so nothing is assumed. `countrunes_satisfiable` is the
contract's witness and `Witness` gives a concrete call state.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
namespace Proof

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

theorem bv_sub_eq_zero8 (x y : BitVec 8) : (x - y = 0#8) ↔ x.toNat = y.toNat := by
  constructor
  · intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this; omega
  · intro h; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem bv_sub_eq_zero32 (x y : BitVec 32) : (x - y = 0#32) ↔ x.toNat = y.toNat := by
  constructor
  · intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this; omega
  · intro h; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem or_of_low (x y n : Nat) (hx : x % 2 ^ n = 0) (hy : y < 2 ^ n) : x ||| y = x + y := by
  have : x = x / 2 ^ n * 2 ^ n := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hx)).symm
  rw [this, or_low _ _ _ hy]

theorem or6 (x y : Nat) (hx : x % 64 = 0) (hy : y < 64) : x ||| y = x + y := or_of_low x y 6 hx hy
theorem or6' (x y : Nat) (hx : x % 64 = 0) (hy : y < 64) : y ||| x = x + y := by
  rw [Nat.or_comm]; exact or6 x y hx hy
theorem or12 (x y : Nat) (hx : x % 4096 = 0) (hy : y < 4096) : x ||| y = x + y := or_of_low x y 12 hx hy
theorem or12' (x y : Nat) (hx : x % 4096 = 0) (hy : y < 4096) : y ||| x = x + y := by
  rw [Nat.or_comm]; exact or12 x y hx hy
theorem or18 (x y : Nat) (hx : x % 262144 = 0) (hy : y < 262144) : x ||| y = x + y := or_of_low x y 18 hx hy
theorem or18' (x y : Nat) (hx : x % 262144 = 0) (hy : y < 262144) : y ||| x = x + y := by
  rw [Nat.or_comm]; exact or18 x y hx hy

theorem land63 (b : Nat) : b &&& 63 = b % 64 := Nat.and_two_pow_sub_one_eq_mod b 6
theorem land31 (b : Nat) : b &&& 31 = b % 32 := Nat.and_two_pow_sub_one_eq_mod b 5
theorem land15 (b : Nat) : b &&& 15 = b % 16 := Nat.and_two_pow_sub_one_eq_mod b 4
theorem land7 (b : Nat) : b &&& 7 = b % 8 := Nat.and_two_pow_sub_one_eq_mod b 3

/-! ### 32-bit signed comparisons (`CMPL` then `JLE`/`JG`), local to this proof -/

theorem sub_lt_signed32 (x y : BitVec 32) :
    ((x - y).msb != decide ((x - y).toInt ≠ x.toInt - y.toInt)) = decide (x.toInt < y.toInt) := by
  rw [BitVec.msb_eq_toInt, BitVec.toInt_sub, Int.bmod_def]
  have h1 := @BitVec.toInt_lt 32 x; have h2 := @BitVec.le_toInt 32 x
  have h3 := @BitVec.toInt_lt 32 y; have h4 := @BitVec.le_toInt 32 y
  simp only [Nat.reduceSub, Nat.reducePow, Int.reducePow, Int.reduceNeg] at *
  generalize x.toInt = a at *
  generalize y.toInt = b at *
  have hc : ((4294967296 : Nat) : Int) = 4294967296 := rfl
  simp only [hc] at *
  generalize hr : (a - b) % 4294967296 = r at *
  have hr0 : 0 ≤ r := by rw [← hr]; omega
  have hr1 : r < 4294967296 := by rw [← hr]; omega
  have hq : ∃ q, a - b = r + 4294967296 * q := ⟨(a - b) / 4294967296, by rw [← hr]; omega⟩
  obtain ⟨q, hq⟩ := hq
  split <;> rename_i hc <;>
  (by_cases p1 : r < 0 <;> by_cases p1' : r - 4294967296 < 0 <;>
   by_cases p2 : r = a - b <;> by_cases p2' : r - 4294967296 = a - b <;>
   by_cases p3 : a < b <;> simp [p1, p1', p2, p2', p3] <;> omega)

theorem sub_eq_zero_iff32 (x y : BitVec 32) : (x - y = 0) ↔ x.toInt = y.toInt := by
  rw [BitVec.toInt_inj, ← BitVec.toNat_inj, ← BitVec.toNat_inj, BitVec.toNat_sub]
  have := x.isLt; have := y.isLt
  rw [show (0 : BitVec 32).toNat = 0 from rfl]
  omega

theorem cond_sub_le32 (x y : BitVec 32) :
    condition 14 (subFlags x y false).2 = some (decide (x.toInt ≤ y.toInt)) := by
  simp only [condition_14, subFlags_zf, subFlags_sf, subFlags_ovf, subFlags_false_fst,
    Bool.toNat_false, Int.natCast_zero, Int.sub_zero, sub_lt_signed32]
  congr 1
  by_cases h : x.toInt = y.toInt
  · rw [decide_eq_true ((sub_eq_zero_iff32 x y).mpr h)]; simp; omega
  · rw [decide_eq_false (fun h' => h ((sub_eq_zero_iff32 x y).mp h'))]
    by_cases h' : x.toInt < y.toInt
    · rw [decide_eq_true h']; simp; omega
    · rw [decide_eq_false h']; simp; omega

theorem cond_sub_g32 (x y : BitVec 32) :
    condition 15 (subFlags x y false).2 = some (decide (y.toInt < x.toInt)) := by
  simp only [condition_15, subFlags_zf, subFlags_sf, subFlags_ovf, subFlags_false_fst,
    Bool.toNat_false, Int.natCast_zero, Int.sub_zero, sub_lt_signed32, Option.map_some]
  congr 1
  by_cases h : x.toInt = y.toInt
  · rw [decide_eq_true ((sub_eq_zero_iff32 x y).mpr h)]; simp; omega
  · rw [decide_eq_false (fun h' => h ((sub_eq_zero_iff32 x y).mp h'))]
    by_cases h' : x.toInt < y.toInt
    · rw [decide_eq_true h']; simp; omega
    · rw [decide_eq_false h']; simp; omega

attribute [local janus64_exec high, local janus64_post high] cond_sub_le32 cond_sub_g32

theorem sw32_64 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; omega

theorem toInt32_ofNat_small (v : Nat) (h : v < 2147483648) : (BitVec.ofNat 32 v).toInt = (v : Int) := by
  rw [Janus.Tactic.toInt32_of_lt _ (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The rune of a two-byte sequence, as `decoderune` assembles it (`ANDL`/`SHLL`/`ORL`). -/
theorem r2a (b0 b1 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) :
    ((BitVec.ofNat 8 b1).setWidth 32 &&& 63#32 ||| ((BitVec.ofNat 8 b0).setWidth 32 &&& 31#32) <<< 6) =
      BitVec.ofNat 32 (b0 % 32 * 64 + b1 % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, land63, land31, Nat.reducePow, Nat.reduceMod]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  simp (disch := omega) only [or6, or6', or12, or12', or18, or18']
  try simp (disch := omega) only [Nat.mod_eq_of_lt]

theorem r3a (b0 b1 b2 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) :
    ((BitVec.ofNat 8 b2).setWidth 32 &&& 63#32 |||
      (((BitVec.ofNat 8 b1).setWidth 32 &&& 63#32) <<< 6 ||| ((BitVec.ofNat 8 b0).setWidth 32 &&& 15#32) <<< 12)) =
      BitVec.ofNat 32 (b0 % 16 * 4096 + b1 % 64 * 64 + b2 % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, land63, land15, Nat.reducePow, Nat.reduceMod]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  try simp (disch := omega) only [or6, or6', or12, or12', or18, or18']
  try simp (disch := omega) only [or6, or6', or12, or12', or18, or18']
  try simp (disch := omega) only [Nat.mod_eq_of_lt]
  try omega

theorem r4a (b0 b1 b2 b3 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) :
    ((BitVec.ofNat 8 b3).setWidth 32 &&& 63#32 |||
      (((BitVec.ofNat 8 b0).setWidth 32 &&& 7#32) <<< 18 ||| ((BitVec.ofNat 8 b1).setWidth 32 &&& 63#32) <<< 12 |||
        ((BitVec.ofNat 8 b2).setWidth 32 &&& 63#32) <<< 6)) =
      BitVec.ofNat 32 (b0 % 8 * 262144 + b1 % 64 * 4096 + b2 % 64 * 64 + b3 % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, land63, land7, Nat.reducePow, Nat.reduceMod]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  try simp (disch := omega) only [or6, or6', or12, or12', or18, or18']
  try simp (disch := omega) only [or6, or6', or12, or12', or18, or18']
  try simp (disch := omega) only [or6, or6', or12, or12', or18, or18']
  try simp (disch := omega) only [Nat.mod_eq_of_lt]
  try omega

/-- amd64's form of the mask (`SUB; NEG; SAR $63; AND`): `k` when `k < n`. -/
theorem mask_k (a b : BitVec 64) (h : a.toNat < b.toNat) (hb : b.toNat < 2 ^ 63) :
    ((0#64 - (b - a)).sshiftRight 63).toNat &&& a.toNat = a.toNat := by
  have e : 0#64 - (b - a) = a - b := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [e, Nat.and_comm]; exact and_sshr_sub a b h hb


set_option linter.unusedSimpArgs false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem decoderune_meets (rt : List (Nat × Nat)) (stack : Nat) (H : RtReady) (hst : 8 ≤ stack) :
    RtContract64 Extracted.program decAddr rt stack H decoderuneSpec := by
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, ⟨⟨hpb, hrd⟩, hk⟩, hout, hg, -⟩
  simp only [decoderuneSpec, argWords64, wordsFrom_succ, wordsFrom_zero, arg, List.getD_cons_zero,
    List.getD_cons_succ, Nat.reduceAdd, Nat.zero_add, List.mem_cons, List.not_mem_nil, or_false, forall_eq, readsOutside_cons, readsOutside_nil,
    calleeStack64, outside_cons, outside_nil, and_true, Nat.reduceLT, ↓reduceIte, argReg, intArgRegs,
    List.getD_cons_zero, List.getD_cons_succ] at hpb hrd hk hout ⊢
  simp only [decoderuneSpec] at hacc hsa hg ⊢
  obtain ⟨⟨hg1, hg2, hg3⟩, -⟩ := hg
  have h3i : (s.regs 3).toInt = ((s.regs 3).toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have h1i : (s.regs 1).toInt = ((s.regs 1).toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hdi : (s.regs 1).toNat < (s.regs 3).toNat →
      (s.regs 3 - s.regs 1).toInt = (((s.regs 3).toNat - (s.regs 1).toNat : Nat) : Int) := fun h => by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [BitVec.toNat_sub]; omega), BitVec.toNat_sub]; congr 1; omega
  by_cases hn0 : 0 < (s.regs 3).toNat
  · have hr := hrd hn0
    janus64_run [h1i, h3i, mask_k, hdi]
    all_goals (apply RtPost64.intro <;> (try rfl) <;> (try simp only [setRegF_apply, retAddrOf]; done))
    all_goals (try (simp only [calleeStack64, List.append_nil, List.nil_append, decoderuneSpec, Bool.false_eq_true, rtIf_false]; janus_frame))
    all_goals (simp only [argWords64, wordsFrom_succ, wordsFrom_zero, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceAdd, Nat.zero_add, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceLT, argReg, intArgRegs])
    all_goals
      have hb0 := Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 1).toNat) 1
      have hb1 := Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 1).toNat + 1) 1
      have hb2 := Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 1).toNat + 2) 1
      have hb3 := Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 1).toNat + 3) 1
      simp only [Nat.pow_one] at hb0 hb1 hb2 hb3
      rw [decodeRune_eq_arith]; unfold decodeRuneA
      simp only [strBytes_length, isCont, byteAt_strBytes', ← Nat.add_assoc,
        Bool.and_eq_true, decide_eq_true_eq]
      clear hpc hra hal hsb hsa hacc hrd hout hg1 hg2 hg3 h3i h1i hdi hr hst
      try simp only [sw32_64] at *
      try simp (disch := omega) only [r2a, r3a, r4a] at *
      try simp only [bv_sub_eq_zero8, bv_sub_eq_zero32, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, Nat.reduceMod] at *
      try simp (disch := omega) only [toInt32_ofNat_small] at *
      try simp (disch := omega) only [Nat.mod_eq_of_lt] at *
      try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.or_eq_true, beq_iff_eq, Bool.not_eq_false, Bool.and_eq_false_iff, Bool.not_eq_false'] at *
      try simp (disch := omega) only [if_pos, if_neg]
      try simp only [Prod.mk.injEq, true_and, and_true]
      try omega
  · janus64_run [h1i, h3i, mask_k, hdi]
    all_goals (apply RtPost64.intro <;> (try rfl) <;> (try simp only [setRegF_apply, retAddrOf]; done))
    all_goals (try (simp only [calleeStack64, List.append_nil, List.nil_append, decoderuneSpec, Bool.false_eq_true, rtIf_false]; janus_frame))
    all_goals (simp only [argWords64, wordsFrom_succ, wordsFrom_zero, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceAdd, Nat.zero_add, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceLT, argReg, intArgRegs])
    all_goals
      have hb0 := Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 1).toNat) 1
      have hb1 := Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 1).toNat + 1) 1
      have hb2 := Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 1).toNat + 2) 1
      have hb3 := Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 1).toNat + 3) 1
      simp only [Nat.pow_one] at hb0 hb1 hb2 hb3
      rw [decodeRune_eq_arith]; unfold decodeRuneA
      simp only [strBytes_length, isCont, byteAt_strBytes', ← Nat.add_assoc,
        Bool.and_eq_true, decide_eq_true_eq]
      clear hpc hra hal hsb hsa hacc hrd hout hg1 hg2 hg3 h3i h1i hdi hst
      try simp only [sw32_64] at *
      try simp (disch := omega) only [r2a, r3a, r4a] at *
      try simp only [bv_sub_eq_zero8, bv_sub_eq_zero32, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, Nat.reduceMod] at *
      try simp (disch := omega) only [toInt32_ofNat_small] at *
      try simp (disch := omega) only [Nat.mod_eq_of_lt] at *
      try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.or_eq_true, beq_iff_eq, Bool.not_eq_false, Bool.and_eq_false_iff, Bool.not_eq_false'] at *
      try simp (disch := omega) only [if_pos, if_neg]
      try simp only [Prod.mk.injEq, true_and, and_true]
      try omega


/-- `MOVSXD` of a non-negative `int32`. -/
theorem sext_small (x : BitVec 32) (h : x.toNat < 2 ^ 31) : BitVec.signExtend 64 x = BitVec.ofNat 64 x.toNat := by
  have hm : x.msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  first | omega | skip

theorem toNat_sw_byte (m : Arm64.Memory) (a : Nat) :
    (BitVec.setWidth 32 (BitVec.ofNat 8 (m.readLE a 1))).toNat = m.readLE a 1 := by
  have hb := Arm64.Memory.readLE_lt m a 1
  simp only [Nat.pow_one] at hb
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem toInt_sw_byte (m : Arm64.Memory) (a : Nat) :
    (BitVec.setWidth 32 (BitVec.ofNat 8 (m.readLE a 1))).toInt = (m.readLE a 1 : Int) := by
  have hb := Arm64.Memory.readLE_lt m a 1
  simp only [Nat.pow_one] at hb
  rw [Janus.Tactic.toInt32_of_lt _ (by rw [toNat_sw_byte]; omega), toNat_sw_byte]

theorem toInt_127_32 : (127#32).toInt = 127 := by decide

/-! ## `runtime.countrunes`, from its code -/

/-- `runtime.countrunes`' address. -/
def crAddr : Nat := segAddr Extracted.program "runtime.countrunes"

abbrev head : Nat := crAddr + 0x24

/-- The memory after countrunes' prologue (`PUSHQ BP`, the spills of `BX` and `AX`). -/
def M0 (s : State) (p n : BitVec 64) : Arm64.Memory :=
  ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 16) 8 n.toNat).writeLE
    ((s.regs 4).toNat + 8) 8 p.toNat

/-- What the loop may change: `decoderune`'s stack window, its return-address and spill slots,
and the saved count. -/
def R (s : State) : List (Nat × Nat) := [((s.regs 4).toNat - 4144, (s.regs 4).toNat - 8)]

theorem rr_mono' {p : Amd64.Program} {ret : BitVec 64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', h1, h2, h3⟩ := h; exact ⟨k, s', h1, h2, hQ _ h3⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem loop (rt : List (Nat × Nat)) (H : RtReady) (p n : BitVec 64)
    (hdec : RtContract64 Extracted.program decAddr rt 4096 H decoderuneSpec) (s : State)
    (hg1 : (s.regs 14).toNat + 24 ≤ 2 ^ 48) (hg2 : s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 48 < (s.regs 4).toNat)
    (hal : (s.regs 4).toNat % 8 = 0) (hb : 4144 ≤ (s.regs 4).toNat) (ha : (s.regs 4).toNat + 24 ≤ 2 ^ 48)
    (hw : s.mem.accessible ((s.regs 4).toNat - 4144) (4144 + 24) true = true)
    (hgs1 : (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4144 ∨ (s.regs 4).toNat ≤ (s.regs 14).toNat + 16)
    (hgs2 : (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat + 8 ∨ (s.regs 4).toNat + 24 ≤ (s.regs 14).toNat + 16)
    (hp1 : p.toNat + n.toNat ≤ 2 ^ 48) (hp2 : 0 < n.toNat → s.mem.accessible p.toNat n.toNat false = true)
    (hps1 : p.toNat + n.toNat ≤ (s.regs 4).toNat - 4144 ∨ (s.regs 4).toNat ≤ p.toNat)
    (hps2 : p.toNat + n.toNat ≤ (s.regs 4).toNat + 8 ∨ (s.regs 4).toNat + 24 ≤ p.toNat)
    (hn : n.toNat < 2 ^ 63) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ∀ fuel (S : State) (T : Nat),
      (S.regs 2).toNat + (runesFrom (strBytes s.mem p.toNat n.toNat) (S.regs 1).toNat).length = T →
      n.toNat - (S.regs 1).toNat ≤ fuel → (S.regs 1).toNat ≤ n.toNat → (S.regs 2).toNat ≤ (S.regs 1).toNat →
      S.rip = BitVec.ofNat 64 head → S.regs 0 = p → S.regs 3 = n →
      S.regs 4 = s.regs 4 - 40#64 → S.regs 14 = s.regs 14 → S.regs 5 = s.regs 4 - 8#64 →
      S.xmm 15 = s.xmm 15 → S.df = s.df → S.fsBase = s.fsBase → S.mxcsr = s.mxcsr →
      S.x87 = s.x87 → S.fpucw = s.fpucw →
      MemFrame (M0 s p n) S.mem (R s) →
      ReachesRet Extracted.program (retAddrOf s) S fun s' =>
        s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8#64 ∧ s'.regs 5 = s.regs 5 ∧
        s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧ s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
        s'.mxcsr = s.mxcsr ∧ s'.x87 = s.x87 ∧ s'.fpucw = s.fpucw ∧
        MemFrame (M0 s p n) s'.mem (R s) ∧ (s'.regs 0).toNat = T := by
  intro fuel
  induction fuel with
  | zero =>
    intro S T hT hf hk hck hpc h0 h3 hsp h14 h5 hx hdf hfs hmx hx87 hfpu hfr
    have hfr0 := hfr
    simp only [M0, R] at hfr
    janus64_run
    refine ⟨hfs, hx87, hfpu, hfr0, ?_⟩
    rw [← hT, runesFrom_of_le _ _ (by simp; omega)]
    simp
  | succ fuel ih =>
    intro S T hT hf hk hck hpc h0 h3 hsp h14 h5 hx hdf hfs hmx hx87 hfpu hfr
    have hfr0 := hfr
    have hbs : strBytes S.mem p.toNat n.toNat = strBytes s.mem p.toNat n.toNat := by
      rw [strBytes_of_frame hfr (by
        simp only [R, outside_cons, outside_nil, and_true]
        omega)]
      simp only [M0]
      rw [strBytes_writeLE _ _ _ _ _ _ (by omega), strBytes_writeLE _ _ _ _ _ _ (by omega),
        strBytes_writeLE _ _ _ _ _ _ (by omega)]
    simp only [M0, R] at hfr
    by_cases hkn : (S.regs 1).toNat = n.toNat
    · janus64_run
      refine ⟨hfs, hx87, hfpu, hfr0, ?_⟩
      rw [← hT, runesFrom_of_le _ _ (by simp; omega)]
      simp
    · have hr := hp2 (by omega)
      have hkl : (S.regs 1).toNat < (strBytes s.mem p.toNat n.toNat).length := by simp; omega
      have hd1 := decodeRune_snd (strBytes s.mem p.toNat n.toNat) (S.regs 1).toNat
      have hd2 := decodeRune_snd_le_length _ _ hkl
      simp only [strBytes_length] at hd2
      have hby := byteAt_strBytes s.mem p.toNat n.toNat (S.regs 1).toNat (by simp at hkl; omega)
      by_cases hasc : s.mem.readLE (p.toNat + (S.regs 1).toNat) 1 < 128
      · janus64_run [false_implies, implies_true, List.not_mem_nil, forall_const, sw32_64, toInt_sw_byte,
          toInt_127_32] until [head] calls [hdec]
        apply ih
        all_goals (try (janus64_simp; done))
        all_goals (try (janus64_simp; omega))
        all_goals (try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
        all_goals first
          | exact hfr0
          | (have hrs : rangeStep (strBytes s.mem p.toNat n.toNat) (S.regs 1).toNat =
                (s.mem.readLE (p.toNat + (S.regs 1).toNat) 1, (S.regs 1).toNat + 1) := by
              unfold rangeStep; rw [hby, if_pos (by omega)]
             have hk1 : (S.regs 1 + 1#64).toNat = (S.regs 1).toNat + 1 := by
               simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
             rw [hk1, ← hT, runesFrom_of_lt _ _ hkl, hrs]
             simp only [List.length_cons, BitVec.toNat_add, BitVec.toNat_ofNat]
             omega)
          | (simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      · janus64_run [false_implies, implies_true, List.not_mem_nil, forall_const, sw32_64, toInt_sw_byte,
          toInt_127_32] until [head] calls [hdec]
        rename_i r0 r1 r2 jk fl xm yh M1 hfl hpost
        have hfw : MemFrame (M0 s p n) ((S.mem.writeLE ((s.regs 4).toNat - 16) 8 (S.regs 2).toNat).writeLE
            ((s.regs 4).toNat - 48) 8 (crAddr + 0x45)) (R s) :=
          (hfr0.writeLE _ (r := ((s.regs 4).toNat - 4144, (s.regs 4).toNat - 8)) (by simp [R]) (by omega) (by omega)).writeLE
            _ (r := ((s.regs 4).toNat - 4144, (s.regs 4).toNat - 8)) (by simp [R]) (by omega) (by omega)
        rw [hbs] at hpost
        obtain ⟨hr0, hr1⟩ := hpost
        apply ih
        all_goals (try (janus64_simp; done))
        all_goals (try (janus64_simp; omega))
        all_goals (try simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte,
          List.getD_cons_zero, List.getD_cons_succ, or_self, or_false, false_or])
        all_goals first
          | (refine MemFrame.trans hfw hfl ?_
             intro a k' h
             simp only [R, outside_append, outside_cons, outside_nil, List.nil_append, and_true] at h ⊢
             exact ⟨h, by omega, by omega⟩)
          | omega
          | (have hrs : rangeStep (strBytes s.mem p.toNat n.toNat) (S.regs 1).toNat =
                decodeRune (strBytes s.mem p.toNat n.toNat) (S.regs 1).toNat := by
              unfold rangeStep; rw [if_neg (by omega)]
             rw [← hT, runesFrom_of_lt _ _ hkl, hrs, hr1]
             simp only [List.length_cons, BitVec.toNat_add, BitVec.toNat_ofNat]
             omega)
          | (simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`runtime.countrunes` meets its contract**, given `decoderune`'s. -/
theorem countrunes_meets (rt : List (Nat × Nat)) (H : RtReady) (stack : Nat) (hst : 4144 ≤ stack) :
    RtContract64 Extracted.program crAddr rt stack H countrunesSpec := by
  have hdec := decoderune_meets rt 4096 H (by decide)
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, ⟨hp1, hp2⟩, hreads, hg, -⟩
  simp only [countrunesSpec, argWords64, wordsFrom_succ, wordsFrom_zero, arg, List.getD_cons_zero,
    List.getD_cons_succ, Nat.reduceAdd, Nat.zero_add, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, readsOutside_cons, readsOutside_nil, calleeStack64, outside_cons, outside_nil, and_true, Nat.reduceLT, ↓reduceIte, argReg,
    intArgRegs] at hp1 hp2 hreads hg hacc hsa ⊢
  obtain ⟨⟨hg1, hg2, hg3⟩, hgs1, hgs2⟩ := hg
  obtain ⟨hpo1, hpo2⟩ := hreads
  have hw : s.mem.accessible ((s.regs 4).toNat - 4144) (4144 + 24) true = true :=
    Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  janus64_run until [head]
  refine rr_mono' (loop rt H (s.regs 0) (s.regs 3) hdec s hg1 hg2 (by omega) hal (by omega) (by omega) hw
    (by omega) (by omega) hp1 hp2 (by omega) (by omega) (by omega) hra (s.regs 3).toNat _ _ rfl
    (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by janus64_simp)
    (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
    (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) rfl rfl ?_) ?_
  · simp only [M0, R]; exact MemFrame.refl _ _
  · rintro s' ⟨hrip, h4, h5, h14, hx, hfs, hdf, hmx, hx87, hfpu, hfr, h0⟩
    refine RtPost64.intro hrip h4 h5 h14 hx hfs hdf hmx ?_ ?_ hx87 hfpu
    · have h1 : MemFrame s.mem (M0 s (s.regs 0) (s.regs 3)) [((s.regs 4).toNat - stack, (s.regs 4).toNat),
          ((s.regs 4).toNat + 8, (s.regs 4).toNat + 8 + 8 * 2)] := by
        simp only [M0]
        exact ((MemFrame.of_writeLE _ _ (r := ((s.regs 4).toNat - stack, (s.regs 4).toNat)) (by simp) (by omega) (by omega)).writeLE
          _ (r := ((s.regs 4).toNat + 8, (s.regs 4).toNat + 8 + 8 * 2)) (by simp) (by omega) (by omega)).writeLE
          _ (r := ((s.regs 4).toNat + 8, (s.regs 4).toNat + 8 + 8 * 2)) (by simp) (by omega) (by omega)
      refine MemFrame.trans h1 hfr ?_
      intro a k h
      simp only [countrunesSpec, rtIf_false, calleeStack64, R, List.nil_append, List.append_nil,
        outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨⟨h.1, h.2⟩, by omega⟩
    · simp only [countrunesSpec, argWords64, wordsFrom_succ, wordsFrom_zero, arg, List.getD_cons_zero,
        List.getD_cons_succ, Nat.reduceAdd, Nat.zero_add, countRunes, runes, Nat.reduceLT, ↓reduceIte,
        argReg, intArgRegs]
      rw [h0]
      simp [setRegF_apply]

/-- `countrunes(s)` returns the number of runes `for range s` produces: the contract is satisfiable,
by the runtime's own code (`countrunes_meets`) at a concrete call state. -/
theorem countrunes_satisfiable : ∃ (rt : List (Nat × Nat)) (H : RtReady),
    RtContract64 Extracted.program crAddr rt 4144 H countrunesSpec :=
  ⟨[], fun _ _ _ _ => True, countrunes_meets [] _ 4144 (Nat.le_refl _)⟩

/-! ## RuneLen -/

def Pre (p n : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 96 ∧ StackWritable s 4176 24 ∧ (s.regs 4).toNat % 8 = 0 ∧
    ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4176 ∨ (s.regs 4).toNat + 24 ≤ (s.regs 14).toNat + 16) ∧
    StrIn s.mem p.toNat n.toNat ∧
    (p.toNat + n.toNat ≤ (s.regs 4).toNat - 4176 ∨ (s.regs 4).toNat + 24 ≤ p.toNat)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **RuneLen, from `countrunes`' contract.** -/
theorem correctness_of_contract (rt : List (Nat × Nat)) (H : RtReady) (p n : BitVec 64)
    (hc : RtContract64 Extracted.program crAddr rt 4144 H countrunesSpec) :
    Ensures Extracted.program Extracted.entry [p, n] (Pre p n)
      (fun s s' => (s'.regs 0).toNat = countRunes (strBytes s.mem p.toNat n.toNat)) := by
  intro ret hret s hs ⟨hsg, ⟨hb, ha, hw⟩, hal, hgs, ⟨hp1, hp2⟩, hps⟩
  janus64_intro hs
  have hgl := hsg.load
  have hgb := hsg.below
  have hnw2 := hsg.noWrap
  have hgr := hsg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hal hgs hps ⊢
  janus64_run [false_implies, implies_true, List.not_mem_nil, forall_const] calls [hc]
  all_goals assumption

/-- **RuneLen, with the runtime's own `countrunes` and `decoderune`**: nothing assumed. -/
theorem correctness (p n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, n] (Pre p n)
      (fun s s' => (s'.regs 0).toNat = countRunes (strBytes s.mem p.toNat n.toNat)) :=
  correctness_of_contract [] (fun _ _ _ _ => True) p n (countrunes_meets [] _ 4144 (Nat.le_refl _))

/-! ## Non-vacuity -/

namespace Witness

open Janus.Contracts.Sat (wsp wg wret wmem)

def ret : Nat := wret
set_option maxRecDepth 100000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- `wmem` with the return address at `[RSP]`. -/
def mem0 : Arm64.Memory := ⟨fun a => if a = wsp + 2 then 0x20 else wmem.bytes a, wmem.regions⟩

def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [0, 0] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h; rcases i with _ | _ | i <;> simp [s0, argReg, intArgRegs] at h ⊢ <;> omega, rfl⟩

theorem pre : Pre 0 0 s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, ?_⟩, by decide, by decide,
    ⟨by decide, by simp⟩, by decide⟩
  have hw : mem0.accessible (wsp - 0x2000) 0x2100 true = true := by decide
  exact Arm64.Memory.accessible_mono _ hw (by decide) (by decide)

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0, 0] s ∧ Pre 0 0 s :=
  ⟨ret, s0, hret, setup, pre⟩

/-- The witness call returns, with the conclusion of `correctness`. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = countRunes (strBytes s0.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat) :=
  correctness 0 0 ret hret s0 setup pre

end Witness

end Proof
