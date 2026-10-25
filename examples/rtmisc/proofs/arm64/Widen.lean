import Extracted

/-!
# `Widen(b uint32) uint64` built with `-d=softfloat`: `runtime.f32to64` is IEEE `convertFormat` (arm64)

```go
func Widen(b uint32) uint64 { return math.Float64bits(float64(math.Float32frombits(b))) }
```

With `-gcflags=…=-d=softfloat` the compiler turns the conversion into a call of the runtime's
software floating point, `runtime.f32to64` (`runtime/softfloat64.go`: `funpack32`, inlined, with
its normalisation loop for subnormals, then `fpack64`). Nothing is assumed about them: the
extraction copies `Widen`, `runtime.f32to64` and `runtime.fpack64`, and the proof executes them.

**Guarantee.** For every argument word `b` (only its low 32 bits are the `uint32`) and every Go
call state in which the stack-growth prologues of `Widen` and `f32to64` fall through and the two
frames are writable (`GuardOK s 48`, `StackOK s 112 0`, the guard word apart), the call returns,
obeys the ABI, and returns the IEEE 754 conversion of the binary32 encoding `b mod 2^32` to
binary64 (`Float.cvt binary32 binary64 .rne`, §5.4.2): exactly its encoding for every number,
zero and infinity (widening is exact, so the rounding direction plays no part), and a NaN for a
NaN (`runtime.nan64`; IEEE leaves the NaN's payload open).

**How.** `fpack_normal` is a callee summary of `runtime.fpack64` for an exact, normal
significand; `loop` is the induction over the subnormal normalisation (`for mant < 1<<23 {
mant <<= 1; exp-- }`, `23 - log2 F` iterations); `cvt32to64_*` (`Janus/Spec/SoftFloat.lean`)
compute the IEEE result by class.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Float

namespace Proof

/-- `UBFIZ X1, X4, #29, #32` as executed. -/
theorem ubfiz29 (x : BitVec 64) :
    x.rotateRight 35 &&& 2305843008676823040#64 &&& 2305843009213693951#64 = (x &&& 4294967295#64) <<< 29 := by
  rw [BitVec.and_assoc, show 2305843008676823040#64 &&& 2305843009213693951#64 = 2305843008676823040#64 by decide]
  exact SoftFloat.ubfiz_eq x 29 32 (by decide) (by decide)

/-- `LSL X0, X6, #32` as executed. -/
theorem lsl32 (x : BitVec 64) :
    x.rotateRight 32 &&& 18446744069414584320#64 &&& 18446744073709551615#64 = (x &&& 4294967295#64) <<< 32 := by
  rw [BitVec.and_assoc, show 18446744069414584320#64 &&& 18446744073709551615#64 = 18446744069414584320#64 by decide]
  exact SoftFloat.ubfiz_eq x 32 32 (by decide) (by decide)

/-- `runtime.fpack64` on an exact normal value (`2^52 ≤ mant < 2^53`, `-1022 ≤ exp ≤ 1023`,
nothing truncated): it returns `mant & (2^52 - 1) | sign | (exp + 1023) << 52`. -/
theorem fpack_normal :
    Summary Extracted.program (segAddr Extracted.program "runtime.fpack64")
      (fun s => 2 ^ 52 ≤ (s.regs 1).toNat ∧ (s.regs 1).toNat < 2 ^ 53 ∧ -1022 ≤ (s.regs 2).toInt ∧
        (s.regs 2).toInt ≤ 1023 ∧ s.regs 3 = 0#64 ∧ (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48)
      (fun s s' => SoftFloat.LeafRet s s'
        (s.regs 1 &&& 4503599627370495#64 ||| (s.regs 0 ||| (s.regs 2 + 1023#64) <<< 52))) := by
  intro s hpc ⟨h1, h1', h2, h2', h3, h30, h30'⟩
  janus_run [SoftFloat.add_flags_nv]
  all_goals exact SoftFloat.leafRet_of _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- The sign bit of the input word, at bit 63 (`AND`, then `LSL #32`). -/
theorem sign_bits (b : BitVec 64) :
    ((b &&& 2147483648#64 &&& 4294967295#64) <<< 32).toNat = (b.toNat % 2 ^ 32 / 2 ^ 31 % 2) * 2 ^ 63 := by
  rw [BitVec.toNat_shiftLeft, BitVec.and_assoc,
    show (2147483648#64 &&& 4294967295#64) = 2147483648#64 by decide, BitVec.toNat_and,
    show (2147483648#64).toNat = 2 ^ 31 by rfl, and_two_pow_eq, Nat.shiftLeft_eq]
  have : b.toNat / 2 ^ 31 % 2 = b.toNat % 2 ^ 32 / 2 ^ 31 % 2 := by omega
  rw [this, Nat.mul_assoc, ← Nat.pow_add]
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt (b.toNat % 2 ^ 32 / 2 ^ 31) (show 0 < 2 by decide); omega)

/-- The result word of the normal case, as a natural number. -/
theorem normal_bits (b : BitVec 64) (F E : Nat) (hF : F < 2 ^ 23) (hE : E < 256) (hFor : F ||| 8388608 = F + 8388608) :
    (((BitVec.ofNat 64 F ||| 8388608#64) &&& 4294967295#64) <<< 29 &&& 4503599627370495#64 |||
      ((b &&& 2147483648#64 &&& 4294967295#64) <<< 32 ||| (BitVec.ofNat 64 E + 896#64) <<< 52)).toNat =
    pack binary64 (decide (b.toNat % 2 ^ 32 / 2 ^ 31 % 2 = 1)) (E + 896) (F * 2 ^ 29) := by
  rw [BitVec.toNat_or, BitVec.toNat_or, sign_bits]
  have h1 : (((BitVec.ofNat 64 F ||| 8388608#64) &&& 4294967295#64) <<< 29 &&& 4503599627370495#64).toNat =
      F * 2 ^ 29 := by
    simp only [BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_or, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega), hFor,
      show (4294967295 : Nat) = 2 ^ 32 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod,
      show (4503599627370495 : Nat) = 2 ^ 52 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have h2 : ((BitVec.ofNat 64 E + 896#64) <<< 52).toNat = (E + 896) * 2 ^ 52 := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  rw [h1, h2]
  exact or_pack64 _ _ (b.toNat % 2 ^ 32 / 2 ^ 31) (by omega) (by omega)

/-- The result word of the subnormal case (after `j` normalisation steps), as a natural number. -/
theorem sub_bits (b : BitVec 64) (m j : Nat) (hm : m < 2 ^ 32) (hj : j ≤ 23) :
    ((BitVec.ofNat 64 m &&& 4294967295#64) <<< 29 &&& 4503599627370495#64 |||
      ((b &&& 2147483648#64 &&& 4294967295#64) <<< 32 ||| (BitVec.ofInt 64 (-126 - (j : Int)) + 1023#64) <<< 52)).toNat =
    pack binary64 (decide (b.toNat % 2 ^ 32 / 2 ^ 31 % 2 = 1)) (897 - j) (m * 2 ^ 29 % 2 ^ 52) := by
  rw [BitVec.toNat_or, BitVec.toNat_or, sign_bits]
  have h1 : ((BitVec.ofNat 64 m &&& 4294967295#64) <<< 29 &&& 4503599627370495#64).toNat = m * 2 ^ 29 % 2 ^ 52 := by
    simp only [BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (show m < 18446744073709551616 by omega),
      show (4294967295 : Nat) = 2 ^ 32 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod,
      show (4503599627370495 : Nat) = 2 ^ 52 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have h2 : ((BitVec.ofInt 64 (-126 - (j : Int)) + 1023#64) <<< 52).toNat = (897 - j) * 2 ^ 52 := by
    have : BitVec.ofInt 64 (-126 - (j : Int)) + 1023#64 = BitVec.ofNat 64 (897 - j) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
      omega
    rw [this]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  rw [h1, h2]
  exact or_pack64 _ _ (b.toNat % 2 ^ 32 / 2 ^ 31) (Nat.mod_lt _ (by decide)) (by omega)

/-- The loop head `CMPW $0x800000, R4` of the subnormal normalisation in `funpack32`. -/
abbrev head : Nat := 0x677a8

/-- The memory at the loop head: the frames of `Widen` and `f32to64` (saved `X30`, `X29`). -/
def M (s : State) (ret : Nat) : Memory :=
  (((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
    (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp - 96) 8 548236).writeLE
    (BitVec.toNat s.sp - 104) 8 (BitVec.toNat s.sp - 56)

/-- The normalisation loop `for mant < 1<<23 { mant <<= 1; exp-- }` of a subnormal binary32
(`F = mant` at entry, `0 < F < 2^23`), from its `j`-th iteration on, and everything after it:
`fpack64` of the normalised significand, the returns of `f32to64` and `Widen`. -/
theorem loop (b : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hal : BitVec.toNat s.sp % 16 = 0) (hb : 112 ≤ BitVec.toNat s.sp) (ha : BitVec.toNat s.sp ≤ 2 ^ 48)
    (hw : s.mem.accessible (BitVec.toNat s.sp - 112) 112 true = true)
    (F : Nat) (hF0 : 0 < F) (hF : F < 2 ^ 23) (hFv : b.toNat % 2 ^ 23 = F) (hEv : b.toNat / 2 ^ 23 % 256 = 0) :
    ∀ k j, j + k = 23 - Nat.log2 F → ∀ S : State, S.pc = BitVec.ofNat 64 head →
      S.regs 4 = BitVec.ofNat 64 (F * 2 ^ j) → S.regs 1 = BitVec.ofInt 64 (-126 - j) →
      S.regs 0 = b → S.sp = s.sp - 96#64 → S.mem = M s ret → S.regs 28 = s.regs 28 →
      S.regs 18 = s.regs 18 →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        ResultIs binary64 (cvt binary32 binary64 .rne (b.toNat % 2 ^ 32)) (s'.regs 0).toNat) := by
  have hL : Nat.log2 F < 23 := (Nat.log2_lt (by omega)).2 hF
  have hL1 : 2 ^ Nat.log2 F ≤ F := Nat.log2_self_le (by omega)
  have hL2 : F < 2 ^ (Nat.log2 F + 1) := Nat.lt_log2_self
  intro k
  induction k with
  | zero =>
    intro j hj S hpc h4 h1 h0 hsp hm h28 h18
    simp only [M] at hm
    have hge : 2 ^ 23 ≤ F * 2 ^ j := by
      calc 2 ^ 23 = 2 ^ Nat.log2 F * 2 ^ j := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ F * 2 ^ j := Nat.mul_le_mul_right _ hL1
    have hlt : F * 2 ^ j < 2 ^ 24 := by
      calc F * 2 ^ j < 2 ^ (Nat.log2 F + 1) * 2 ^ j := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
        _ = 2 ^ 24 := by rw [← Nat.pow_add]; congr 1; omega
    have hte : (BitVec.ofInt 64 (-126 - (j : Int))).toInt = -126 - (j : Int) :=
      SoftFloat.toInt_ofInt64 _ (by omega) (by omega)
    generalize hmj : F * 2 ^ j = m at h4 hge hlt
    janus_run [ubfiz29, lsl32, SoftFloat.sub_flags_c32, BitVec.toNat_setWidth] calls [fpack_normal]
    rename_i r _ hr0
    have hx : b.toNat % 4294967296 / 2 ^ 23 % 256 = 0 := by omega
    have hx2 : b.toNat % 4294967296 % 2 ^ 23 = F := by omega
    rw [cvt32to64_sub _ hx (by omega), hr0, sub_bits b m j (by omega) (by omega), hx2]
    show pack binary64 _ (897 - j) (m * 2 ^ 29 % 2 ^ 52) = pack binary64 _ _ _
    rw [← hmj, Nat.mul_assoc, ← Nat.pow_add, show j + 29 = 52 - Nat.log2 F by omega,
      show 897 - j = Nat.log2 F + 874 by omega]
  | succ k ih =>
    intro j hj S hpc h4 h1 h0 hsp hm h28 h18
    simp only [M] at hm
    have hlt : F * 2 ^ j < 2 ^ 23 := by
      calc F * 2 ^ j < 2 ^ (Nat.log2 F + 1) * 2 ^ j := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
        _ = 2 ^ (Nat.log2 F + 1 + j) := by rw [← Nat.pow_add]
        _ ≤ 2 ^ 23 := Nat.pow_le_pow_right (by decide) (by omega)
    generalize hmj : F * 2 ^ j = m at h4 hlt
    janus_run [SoftFloat.sub_flags_c32, BitVec.toNat_setWidth] until [head]
    apply ih (j + 1) (by omega)
    · rfl
    · simp only [setReg_apply]
      have e : F * 2 ^ (j + 1) = m + m := by rw [Nat.pow_succ, ← Nat.mul_assoc, hmj]; omega
      rw [e]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, ite_true]
      omega
    · simp only [setReg_apply, Nat.reduceEqDiff, ite_false, ite_true]
      rw [show (-126 - ((j + 1 : Nat) : Int)) = (-126 - (j : Int)) + (-1) by omega, BitVec.ofInt_add,
        BitVec.sub_eq_add_neg]
      congr 1
    · simp [setReg_apply, h0]
    · rfl
    · rfl
    · simp [setReg_apply, h28]
    · simp [setReg_apply, h18]

theorem correctness (b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [b]
      (fun s => GuardOK s 48 ∧ StackOK s 112 0 ∧ Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 112) 112)
      (fun _ s' => ResultIs binary64 (cvt binary32 binary64 .rne (b.toNat % 2 ^ 32)) (s'.regs 0).toNat) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgd⟩
  janus_intro hs
  simp only [Disjoint] at hgd
  janus_run until [0x67700]
  have hF : b &&& 8388607#64 = BitVec.ofNat 64 (b.toNat % 2 ^ 23) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (8388607 : Nat) % 2 ^ 64 = 2 ^ 23 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hE : b.rotateRight 23 &&& 18446741874686296319#64 &&& 255#64 = BitVec.ofNat 64 (b.toNat / 2 ^ 23 % 256) := by
    rw [BitVec.and_assoc, show 18446741874686296319#64 &&& 255#64 = BitVec.ofNat 64 (2 ^ 8 - 1) by decide]
    exact SoftFloat.ubfx_eq b 23 8 (by decide) (by decide)
  rw [hF, hE]
  have hF23 : b.toNat % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (by decide)
  have hE256 : b.toNat / 2 ^ 23 % 256 < 256 := Nat.mod_lt _ (by decide)
  generalize hFv : b.toNat % 2 ^ 23 = F at hF23
  generalize hEv : b.toNat / 2 ^ 23 % 256 = E at hE256
  have hFor : F ||| 8388608 = F + 8388608 := by
    have := Nat.two_pow_add_eq_or_of_lt (i := 23) hF23 1
    simp only [Nat.mul_one, Nat.reducePow] at this
    rw [Nat.or_comm]; omega
  have hEi : (BitVec.ofNat 64 E - 127#64).toInt = (E : Int) - 127 := by
    rw [Tactic.toInt64_cond, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    split <;> omega
  janus_run [ubfiz29, lsl32] until [0x677a8, 0x67200]
  · -- +0 / -0
    janus_run
    rw [cvt32to64_zero _ (by omega) (by omega), show (2147483648 : Nat) = 2 ^ 31 by rfl, and_two_pow_eq]
    have : b.toNat / 2 ^ 31 % 2 = b.toNat % 4294967296 / 2 ^ 31 % 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one (b.toNat % 4294967296 / 2 ^ 31) with h | h <;>
      simp [ResultIs, pack, h, this, binary64, Fmt.signBit]
  · -- subnormal: the normalisation loop
    refine loop b ret hret s hal hb (by omega) (by simpa using hw) F (by omega) hF23 hFv (by omega)
      (23 - Nat.log2 F) 0 (by omega) _ rfl (by simp [setReg_apply]) ?_ (by simp [setReg_apply, h_x0])
      rfl rfl (by simp [setReg_apply]) (by simp [setReg_apply])
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
    decide
  · -- infinity
    rw [cvt32to64_inf _ (by omega) (by omega), show (2147483648 : Nat) = 2 ^ 31 by rfl, and_two_pow_eq]
    have : b.toNat / 2 ^ 31 % 2 = b.toNat % 4294967296 / 2 ^ 31 % 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one (b.toNat % 4294967296 / 2 ^ 31) with h | h <;>
      simp [ResultIs, pack, h, this, binary64, Fmt.signBit]
  · -- NaN: the quiet NaN `nan64`
    rw [cvt32to64_nan _ (by omega) (by omega)]
    show isNaN binary64 9221120237041090560 = true
    decide
  · -- normal
    janus_run [ubfiz29, lsl32] calls [fpack_normal]
    rename_i r _ hr0
    have hx : b.toNat % 4294967296 / 2 ^ 23 % 256 = E := by omega
    have hx2 : b.toNat % 4294967296 % 2 ^ 23 = F := by omega
    rw [cvt32to64_normal _ (by omega) (by omega), hr0, normal_bits b F E hF23 hE256 hFor, hx, hx2]
    rfl
  all_goals done

end Proof
