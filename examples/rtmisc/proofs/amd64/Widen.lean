import Janus
import Extracted

/-!
# `Widen(b uint32) uint64` built with `-d=softfloat`: `runtime.f32to64` is IEEE `convertFormat` (amd64)

```go
func Widen(b uint32) uint64 { return math.Float64bits(float64(math.Float32frombits(b))) }
```

As on arm64: with `-d=softfloat` the conversion is a call of `runtime.f32to64`
(`runtime/softfloat64.go`), which the extraction copies together with `runtime.fpack64` and the
proof executes; nothing about them is assumed.

**Guarantee.** For every argument word `b` (the `uint32` is its low 32 bits, `EAX`) and every Go
call state in which the stack-growth prologues of `Widen` and `f32to64` fall through
(`StackGuardOK s 32`), the two frames and the return-address slot are writable
(`StackWritable s 80 8`) and the guard word is apart from them, the call returns, obeys the ABI,
and returns in `RAX` the IEEE 754 conversion of the binary32 encoding `b mod 2^32` to binary64
(`Float.cvt binary32 binary64 .rne`): exactly its encoding for every number, zero and infinity, a
NaN for a NaN.

**How.** As on arm64: `fpack_normal` (a summary of `fpack64` for exact normal values), `loop`
(the subnormal normalisation, by induction), and `cvt32to64_*` for the IEEE side.
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Float

/-- `runtime.fpack64` on an exact normal value (`2^52 ≤ mant < 2^53` in `RBX`,
`-1022 ≤ exp ≤ 1023` in `RCX`, nothing truncated in `RDI`): it returns
`sign | (exp + 1023) << 52 | mant & (2^52 - 1)` in `RAX`. -/
theorem fpack_normal :
    Summary Extracted.program (segAddr Extracted.program "runtime.fpack64")
      (fun s => 2 ^ 52 ≤ (s.regs 3).toNat ∧ (s.regs 3).toNat < 2 ^ 53 ∧ -1022 ≤ (s.regs 1).toInt ∧
        (s.regs 1).toInt ≤ 1023 ∧ s.regs 7 = 0#64 ∧ s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => SoftFloat.LeafRet64 s s'
        (s.regs 0 ||| (s.regs 1 + 1023#64) <<< 52 ||| 4503599627370495#64 &&& s.regs 3)) := by
  intro s hpc ⟨h1, h1', h2, h2', h3, h4, h4'⟩
  janus64_run
  all_goals exact SoftFloat.leafRet64_of _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- The sign bit of the input word, at bit 63 (`ANDL $-0x80000000`, then `SHLQ $32`). -/
theorem sign_bits (b : BitVec 64) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 b &&& 2147483648#32) <<< 32).toNat =
      (b.toNat % 2 ^ 32 / 2 ^ 31 % 2) * 2 ^ 63 := by
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_and, Nat.shiftLeft_eq,
    show (2147483648#32).toNat = 2 ^ 31 by rfl]
  rw [and_two_pow_eq]
  have := Nat.mod_lt (b.toNat % 2 ^ 32 / 2 ^ 31) (show 0 < 2 by decide)
  generalize b.toNat % 2 ^ 32 / 2 ^ 31 % 2 = c at *
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> decide

/-- The result word of the normal case, as a natural number. -/
theorem normal_bits (b : BitVec 64) (F E : Nat) (hF : F < 2 ^ 23) (hE : E < 256)
    (hSor : (BitVec.setWidth 32 (BitVec.ofNat 64 F) ||| 8388608#32).toNat = F + 8388608) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 b &&& 2147483648#32) <<< 32 ||| (BitVec.ofNat 64 E + 896#64) <<< 52 |||
      4503599627370495#64 &&& BitVec.setWidth 64
        (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 F) ||| 8388608#32))) <<< 29).toNat =
    pack binary64 (decide (b.toNat % 2 ^ 32 / 2 ^ 31 % 2 = 1)) (E + 896) (F * 2 ^ 29) := by
  rw [BitVec.toNat_or, BitVec.toNat_or, sign_bits]
  have h1 : (4503599627370495#64 &&& BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 F) ||| 8388608#32))) <<< 29).toNat =
      F * 2 ^ 29 := by
    simp only [BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq, hSor]
    rw [show (4503599627370495#64).toNat = 2 ^ 52 - 1 by rfl, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have h2 : ((BitVec.ofNat 64 E + 896#64) <<< 52).toNat = (E + 896) * 2 ^ 52 := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  rw [h1, h2, Nat.or_comm]
  exact or_pack64 _ _ (b.toNat % 2 ^ 32 / 2 ^ 31) (by omega) (by omega)

/-- The loop head `CMPL SI, $0x800000` of the subnormal normalisation in `funpack32`. -/
abbrev head : Nat := 0x45b267

/-- The memory at the loop head: the frames of `Widen` and `f32to64` (saved `RBP`s, the return
address into `Widen`). -/
def M (s : State) : Arm64.Memory :=
  ((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8 (BitVec.toNat (s.regs 5))).writeLE
    (BitVec.toNat (s.regs 4) - 32) 8 4702291).writeLE (BitVec.toNat (s.regs 4) - 40) 8 (BitVec.toNat (s.regs 4) - 8)

/-- The result word of the subnormal case (after `j` normalisation steps), as a natural number. -/
theorem sub_bits (b : BitVec 64) (m j : Nat) (hm : m < 2 ^ 32) (hj : j ≤ 23) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 b &&& 2147483648#32) <<< 32 |||
        (BitVec.ofInt 64 (-126 - (j : Int)) + 1023#64) <<< 52 |||
      4503599627370495#64 &&& BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 m)) <<< 29).toNat =
    pack binary64 (decide (b.toNat % 2 ^ 32 / 2 ^ 31 % 2 = 1)) (897 - j) (m * 2 ^ 29 % 2 ^ 52) := by
  rw [BitVec.toNat_or, BitVec.toNat_or, sign_bits]
  have h1 : (4503599627370495#64 &&& BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 m)) <<< 29).toNat =
      m * 2 ^ 29 % 2 ^ 52 := by
    simp only [BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    rw [show (4503599627370495 : Nat) % 2 ^ 64 = 2 ^ 52 - 1 by rfl, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have h2 : ((BitVec.ofInt 64 (-126 - (j : Int)) + 1023#64) <<< 52).toNat = (897 - j) * 2 ^ 52 := by
    have : BitVec.ofInt 64 (-126 - (j : Int)) + 1023#64 = BitVec.ofNat 64 (897 - j) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
      omega
    rw [this]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  rw [h1, h2, Nat.or_comm]
  exact or_pack64 _ _ (b.toNat % 2 ^ 32 / 2 ^ 31) (Nat.mod_lt _ (by decide)) (by omega)

/-- The normalisation loop `for mant < 1<<23 { mant <<= 1; exp-- }` of a subnormal binary32
(`F = mant` at entry, `0 < F < 2^23`), from its `j`-th iteration on, and everything after it:
`fpack64` of the normalised significand, the returns of `f32to64` and `Widen`. -/
theorem loop (b : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hle : 80 ≤ BitVec.toNat (s.regs 4)) (hnw : BitVec.toNat (s.regs 4) + 8 ≤ 2 ^ 48)
    (hacc : Arm64.Memory.accessible s.mem (BitVec.toNat (s.regs 4) - 80) 88 true = true)
    (h_ret : Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 4)) 8 = ret)
    (F : Nat) (hF0 : 0 < F) (hF : F < 2 ^ 23) (hFv : b.toNat % 2 ^ 23 = F) (hEv : b.toNat / 2 ^ 23 % 256 = 0) :
    ∀ k j, j + k = 23 - Nat.log2 F → ∀ S : State, S.rip = BitVec.ofNat 64 head →
      S.regs 6 = BitVec.ofNat 64 (F * 2 ^ j) → S.regs 1 = BitVec.ofInt 64 (-126 - j) →
      S.regs 0 = b → S.regs 4 = s.regs 4 - 72#64 → S.regs 5 = s.regs 4 - 40#64 → S.mem = M s →
      S.regs 14 = s.regs 14 → S.xmm = s.xmm →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        ResultIs binary64 (cvt binary32 binary64 .rne (b.toNat % 2 ^ 32)) (s'.regs 0).toNat) := by
  have hL : Nat.log2 F < 23 := (Nat.log2_lt (by omega)).2 hF
  have hL1 : 2 ^ Nat.log2 F ≤ F := Nat.log2_self_le (by omega)
  have hL2 : F < 2 ^ (Nat.log2 F + 1) := Nat.lt_log2_self
  intro k
  induction k with
  | zero =>
    intro j hj S hpc h6 h1 h0 h4 h5 hm h14 hx
    simp only [M] at hm
    have hge : 2 ^ 23 ≤ F * 2 ^ j := by
      calc 2 ^ 23 = 2 ^ Nat.log2 F * 2 ^ j := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ F * 2 ^ j := Nat.mul_le_mul_right _ hL1
    have hlt : F * 2 ^ j < 2 ^ 24 := by
      calc F * 2 ^ j < 2 ^ (Nat.log2 F + 1) * 2 ^ j := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
        _ = 2 ^ 24 := by rw [← Nat.pow_add]; congr 1; omega
    have hte : (BitVec.ofInt 64 (-126 - (j : Int))).toInt = -126 - (j : Int) :=
      SoftFloat.toInt_ofInt64 _ (by omega) (by omega)
    generalize hmj : F * 2 ^ j = m at h6 hge hlt
    janus64_run [BitVec.toNat_setWidth] calls [fpack_normal]
    rename_i r _ hr0
    refine ⟨by rw [hx], ?_⟩
    have hx0 : b.toNat % 4294967296 / 2 ^ 23 % 256 = 0 := by omega
    have hx2 : b.toNat % 4294967296 % 2 ^ 23 = F := by omega
    rw [cvt32to64_sub _ hx0 (by omega), hr0, sub_bits b m j (by omega) (by omega), hx2]
    show pack binary64 _ (897 - j) (m * 2 ^ 29 % 2 ^ 52) = pack binary64 _ _ _
    rw [← hmj, Nat.mul_assoc, ← Nat.pow_add, show j + 29 = 52 - Nat.log2 F by omega,
      show 897 - j = Nat.log2 F + 874 by omega]
  | succ k ih =>
    intro j hj S hpc h6 h1 h0 h4 h5 hm h14 hx
    simp only [M] at hm
    have hlt : F * 2 ^ j < 2 ^ 23 := by
      calc F * 2 ^ j < 2 ^ (Nat.log2 F + 1) * 2 ^ j := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
        _ = 2 ^ (Nat.log2 F + 1 + j) := by rw [← Nat.pow_add]
        _ ≤ 2 ^ 23 := Nat.pow_le_pow_right (by decide) (by omega)
    generalize hmj : F * 2 ^ j = m at h6 hlt
    janus64_run [BitVec.toNat_setWidth] until [head]
    apply ih (j + 1) (by omega)
    · rfl
    · simp only [setRegF_apply, ite_true, reduceIte]
      have e : F * 2 ^ (j + 1) = m + m := by rw [Nat.pow_succ, ← Nat.mul_assoc, hmj]; omega
      rw [e]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · simp only [setRegF_apply, Nat.reduceEqDiff, ite_false, ite_true]
      rw [show (-126 - ((j + 1 : Nat) : Int)) = (-126 - (j : Int)) + (-1) by omega, BitVec.ofInt_add,
        BitVec.sub_eq_add_neg]
      congr 1
    · simp [setRegF_apply, h0]
    · simp [setRegF_apply, h4]
    · simp [setRegF_apply, h5]
    · simp only [M]
    · simp [setRegF_apply, h14]
    · simp [hx]

theorem correctness (b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [b]
      (fun s => StackGuardOK s 32 ∧ StackWritable s 80 8 ∧
        Janus.Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 80) 88)
      (fun _ s' => ResultIs binary64 (cvt binary32 binary64 .rne (b.toNat % 2 ^ 32)) (s'.regs 0).toNat) := by
  intro ret hret s hs ⟨hg, ⟨hle, hnw, hacc⟩, hgd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hacc hle hnw hgl hgb hnw2 hgr hgd
  janus64_run until [0x45b1c2]
  have hDX : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b)) >>> 23)))) =
      BitVec.ofNat 64 (b.toNat / 2 ^ 23 % 256) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have hSI : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b)) &&& 8388607#32) =
      BitVec.ofNat 64 (b.toNat % 2 ^ 23) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (8388607 : Nat) % 2 ^ 32 = 2 ^ 23 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hDX, hSI]
  have hF23 : b.toNat % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (by decide)
  have hE256 : b.toNat / 2 ^ 23 % 256 < 256 := Nat.mod_lt _ (by decide)
  generalize hFv : b.toNat % 2 ^ 23 = F at hF23
  generalize hEv : b.toNat / 2 ^ 23 % 256 = E at hE256
  have hFor : F ||| 8388608 = F + 8388608 := by
    have := Nat.two_pow_add_eq_or_of_lt (i := 23) hF23 1
    simp only [Nat.mul_one, Nat.reducePow] at this
    rw [Nat.or_comm]; omega
  have hEi : (BitVec.ofNat 64 E - 127#64).toInt = (E : Int) - 127 := by
    rw [toInt64_cond, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    split <;> omega
  have hSor : (BitVec.setWidth 32 (BitVec.ofNat 64 F) ||| 8388608#32).toNat = F + 8388608 := by
    rw [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show F < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show F < 2 ^ 32 by omega)]
    exact hFor
  janus64_run until [0x45b267, 0x45ac00]
  · -- +0 / -0
    janus64_run
    have hF0 : F = 0 := by have := congrArg BitVec.toNat hbr; simp at this; omega
    rw [cvt32to64_zero _ (by omega) (by omega), show (2147483648 : Nat) = 2 ^ 31 by rfl, and_two_pow_eq]
    have := Nat.mod_lt (b.toNat % 4294967296 / 2 ^ 31) (show 0 < 2 by decide)
    generalize b.toNat % 4294967296 / 2 ^ 31 % 2 = c at *
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> (simp only [ResultIs]; decide)
  · -- subnormal: the normalisation loop
    have hF0 : F ≠ 0 := by intro h; apply hbr; subst h; rfl
    refine loop b ret hret s hle hnw (by simpa using hacc) h_ret F (by omega) hF23 hFv (by omega)
      (23 - Nat.log2 F) 0 (by omega) _ rfl (by simp [setRegF_apply]) ?_ (by simp [setRegF_apply, h_a0])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) rfl (by simp [setRegF_apply]) rfl
    simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]
    decide
  · -- infinity
    have hF0 : F = 0 := by have := congrArg BitVec.toNat hbr; simp at this; omega
    rw [cvt32to64_inf _ (by omega) (by omega), BitVec.toNat_xor, sign_bits]
    have := Nat.mod_lt (b.toNat % 2 ^ 32 / 2 ^ 31) (show 0 < 2 by decide)
    rw [show b.toNat % 4294967296 = b.toNat % 2 ^ 32 by rfl]
    generalize b.toNat % 2 ^ 32 / 2 ^ 31 % 2 = c at *
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> (simp only [ResultIs]; decide)
  · -- NaN: the quiet NaN `nan64`
    have hF0 : F ≠ 0 := by intro h; apply hbr; subst h; rfl
    rw [cvt32to64_nan _ (by omega) (by omega)]
    show isNaN binary64 9221120237041090560 = true
    decide
  · -- normal
    janus64_run [BitVec.toNat_setWidth] calls [fpack_normal]
    rename_i r _ hr0
    have hx : b.toNat % 4294967296 / 2 ^ 23 % 256 = E := by omega
    have hx2 : b.toNat % 4294967296 % 2 ^ 23 = F := by omega
    rw [cvt32to64_normal _ (by omega) (by omega), hr0, normal_bits b F E hF23 hE256 hSor, hx, hx2]
    rfl

end Proof
