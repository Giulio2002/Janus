import Extracted

/-!
# `Div(n, m complex128) complex128`: complex division through `runtime.complex128div` (amd64)

```go
func Div(n, m complex128) complex128 { return n / m }
```

`GOAMD64=v1` has no FMA, so the compiled Smith's algorithm and Annex G recovery round every
product and sum separately: the specification is `cdiv false` (`Janus.Spec.Complex`).

**Guarantee.** For every call with `n = a + bi` in `X0, X1` and `m = c + di` in `X2, X3` (the low
halves), Go's `MXCSR` controls (`GoMXCSR`: round to nearest, every exception masked, no
`DAZ`/`FTZ`; any sticky flags), the stack-growth prologue falling through, 48 bytes of stack and
the return-address slot writable, the word `runtime.inf` holding `+∞` (`RuntimeInf`, a stated
hypothesis: `.noptrbss`), and the program's read-only data (the constant `1.0`) loaded, `Div`
returns, obeys the ABI, and its results are exactly `cdiv false a b c d` (each part the IEEE
result, or a NaN where the specification has none).

**How.** As on arm64 (`examples/rtmisc/proofs/arm64/Div.lean`): `cdiv_summary` runs Smith's
algorithm to the join, `fixup` the NaN tests, `test1`–`test3` the cases of the recovery and
`body1`–`body3` (with `body3b`, `tail3`) their arithmetic; the SSE2 instructions are related to
the specification by `x_add'`, `x_sub'`, `x_mul'`, `x_div'` and `UCOMISD` by `comis_cf`,
`comis_pf`, `comis_zf` (`Janus.Spec.ComplexMachine`). `MXCSR`'s control bits are tracked through
the raised flags (`GoMXCSR`, `mx_raise_div`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Float Janus.Contracts.Misc Janus.Amd64.FP

namespace Proof

abbrev cdivAddr : Nat := segAddr Extracted.program "runtime.complex128div"

/-- `runtime.inf`: the word the `MOVSD runtime.inf(%rip), %xmm2` at `complex128div+0xe5` reads
(`F2 0F 10 15 disp32`, 8 bytes; the address is the next instruction's plus the signed
displacement). -/
def infAddr : Nat :=
  match Extracted.program.fetch (cdivAddr + 0xe5) with
  | some bs =>
    let disp := bs[4]! + 256 * bs[5]! + 65536 * bs[6]! + 16777216 * bs[7]!
    (cdivAddr + 0xed + disp + 2 ^ 64 - (if disp ≥ 2 ^ 31 then 2 ^ 32 else 0)) % 2 ^ 64
  | none => 0

theorem btr63 : (~~~((9223372036854775808 : Nat) : BitVec 64)).toNat + 1 = 9223372036854775808 := by decide
theorem m63' (x : Nat) : x % 9223372036854775808 % 18446744073709551616 = x % 9223372036854775808 := by omega
theorem m63 (x : Nat) : x % 9223372036854775808 % 340282366920938463463374607431768211456 = x % 9223372036854775808 := by omega
theorem m64 (x : Nat) : x % 18446744073709551616 % 340282366920938463463374607431768211456 = x % 18446744073709551616 := by omega
theorem m128 (x : Nat) : x % 340282366920938463463374607431768211456 % 18446744073709551616 = x % 18446744073709551616 :=
  Nat.mod_mod_of_dvd x (by decide)
theorem low8_merge (v : BitVec 64) (b : BitVec 8) :
    (v &&& 18446744073709551360#64 ||| BitVec.setWidth 64 b).setWidth 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]
theorem isNaN0 : isNaN binary64 0 = false := by decide
theorem tt (b : Bool) : (b = true ∨ b = false) = True := by cases b <;> simp
theorem tt' (b : Bool) : (b = false ∨ b = true) = True := by cases b <;> simp
theorem w8 (x : BitVec 64) : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 x)) = BitVec.setWidth 8 x := by
  simp [BitVec.setWidth_setWidth_of_le]
theorem w8' (x : BitVec 32) : BitVec.setWidth 8 (BitVec.setWidth 64 x) = BitVec.setWidth 8 x := by
  simp [BitVec.setWidth_setWidth_of_le]
theorem w8'' (x : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x))) = BitVec.setWidth 8 x := by
  simp [BitVec.setWidth_setWidth_of_le]
theorem ite8_and (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#8 else 0#8) &&& (if q then 1#8 else 0#8)) = if p ∧ q then 1#8 else 0#8 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
theorem ite8_zero (p : Prop) [Decidable p] : ((if p then 1#8 else 0#8) = 0#8) = ¬p := by
  by_cases hp : p <;> simp [hp]

theorem not63 : (~~~((9223372036854775808 : Nat) : BitVec 64)).toNat = 9223372036854775807 := by decide
theorem cs64 (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.setWidth 64 (BitVec.ofNat 128 x) &&& ~~~((9223372036854775808 : Nat) : BitVec 64) |||
      9223372036854775808#64 &&& BitVec.ofNat 64 y).toNat = copysign x y := by
  rw [← copysign_or]
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, not63]
  rw [show (9223372036854775807 : Nat) = 2 ^ 63 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_eq_of_lt (show x < 2 ^ 128 by omega), Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    Nat.and_comm 9223372036854775808 y]
  have : (x % 2 ^ 63 ||| y &&& 9223372036854775808) < 2 ^ 64 := by
    apply Nat.or_lt_two_pow
    · have := Nat.mod_lt x (show 0 < 2 ^ 63 by decide); omega
    · exact Nat.lt_of_le_of_lt Nat.and_le_left hy
  rw [Nat.mod_eq_of_lt this]

theorem csK (x : BitVec 128) (K : Nat) (hK : K < 2 ^ 64) :
    (BitVec.setWidth 64 x &&& 9223372036854775808#64 ||| BitVec.ofNat 64 K &&& ~~~((9223372036854775808 : Nat) : BitVec 64)).toNat =
      copysign K (x.toNat % 2 ^ 64) := by
  rw [← copysign_or']
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, not63]
  rw [show (9223372036854775807 : Nat) = 2 ^ 63 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hK]
  have : (x.toNat % 2 ^ 64 &&& 9223372036854775808 ||| K % 2 ^ 63) < 2 ^ 64 := by
    apply Nat.or_lt_two_pow
    · exact Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt _ (by decide))
    · have := Nat.mod_lt K (show 0 < 2 ^ 63 by decide); omega
  rw [Nat.mod_eq_of_lt this]
theorem cs1 (x : BitVec 128) :
    (BitVec.setWidth 64 x &&& 9223372036854775808#64 ||| 4607182418800017408#64 &&& ~~~((9223372036854775808 : Nat) : BitVec 64)).toNat =
      copysign 4607182418800017408 (x.toNat % 2 ^ 64) := csK x _ (by decide)
theorem cs0 (x : BitVec 128) :
    (BitVec.setWidth 64 x &&& 9223372036854775808#64 ||| 0#64 &&& ~~~((9223372036854775808 : Nat) : BitVec 64)).toNat =
      copysign 0 (x.toNat % 2 ^ 64) := csK x _ (by decide)

theorem csK' (K y : Nat) (hK : K < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 K &&& ~~~((9223372036854775808 : Nat) : BitVec 64) ||| BitVec.ofNat 64 y &&& 9223372036854775808#64).toNat =
      copysign K y := by
  rw [← copysign_or]
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ofNat, not63]
  rw [show (9223372036854775807 : Nat) = 2 ^ 63 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hK, Nat.mod_eq_of_lt hy]
  have : (K % 2 ^ 63 ||| y &&& 9223372036854775808) < 2 ^ 64 := by
    apply Nat.or_lt_two_pow
    · have := Nat.mod_lt K (show 0 < 2 ^ 63 by decide); omega
    · exact Nat.lt_of_le_of_lt Nat.and_le_left hy
  rw [Nat.mod_eq_of_lt this]
theorem cs0' (y : Nat) (hy : y < 2 ^ 64) :
    (0#64 &&& ~~~((9223372036854775808 : Nat) : BitVec 64) ||| BitVec.ofNat 64 y &&& 9223372036854775808#64).toNat =
      copysign 0 y := csK' 0 y (by decide) hy
theorem cs1' (y : Nat) (hy : y < 2 ^ 64) :
    (4607182418800017408#64 &&& ~~~((9223372036854775808 : Nat) : BitVec 64) ||| BitVec.ofNat 64 y &&& 9223372036854775808#64).toNat =
      copysign 4607182418800017408 y := csK' _ y (by decide) hy

theorem csK'' (K y : Nat) (hK : K < 2 ^ 64) (hy : y < 2 ^ 64) :
    (9223372036854775808#64 &&& BitVec.ofNat 64 y ||| BitVec.ofNat 64 K &&& ~~~((9223372036854775808 : Nat) : BitVec 64)).toNat =
      copysign K y := by
  rw [BitVec.or_comm, BitVec.and_comm (9223372036854775808#64)]; exact csK' K y hK hy
theorem cs0'' (y : Nat) (hy : y < 2 ^ 64) :
    (9223372036854775808#64 &&& BitVec.ofNat 64 y ||| 0#64 &&& ~~~((9223372036854775808 : Nat) : BitVec 64)).toNat =
      copysign 0 y := csK'' 0 y (by decide) hy
theorem cs1'' (y : Nat) (hy : y < 2 ^ 64) :
    (9223372036854775808#64 &&& BitVec.ofNat 64 y ||| 4607182418800017408#64 &&& ~~~((9223372036854775808 : Nat) : BitVec 64)).toNat =
      copysign 4607182418800017408 y := csK'' _ y (by decide) hy
theorem mod_div64 (x : Nat) : x % 18446744073709551616 / 18446744073709551616 = 0 :=
  Nat.div_eq_of_lt (Nat.mod_lt _ (by decide))

theorem cs_mod128 (x y : Nat) : copysign x y % 340282366920938463463374607431768211456 = copysign x y :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (copysign_lt x y) (by decide))
theorem cs_div64 (x y : Nat) : copysign x y / 18446744073709551616 = 0 := Nat.div_eq_of_lt (copysign_lt x y)
theorem inf128 : infBits % 340282366920938463463374607431768211456 = infBits := by decide

theorem cs64inf (y : Nat) (hy : y < 2 ^ 64) :
    (BitVec.setWidth 64 (BitVec.ofNat 128 infBits) &&& ~~~((9223372036854775808 : Nat) : BitVec 64) |||
      9223372036854775808#64 &&& BitVec.ofNat 64 y).toNat = copysign infBits y := cs64 _ y (by decide) hy

/-- The side conditions of the lifting lemmas. -/
macro "lt64" : tactic => `(tactic| first | exact Nat.mod_lt _ (by decide) | exact copysign_lt _ _ | assumption)

/-- The return of `complex128div` from `S` with results `X` (`X0`) and `Y` (`X1`). -/
def Out (S : State) (X Y : Option Nat) (s' : State) : Prop :=
  (s'.regs 4 = S.regs 4 + 8#64 ∧ s'.regs 5 = S.regs 5 ∧ s'.regs 14 = S.regs 14 ∧ s'.mem = S.mem ∧
    s'.ymmHi = S.ymmHi ∧ s'.fsBase = S.fsBase ∧ s'.df = S.df ∧ s'.xmm 15 = S.xmm 15) ∧
  ResultIs binary64 X ((s'.xmm 0).toNat % 2 ^ 64) ∧ ResultIs binary64 Y ((s'.xmm 1).toNat % 2 ^ 64)

/-- What the return needs: the return address readable and canonical, `MXCSR` default, `runtime.inf`. -/
structure Env (S : State) : Prop where
  mx : GoABI.GoMXCSR S
  ra : S.mem.accessible (S.regs 4).toNat 8 false = true
  ral : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47
  sp : (S.regs 4).toNat + 8 ≤ 2 ^ 48
  inf : RuntimeInf S.mem infAddr
  one : S.mem.accessible 4825504 8 false = true ∧ S.mem.readLE 4825504 8 = 4607182418800017408

/-- The constant `1.0` (`$f64.3ff0000000000000`, the program's read-only data) in memory. -/
theorem one_loaded {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) :
    m.accessible 4825504 8 false = true ∧ m.readLE 4825504 8 = 4607182418800017408 := by
  have hseg : SegLoaded m (Extracted.program.data[0]'(by decide)) := hd _ (List.getElem_mem _)
  have hacc := hseg.accessible
  have hrd := hseg.readLE 0 8 (by decide +kernel)
  have hlen : (Extracted.program.data[0]'(by decide)).bytes.length = 8 := by decide +kernel
  have hbase : (Extracted.program.data[0]'(by decide)).base = 4825504 := rfl
  have hv : Janus.Tactic.leOfBytes (((Extracted.program.data[0]'(by decide)).bytes.drop 0).take 8) =
      4607182418800017408 := by decide +kernel
  rw [hlen, hbase] at hacc
  rw [hbase, hv] at hrd
  exact ⟨hacc, by simpa using hrd⟩

/-- `GoMXCSR` after instructions raised flags. -/
theorem gomx_raise {S S' : State} (h : GoABI.GoMXCSR S) (x : Nat)
    (h' : S'.mxcsr = BitVec.ofNat 32 ((S.mxcsr.toNat ||| x % 64) % 4294967296)) : GoABI.GoMXCSR S' := by
  unfold GoABI.GoMXCSR at *; rw [h', BitVec.toNat_ofNat, Nat.mod_mod, mx_raise_div, Nat.mod_eq_of_lt S.mxcsr.isLt, h]

/-- `Env` at a later state of a block that left the memory, `RSP` and the control bits of `MXCSR`
alone (`hm`, `hra`, … the facts of the block's entry). -/
macro "env_tac" hm:ident hra:ident hral:ident hsp:ident hinf:ident hdl:ident : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold GoABI.GoMXCSR
    dsimp only
    simp only [BitVec.toNat_ofNat, Nat.reducePow, mx_raise_div, Nat.mod_mod, GoMXCSR.mod $hm]
    first | exact $hm | (simp only [GoMXCSR.mod $hm]; exact $hm)
  · exact $hra
  · exact $hral
  · exact $hsp
  · exact $hinf
  · exact $hdl))

/-- `Out` macro for a path that returned. -/
macro "out_tac" : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals try (first | rfl | (simp only [setXmmF_apply, Nat.reduceEqDiff, reduceIte]; done) | (simp only [setRegF_apply]; done) | (simp only [setRegF_apply, Nat.reduceEqDiff, reduceIte]; done))))

set_option maxHeartbeats 0 in
/-- `m == 0` and a number in the numerator. -/
theorem body1 (S : State) (a b c : Nat) (hpc : S.rip = BitVec.ofNat 64 (cdivAddr + 0xe5)) (h : Env S)
    (h0 : (S.xmm 0).toNat % 2 ^ 64 = a) (h7 : (S.xmm 7).toNat % 2 ^ 64 = b) (hr1 : S.regs 1 = BitVec.ofNat 64 c) (hc : c < 2 ^ 64) :
    ReachesRet Extracted.program (retAddrOf S) S
      (Out S (O.mul2 (some (copysign infE c)) (some a)) (O.mul2 (some (copysign infE c)) (some b))) := by
  obtain ⟨hm, hra, hral, hsp, ⟨hi1, hi2, hi3⟩, hdl⟩ := h
  janus_eval_nat hI : infAddr
  rw [hI] at hi1 hi2 hi3
  have ha : a < 2 ^ 64 := h0 ▸ Nat.mod_lt _ (by decide)
  have hb : b < 2 ^ 64 := h7 ▸ Nat.mod_lt _ (by decide)
  janus64_run [h0, h7, hr1, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, hi3, lo64, btr63, m63', m63, m64, cs64inf c hc, Nat.mod_one]
  out_tac
  all_goals try simp only [setXmmF_apply, Nat.reduceEqDiff, reduceIte, BitVec.toNat_ofNat, Nat.reducePow, m64, m128,
    lo64, copysign_mod, Nat.mod_mod]
  · exact x_mul' (Janus.Arm64.FP.r_some _) (Janus.Arm64.FP.r_some _) (copysign_lt _ _) ha
  · exact x_mul' (Janus.Arm64.FP.r_some _) (Janus.Arm64.FP.r_some _) (copysign_lt _ _) hb

set_option maxHeartbeats 0 in
/-- An infinite numerator over a finite denominator (operand order of the code). -/
theorem body2 (S : State) (a b c d : Nat) (hpc : S.rip = BitVec.ofNat 64 (cdivAddr + 0x2be)) (h : Env S)
    (h0 : (S.xmm 0).toNat % 2 ^ 64 = a) (h4 : (S.xmm 4).toNat % 2 ^ 64 = b)
    (h7 : (S.xmm 7).toNat % 2 ^ 64 = c) (h2 : (S.xmm 2).toNat % 2 ^ 64 = d) :
    ReachesRet Extracted.program (retAddrOf S) S
      (Out S (O.mul2 (O.add2 (O.mul2 (some c) (some (inf2one a))) (O.mul2 (some d) (some (inf2one b)))) (some infE))
        (O.mul2 (O.sub2 (O.mul2 (some c) (some (inf2one b))) (O.mul2 (some (inf2one a)) (some d))) (some infE))) := by
  obtain ⟨hm, hra, hral, hsp, ⟨hi1, hi2, hi3⟩, hdl⟩ := h
  have ⟨ho1, ho2⟩ := hdl
  janus_eval_nat hI : infAddr
  rw [hI] at hi1 hi2 hi3
  have ha : a < 2 ^ 64 := h0 ▸ Nat.mod_lt _ (by decide)
  have hb : b < 2 ^ 64 := h4 ▸ Nat.mod_lt _ (by decide)
  have hc : c < 2 ^ 64 := h7 ▸ Nat.mod_lt _ (by decide)
  have hd : d < 2 ^ 64 := h2 ▸ Nat.mod_lt _ (by decide)
  janus64_run [h0, h4, h7, h2, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, hi3, ho2, lo64, btr63, m63', m63, m64, Nat.mod_one, comis_cf, comis_pf, comis_zf,
    Janus.Arm64.FP.eq64_self, or_self, Bool.not_eq_true', tt, tt', isNaN_sub_self a ha, isNaN_sub_self b hb]
  all_goals out_tac
  all_goals try simp only [setXmmF_apply, Nat.reduceEqDiff, reduceIte, BitVec.toNat_ofNat, Nat.reducePow, m64, m128,
    lo64, copysign_mod, Nat.mod_mod, cs1, cs0, h0, h4, cs_mod128, cs_div64, inf128, Nat.zero_mul, Nat.zero_add]
  all_goals try simp only [Bool.not_eq_true, Bool.not_eq_false] at *
  all_goals try simp only [inf2one, isInf64, isNaN64, *, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false,
    Bool.true_and, Bool.and_true, ite_false, ite_true, Bool.false_eq_true, reduceIte]
  all_goals first
    | exact x_mul' (x_add' (x_mul' (Janus.Arm64.FP.r_some _) (Janus.Arm64.FP.r_some _) (by lt64) (by lt64))
        (x_mul' (Janus.Arm64.FP.r_some _) (Janus.Arm64.FP.r_some _) (by lt64) (by lt64)) (by lt64) (by lt64))
        (Janus.Arm64.FP.r_some _) (by lt64) (by decide)
    | exact x_mul' (x_sub' (x_mul' (Janus.Arm64.FP.r_some _) (Janus.Arm64.FP.r_some _) (by lt64) (by lt64))
        (x_mul' (Janus.Arm64.FP.r_some _) (Janus.Arm64.FP.r_some _) (by lt64) (by lt64)) (by lt64) (by lt64))
        (Janus.Arm64.FP.r_some _) (by lt64) (by decide)

set_option maxHeartbeats 0 in
/-- The last two products of `body3` (by the zero in `X3`) and the return. -/
theorem tail3 (S : State) (p q : Nat) (P Q : Option Nat) (hpc : S.rip = BitVec.ofNat 64 (cdivAddr + 0x2b0))
    (h : Env S) (h1 : (S.xmm 1).toNat % 2 ^ 64 = p) (h6 : (S.xmm 6).toNat % 2 ^ 64 = q)
    (h3 : (S.xmm 3).toNat % 2 ^ 64 = 0) (hP : ResultIs binary64 P p) (hQ : ResultIs binary64 Q q) :
    ReachesRet Extracted.program (retAddrOf S) S (Out S (O.mul2 P (some 0)) (O.mul2 Q (some 0))) := by
  obtain ⟨hm, hra, hral, hsp, ⟨hi1, hi2, hi3⟩, hdl⟩ := h
  have hp : p < 2 ^ 64 := h1 ▸ Nat.mod_lt _ (by decide)
  have hq : q < 2 ^ 64 := h6 ▸ Nat.mod_lt _ (by decide)
  janus64_run [h1, h6, h3, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, lo64, m64, Nat.mod_one]
  all_goals out_tac
  all_goals try simp only [setXmmF_apply, Nat.reduceEqDiff, reduceIte, BitVec.toNat_ofNat, Nat.reducePow, m64, m128,
    lo64, mod_div64, Nat.zero_mul, Nat.zero_add, Nat.mod_mod]
  · exact x_mul' hP (Janus.Arm64.FP.r_some 0) hp (by decide)
  · exact x_mul' hQ (Janus.Arm64.FP.r_some 0) hq (by decide)

/-- `Out` from a later state of the same run. -/
theorem out_mono {S S' : State} {X Y X' Y' : Option Nat} {r : W64}
    (h : ReachesRet Extracted.program r S' (Out S' X Y)) (hX : X = X') (hY : Y = Y')
    (h4 : S'.regs 4 = S.regs 4) (h5 : S'.regs 5 = S.regs 5) (h14 : S'.regs 14 = S.regs 14)
    (hm : S'.mem = S.mem) (hy : S'.ymmHi = S.ymmHi) (hfs : S'.fsBase = S.fsBase) (hdf : S'.df = S.df)
    (hx : S'.xmm 15 = S.xmm 15) :
    ReachesRet Extracted.program r S' (Out S X' Y') := by
  subst hX hY
  obtain ⟨k, s', hs, hpc, ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩, h9, h10⟩ := h
  exact ⟨k, s', hs, hpc, ⟨by rw [e1, h4], e2.trans h5, e3.trans h14, e4.trans hm, e5.trans hy,
    e6.trans hfs, e7.trans hdf, e8.trans hx⟩, h9, h10⟩

/-- What the tests keep: the operands in `X0, X7, X2, X5`, the bits of `c`, `d` in `RCX`, `RDX`. -/
structure Inv (S : State) (a b c d : Nat) : Prop where
  env : Env S
  v0 : (S.xmm 0).toNat % 2 ^ 64 = a
  v7 : (S.xmm 7).toNat % 2 ^ 64 = b
  v2 : (S.xmm 2).toNat % 2 ^ 64 = c
  v5 : (S.xmm 5).toNat % 2 ^ 64 = d
  r1 : S.regs 1 = BitVec.ofNat 64 c
  r2 : S.regs 2 = BitVec.ofNat 64 d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- The second half of `body3`, from the test of `d`, with `c' = inf2one c` in `RBX`. -/
theorem body3b (S : State) (a b c d : Nat) (hpc : S.rip = BitVec.ofNat 64 (cdivAddr + 0x257)) (h : Env S)
    (h5 : (S.xmm 5).toNat % 2 ^ 64 = a) (h8 : (S.xmm 8).toNat % 2 ^ 64 = b)
    (h4 : (S.xmm 4).toNat % 2 ^ 64 = d) (h3 : (S.xmm 3).toNat % 2 ^ 64 = 0)
    (cc : Nat) (hcc : cc < 2 ^ 64) (hr3 : S.regs 3 = BitVec.ofNat 64 cc) (hr0 : S.regs 0 = 9223372036854775808#64) (hr2 : S.regs 2 = BitVec.ofNat 64 d) :
    ReachesRet Extracted.program (retAddrOf S) S
      (Out S (O.mul2 (O.add2 (O.mul2 (some cc) (some a)) (O.mul2 (some b) (some (inf2one d)))) (some 0))
        (O.mul2 (O.sub2 (O.mul2 (some cc) (some b)) (O.mul2 (some (inf2one d)) (some a))) (some 0))) := by
  janus_eval_nat hcd : cdivAddr
  have hinf := h.inf
  obtain ⟨hm, hra, hral, hsp, ⟨hi1, hi2, hi3⟩, hdl⟩ := h
  have ⟨ho1, ho2⟩ := hdl
  have ha : a < 2 ^ 64 := h5 ▸ Nat.mod_lt _ (by decide)
  have hb : b < 2 ^ 64 := h8 ▸ Nat.mod_lt _ (by decide)
  have hd : d < 2 ^ 64 := h4 ▸ Nat.mod_lt _ (by decide)
  have hc1 : cc % 340282366920938463463374607431768211456 = cc := Nat.mod_eq_of_lt (by omega)
  have hc2 : cc / 18446744073709551616 = 0 := Nat.div_eq_of_lt hcc
  janus64_run [h5, h8, h4, h3, hr3, hr2, hr0, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, ho2, lo64, btr63, m63', m63, m64, Nat.mod_one, comis_cf, comis_pf,
    comis_zf, Janus.Arm64.FP.eq64_self, or_self, Bool.not_eq_true', tt, tt', isNaN_sub_self d hd]
    until [cdivAddr + 0x2b0]
  all_goals refine out_mono (tail3 _ _ _ (O.add2 (O.mul2 (some cc) (some a)) (O.mul2 (some b) (some (inf2one d))))
    (O.sub2 (O.mul2 (some cc) (some b)) (O.mul2 (some (inf2one d)) (some a))) ?_ ?_ rfl rfl ?_ ?_ ?_) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  all_goals try (rw [hcd]; try rfl; done)
  all_goals try env_tac hm hra hral hsp hinf hdl
  all_goals try (simp only [setXmmF_apply, Nat.reduceEqDiff, reduceIte]; exact h3)
  all_goals try simp only [setXmmF_apply, Nat.reduceEqDiff, reduceIte, BitVec.toNat_ofNat, Nat.reducePow, m64, m128,
    lo64, copysign_mod, Nat.mod_mod, cs1' d hd, cs0' d hd, cs1'' d hd,
    cs0'' d hd, mod_div64, cs_mod128, cs_div64, hc1, hc2, Nat.zero_mul, Nat.zero_add]
  all_goals try simp only [m64, Nat.mod_mod]
  all_goals try simp only [Bool.not_eq_true, Bool.not_eq_false] at *
  all_goals try simp only [inf2one, isInf64, isNaN64, *, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false,
    Bool.true_and, Bool.and_true, ite_false, ite_true, Bool.false_eq_true, reduceIte]
  all_goals try (rw [hcd]; try rfl; done)
  all_goals try (simp only [hcd]; done)
  all_goals try env_tac hm hra hral hsp hinf hdl
  all_goals first
    | exact x_add' (x_mul' (Janus.Arm64.FP.r_some _) (Janus.Arm64.FP.r_some _) (by lt64) (by lt64))
        (x_mul' (Janus.Arm64.FP.r_some _) (Janus.Arm64.FP.r_some _) (by lt64) (by lt64)) (by lt64) (by lt64)
    | exact x_sub' (x_mul' (Janus.Arm64.FP.r_some _) (Janus.Arm64.FP.r_some _) (by lt64) (by lt64))
        (x_mul' (Janus.Arm64.FP.r_some _) (Janus.Arm64.FP.r_some _) (by lt64) (by lt64)) (by lt64) (by lt64)
    | (env_tac hm hra hral hsp hinf hdl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- An infinite denominator over a finite numerator: zeros (operand order of the code). -/
theorem body3 (S : State) (a b c d : Nat) (hpc : S.rip = BitVec.ofNat 64 (cdivAddr + 0x218)) (h : Env S)
    (h5 : (S.xmm 5).toNat % 2 ^ 64 = a) (h8 : (S.xmm 8).toNat % 2 ^ 64 = b)
    (h2 : (S.xmm 2).toNat % 2 ^ 64 = c) (h4 : (S.xmm 4).toNat % 2 ^ 64 = d) (h3 : (S.xmm 3).toNat % 2 ^ 64 = 0)
    (hr1 : S.regs 1 = BitVec.ofNat 64 c) (hr2 : S.regs 2 = BitVec.ofNat 64 d) :
    ReachesRet Extracted.program (retAddrOf S) S
      (Out S (O.mul2 (O.add2 (O.mul2 (some (inf2one c)) (some a)) (O.mul2 (some b) (some (inf2one d)))) (some 0))
        (O.mul2 (O.sub2 (O.mul2 (some (inf2one c)) (some b)) (O.mul2 (some (inf2one d)) (some a))) (some 0))) := by
  janus_eval_nat hcd : cdivAddr
  have hinf := h.inf
  obtain ⟨hm, hra, hral, hsp, ⟨hi1, hi2, hi3⟩, hdl⟩ := h
  have ⟨ho1, ho2⟩ := hdl
  have ha : a < 2 ^ 64 := h5 ▸ Nat.mod_lt _ (by decide)
  have hb : b < 2 ^ 64 := h8 ▸ Nat.mod_lt _ (by decide)
  have hc : c < 2 ^ 64 := h2 ▸ Nat.mod_lt _ (by decide)
  have hd : d < 2 ^ 64 := h4 ▸ Nat.mod_lt _ (by decide)
  janus64_run [h5, h8, h2, h4, h3, hr1, hr2, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, ho2, lo64, btr63,
    m63', m63, m64, Nat.mod_one, comis_cf, comis_pf, comis_zf, Janus.Arm64.FP.eq64_self, or_self, Bool.not_eq_true',
    tt, tt', isNaN_sub_self c hc] until [cdivAddr + 0x257]
  all_goals refine out_mono (body3b _ a b c d ?_ ?_ ?_ ?_ ?_ ?_ (inf2one c) (copysign_lt _ _) ?_ ?_ ?_) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  all_goals try (rw [hcd]; try rfl; done)
  all_goals try env_tac hm hra hral hsp hinf hdl
  all_goals try (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; assumption)
  all_goals try (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; done)
  all_goals try simp only [Bool.not_eq_true, Bool.not_eq_false] at *
  all_goals simp only [setRegF_apply, Nat.reduceEqDiff, reduceIte]
  all_goals apply BitVec.eq_of_toNat_eq
  all_goals first | rw [cs0' c hc] | rw [cs1' c hc]
  all_goals simp only [inf2one, BitVec.toNat_ofNat, isInf64, isNaN64, *, Bool.not_true, Bool.not_false,
    Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, ite_false, ite_true, Bool.false_eq_true, reduceIte]
  all_goals rw [Nat.mod_eq_of_lt (copysign_lt _ _)]

theorem zero64 : zero binary64 false = 0 := rfl
theorem eq64_zero_comm (d : Nat) : eq64 0 d = eq64 d 0 := by
  unfold eq64; rw [Bool.or_comm, Janus.Arm64.FP.Val.eq_comm']

theorem nan_or (p q : Bool) : ((p = true ∨ q = true) ∧ p = false) = (q = true ∧ p = false) := by
  cases p <;> simp

theorem eq64_nan {x y : Nat} (h : eq64 x y = true) : isNaN binary64 x = false := by
  unfold eq64 at h; cases hx : isNaN binary64 x <;> simp_all
theorem eq64_nan' {x y : Nat} (h : eq64 x y = true) : isNaN binary64 y = false := by
  unfold eq64 at h; cases hy : isNaN binary64 y <;> simp_all
theorem hn1_of (c d : Nat) (x : Bool)
    (h : ¬(eq64 c 0 = true ∧ isNaN binary64 c = false ∧ eq64 d 0 = true ∧ isNaN binary64 d = false)) :
    (eq64 c 0 && eq64 d 0 && x) = false := by
  cases h1 : eq64 c 0 <;> cases h2 : eq64 d 0 <;> simp
  exact absurd ⟨h1, eq64_nan h1, h2, eq64_nan h2⟩ h

/-- The simp set of the branch conditions. -/
macro "cond_simp" : tactic => `(tactic| (
  try simp only [Bool.not_eq_true, Bool.not_eq_false, Bool.and_eq_true] at *
  try simp only [zero64, eq64_zero_comm, nan_or, and_self, and_assoc] at *
  try simp only [isInf64, isNaN64, isZero64, zero64, *, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false,
    Bool.true_and, Bool.and_true, Bool.or_true, Bool.true_or, Bool.false_or, Bool.or_false, ite_false, ite_true,
    Bool.false_eq_true, reduceIte, false_and, and_false, true_and, and_true, false_or, or_false, true_or, or_true,
    not_false_eq_true, not_true_eq_false]))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- The third case of the recovery, and the fall-through that keeps Smith's two NaNs. -/
theorem test3 (S : State) (a b c d e f : Nat) (hpc : S.rip = BitVec.ofNat 64 (cdivAddr + 0x1a2))
    (h : Inv S a b c d) (h1 : (S.xmm 1).toNat % 2 ^ 64 = e) (h6 : (S.xmm 6).toNat % 2 ^ 64 = f)
    (h3 : (S.xmm 3).toNat % 2 ^ 64 = 0) (he : isNaN binary64 e = true) (hf' : isNaN binary64 f = true)
    (hn1 : (isZero64 c && isZero64 d && (!isNaN64 a || !isNaN64 b)) = false)
    (hn2 : ((isInf64 a || isInf64 b) && isFinite64 c && isFinite64 d) = false) :
    ReachesRet Extracted.program (retAddrOf S) S
      (Out S (recover false a b c d (none, none)).1 (recover false a b c d (none, none)).2) := by
  janus_eval_nat hcd : cdivAddr
  have hinf := h.env.inf
  obtain ⟨⟨hm, hra, hral, hsp, ⟨hi1, hi2, hi3⟩, hdl⟩, h0, h7, h2, h5, hr1, hr2⟩ := h
  have hel : e < 2 ^ 64 := h1 ▸ Nat.mod_lt _ (by decide)
  have hfl : f < 2 ^ 64 := h6 ▸ Nat.mod_lt _ (by decide)
  have ha : a < 2 ^ 64 := h0 ▸ Nat.mod_lt _ (by decide)
  have hb : b < 2 ^ 64 := h7 ▸ Nat.mod_lt _ (by decide)
  have hc : c < 2 ^ 64 := h2 ▸ Nat.mod_lt _ (by decide)
  have hd : d < 2 ^ 64 := h5 ▸ Nat.mod_lt _ (by decide)
  janus64_run [h0, h7, h2, h5, h1, h6, h3, hr1, hr2, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, lo64,
    btr63, m63', m63, m64, Nat.mod_one, comis_cf, comis_pf, comis_zf, Janus.Arm64.FP.eq64_self, or_self,
    Bool.not_eq_true', tt, tt', isNaN_sub_self a ha, isNaN_sub_self b hb, isNaN_sub_self c hc,
    isNaN_sub_self d hd] until [cdivAddr + 0x218]
  -- the paths that return Smith's NaNs
  all_goals try (
    out_tac
    all_goals simp only [recover, hn1, hn2]
    all_goals cond_simp
    all_goals simp only [ResultIs, setXmmF_apply, Nat.reduceEqDiff, reduceIte, BitVec.toNat_ofNat, Nat.reducePow,
      m64, m128, h1, h6, Nat.mod_eq_of_lt hel, Nat.mod_eq_of_lt hfl, he, hf']
    done)
  -- the third case
  all_goals refine out_mono (body3 _ a b c d ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_ ?_ rfl rfl rfl rfl rfl rfl rfl rfl
  all_goals try (rw [hcd]; try rfl; done)
  all_goals try env_tac hm hra hral hsp hinf hdl
  all_goals try (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; assumption)
  all_goals try (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; done)
  all_goals simp only [recover, hn1, hn2]
  all_goals cond_simp
  all_goals simp only [O.mac, O.msc, reduceIte, Bool.false_eq_true]
  all_goals try rw [O.mul2_comm (some 0), O.add2_comm (O.mul2 (some b) _), O.mul2_comm (some a)]
  all_goals try rw [O.mul2_comm (some 0), O.mul2_comm (some b), O.mul2_comm (some a)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- The second case of the recovery. -/
theorem test2 (S : State) (a b c d e f : Nat) (hpc : S.rip = BitVec.ofNat 64 (cdivAddr + 0x133))
    (h : Inv S a b c d) (h1 : (S.xmm 1).toNat % 2 ^ 64 = e) (h6 : (S.xmm 6).toNat % 2 ^ 64 = f)
    (h3 : (S.xmm 3).toNat % 2 ^ 64 = 0) (he : isNaN binary64 e = true) (hf' : isNaN binary64 f = true)
    (hn1 : (isZero64 c && isZero64 d && (!isNaN64 a || !isNaN64 b)) = false) :
    ReachesRet Extracted.program (retAddrOf S) S
      (Out S (recover false a b c d (none, none)).1 (recover false a b c d (none, none)).2) := by
  janus_eval_nat hcd : cdivAddr
  have hinv := h
  have hinf := h.env.inf
  obtain ⟨⟨hm, hra, hral, hsp, ⟨hi1, hi2, hi3⟩, hdl⟩, h0, h7, h2, h5, hr1, hr2⟩ := h
  have ha : a < 2 ^ 64 := h0 ▸ Nat.mod_lt _ (by decide)
  have hb : b < 2 ^ 64 := h7 ▸ Nat.mod_lt _ (by decide)
  have hc : c < 2 ^ 64 := h2 ▸ Nat.mod_lt _ (by decide)
  have hd : d < 2 ^ 64 := h5 ▸ Nat.mod_lt _ (by decide)
  janus64_run [h0, h7, h2, h5, h1, h6, h3, hr1, hr2, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, lo64,
    btr63, m63', m63, m64, Nat.mod_one, comis_cf, comis_pf, comis_zf, Janus.Arm64.FP.eq64_self, or_self,
    Bool.not_eq_true', tt, tt', isNaN_sub_self a ha, isNaN_sub_self b hb, isNaN_sub_self c hc,
    isNaN_sub_self d hd] until [cdivAddr + 0x1a2, cdivAddr + 0x2be]
  all_goals first
    | (refine out_mono (body2 _ a b c d ?_ ?_ ?_ ?_ ?_ ?_) ?_ ?_ rfl rfl rfl rfl rfl rfl rfl rfl
       · rw [hcd]; try rfl
       · env_tac hm hra hral hsp hinf hdl
       all_goals try (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; assumption)
       all_goals simp only [recover, hn1]
       all_goals cond_simp
       all_goals simp only [O.mac, O.msc, reduceIte, Bool.false_eq_true]
       all_goals try rw [O.mul2_comm (some infE), O.add2_comm (O.mul2 (some (inf2one b)) _),
         O.mul2_comm (some (inf2one a)), O.mul2_comm (some (inf2one b))]
       all_goals try rw [O.mul2_comm (some infE), O.mul2_comm (some (inf2one b))]
       done)
    | (refine out_mono (test3 _ a b c d e f ?_ ?_ ?_ ?_ ?_ he hf' hn1 ?_) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
       · rw [hcd]; try rfl
       · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
         · env_tac hm hra hral hsp hinf hdl
         all_goals first | assumption | (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; assumption)
       all_goals try (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; assumption)
       all_goals cond_simp)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- The first case of the recovery (`m == 0 && (!isNaN(a) || !isNaN(b))`). -/
theorem test1 (S : State) (a b c d e f : Nat) (hpc : S.rip = BitVec.ofNat 64 (cdivAddr + 0xb2))
    (h : Inv S a b c d) (h1 : (S.xmm 1).toNat % 2 ^ 64 = e) (h6 : (S.xmm 6).toNat % 2 ^ 64 = f)
    (he : isNaN binary64 e = true) (hf' : isNaN binary64 f = true) :
    ReachesRet Extracted.program (retAddrOf S) S
      (Out S (recover false a b c d (none, none)).1 (recover false a b c d (none, none)).2) := by
  janus_eval_nat hcd : cdivAddr
  have hinf := h.env.inf
  obtain ⟨⟨hm, hra, hral, hsp, ⟨hi1, hi2, hi3⟩, hdl⟩, h0, h7, h2, h5, hr1, hr2⟩ := h
  have hc : c < 2 ^ 64 := h2 ▸ Nat.mod_lt _ (by decide)
  janus64_run [h0, h7, h2, h5, h1, h6, hr1, hr2, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, lo64,
    btr63, m63', m63, m64, Nat.mod_one, comis_cf, comis_pf, comis_zf, Janus.Arm64.FP.eq64_self, or_self,
    Bool.not_eq_true', tt, tt', isNaN0, BitVec.setWidth_and, w8, w8', w8'', low8_merge, ite8_and, ite8_zero]
    until [cdivAddr + 0xe5, cdivAddr + 0x133]
  all_goals first
    | (refine out_mono (body1 _ a b c ?_ ?_ ?_ ?_ ?_ hc) ?_ ?_ rfl rfl rfl rfl rfl rfl rfl rfl
       · rw [hcd]; try rfl
       · env_tac hm hra hral hsp hinf hdl
       all_goals try (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; assumption)
       all_goals simp only [recover]
       all_goals cond_simp
       done)
    | (refine out_mono (test2 _ a b c d e f ?_ ?_ ?_ ?_ ?_ he hf' ?_) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
       · rw [hcd]; try rfl
       · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
         · env_tac hm hra hral hsp hinf hdl
         all_goals first | assumption | (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; assumption)
       all_goals try (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; assumption)
       all_goals try (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte, BitVec.toNat_ofNat]; done)
       all_goals cond_simp
       all_goals exact hn1_of _ _ _ (by assumption))

theorem Val.trich (v w : Val) (h1 : Val.eq v w = false) (h2 : Val.lt v w = false) : Val.lt w v = true := by
  cases v with
  | num n e => cases w with
    | num n' e' =>
      have h1' := of_decide_eq_false (by simpa [Val.eq] using h1)
      have h2' := of_decide_eq_false h2
      apply decide_eq_true
      simp only [align] at h1' h2' ⊢
      rw [Int.min_comm e' e]
      omega
    | inf s => cases s <;> simp_all [Val.lt]
  | inf s => cases w with
    | num _ _ => cases s <;> simp_all [Val.lt]
    | inf t => cases s <;> cases t <;> simp_all [Val.lt, Val.eq]

theorem Val.asym (v w : Val) (h : Val.lt v w = true) : Val.lt w v = false := by
  cases v with
  | num n e => cases w with
    | num n' e' =>
      have h' := of_decide_eq_true h
      apply decide_eq_false
      try simp only [align] at h' ⊢
      rw [Int.min_comm e' e]
      omega
    | inf s => cases s <;> simp_all [Val.lt]
  | inf s => cases w with
    | num _ _ => cases s <;> simp_all [Val.lt]
    | inf t => cases s <;> cases t <;> simp_all [Val.lt]

theorem jb_ge (x y : Nat) :
    (((isNaN binary64 x = true ∨ isNaN binary64 y = true) ∨ Janus.Arm64.FP.cmpN x y = true)) = (ge64 x y = false) := by
  unfold Janus.Arm64.FP.cmpN ge64
  have := Val.trich (valueOf binary64 x) (valueOf binary64 y)
  have := Val.asym (valueOf binary64 x) (valueOf binary64 y)
  cases isNaN binary64 x <;> cases isNaN binary64 y <;>
    cases he : Val.eq (valueOf binary64 x) (valueOf binary64 y) <;>
    cases hl : Val.lt (valueOf binary64 y) (valueOf binary64 x) <;>
    cases hl' : Val.lt (valueOf binary64 x) (valueOf binary64 y) <;> simp_all


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- From the join after Smith's algorithm (`e` in `X1`, `f` in `X6`): the recovery. -/
theorem fixup (S : State) (a b c d e f : Nat) (E F : Option Nat)
    (hpc : S.rip = BitVec.ofNat 64 (cdivAddr + 0x99)) (h : Inv S a b c d)
    (h1 : (S.xmm 1).toNat % 2 ^ 64 = e) (h6 : (S.xmm 6).toNat % 2 ^ 64 = f)
    (hE : ResultIs binary64 E e) (hF : ResultIs binary64 F f) (hnE : NoNaN E) (hnF : NoNaN F) :
    ReachesRet Extracted.program (retAddrOf S) S
      (Out S (recover false a b c d (E, F)).1 (recover false a b c d (E, F)).2) := by
  janus_eval_nat hcd : cdivAddr
  have hinv := h
  have hinf := h.env.inf
  obtain ⟨⟨hm, hra, hral, hsp, ⟨hi1, hi2, hi3⟩, hdl⟩, h0, h7, h2, h5, hr1, hr2⟩ := h
  have hel : e < 2 ^ 64 := h1 ▸ Nat.mod_lt _ (by decide)
  have hfl : f < 2 ^ 64 := h6 ▸ Nat.mod_lt _ (by decide)
  have hne := resultIs_nan_iff hE hnE
  have hnf := resultIs_nan_iff hF hnF
  cases E with
  | some x =>
    simp only [Option.isNone_some] at hne
    janus64_run [h1, h6, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, comis_cf, comis_pf, comis_zf,
      Janus.Arm64.FP.eq64_self, or_self, Bool.not_eq_true', tt, tt', hne, lo64, m64, Nat.mod_one]
    all_goals out_tac
    all_goals simp only [recover, setXmmF_apply, Nat.reduceEqDiff, reduceIte, BitVec.toNat_ofNat, Nat.reducePow,
      m128, m64, h1, h6, Nat.mod_eq_of_lt hel, Nat.mod_eq_of_lt hfl]
    · exact hE
    · exact hF
  | none =>
    cases F with
    | some y =>
      simp only [Option.isNone_some, Option.isNone_none] at hne hnf
      janus64_run [h1, h6, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, comis_cf, comis_pf, comis_zf,
        Janus.Arm64.FP.eq64_self, or_self, Bool.not_eq_true', tt, tt', hne, hnf, lo64, m64, Nat.mod_one]
      all_goals out_tac
      all_goals simp only [recover, setXmmF_apply, Nat.reduceEqDiff, reduceIte, BitVec.toNat_ofNat, Nat.reducePow,
        m128, m64, h1, h6, Nat.mod_eq_of_lt hel, Nat.mod_eq_of_lt hfl]
      · exact hE
      · exact hF
    | none =>
      simp only [Option.isNone_none] at hne hnf
      janus64_run [h1, h6, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, comis_cf, comis_pf, comis_zf,
        Janus.Arm64.FP.eq64_self, or_self, Bool.not_eq_true', tt, tt', hne, hnf, lo64, m64, Nat.mod_one]
        until [cdivAddr + 0xb2]
      all_goals refine out_mono (test1 _ a b c d e f ?_ ?_ ?_ ?_ hne hnf) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · rw [hcd]; try rfl
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · env_tac hm hra hral hsp hinf hdl
        all_goals first | assumption | (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; assumption)
      all_goals first | assumption | (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; assumption)

/-- The return of `complex128div` with results `X`, `Y`, as an equation (the shape a caller's
symbolic execution uses): back at the return address with `RSP + 8`, `RBP`, `R14`, memory,
`ymmHi`, `fsBase` and `DF` kept; every other general register, the flags, the `XMM` registers `v`
and `MXCSR` arbitrary, except `X0`, `X1`, which hold `X`, `Y`. -/
abbrev CRet (s s' : State) (X Y : Option Nat) : Prop :=
  ∃ (r : Nat → W64) (fl : Flags) (v : Nat → W128) (mx : BitVec 32),
    s' = { s with regs := Contracts.MapAmd64.keepABI s.regs r, flags := fl, xmm := v, mxcsr := mx,
                  rip := retAddrOf s } ∧ v 15 = s.xmm 15 ∧
    ResultIs binary64 X ((v 0).toNat % 2 ^ 64) ∧ ResultIs binary64 Y ((v 1).toNat % 2 ^ 64)

theorem out_cret {S : State} {X Y : Option Nat}
    (h : ReachesRet Extracted.program (retAddrOf S) S (Out S X Y))
    (hx87 : s'.x87 = s.x87 := by first | rfl | simp_all) (hfw : s'.fpucw = s.fpucw := by first | rfl | simp_all) :
    ReachesRet Extracted.program (retAddrOf S) S (fun s' => CRet S s' X Y) := by
  obtain ⟨k, s', hs, hpc, ⟨e4, e5, e14, em, ey, efs, edf, ex⟩, h9, h10⟩ := h
  refine ⟨k, s', hs, hpc, ⟨s'.regs, s'.flags, s'.xmm, s'.mxcsr, ?_, ex, h9, h10⟩⟩
  obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx, x8, fw⟩ := s'
  simp only at hpc e4 e5 e14 em ey efs edf hx87 hfw ⊢
  subst hpc em ey efs edf hx87 hfw
  congr
  funext i
  simp only [Contracts.MapAmd64.keepABI]
  split
  · rename_i hi; subst hi; exact e4
  · split
    · rename_i hi; rcases hi with rfl | rfl <;> simp [e5, e14]
    · rfl

theorem abs64 (x : Nat) : abs binary64 x = x % 9223372036854775808 := rfl

theorem sw64 (x : BitVec 128) : BitVec.setWidth 64 x = BitVec.ofNat 64 (x.toNat % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- **`runtime.complex128div`** (amd64, `GOAMD64=v1`, Go's `MXCSR` controls): from the call with
`n = a + bi` in `X0, X1` and `m = c + di` in `X2, X3` (low halves), it returns `cdiv false a b c d`
in `X0, X1`. -/
theorem cdiv_summary :
    Summary Extracted.program cdivAddr (fun s => Env s)
      (fun s s' => CRet s s'
        (cdiv false ((s.xmm 0).toNat % 2 ^ 64) ((s.xmm 1).toNat % 2 ^ 64) ((s.xmm 2).toNat % 2 ^ 64)
          ((s.xmm 3).toNat % 2 ^ 64)).1
        (cdiv false ((s.xmm 0).toNat % 2 ^ 64) ((s.xmm 1).toNat % 2 ^ 64) ((s.xmm 2).toNat % 2 ^ 64)
          ((s.xmm 3).toNat % 2 ^ 64)).2) := by
  intro s hpc h
  apply out_cret
  janus_eval_nat hcd : cdivAddr
  have hinf := h.inf
  obtain ⟨hm, hra, hral, hsp, ⟨hi1, hi2, hi3⟩, hdl⟩ := h
  generalize h0 : (s.xmm 0).toNat % 2 ^ 64 = a
  generalize h1 : (s.xmm 1).toNat % 2 ^ 64 = b
  generalize h2 : (s.xmm 2).toNat % 2 ^ 64 = c
  generalize h3 : (s.xmm 3).toNat % 2 ^ 64 = d
  have ha : a < 2 ^ 64 := h0 ▸ Nat.mod_lt _ (by decide)
  have hb : b < 2 ^ 64 := h1 ▸ Nat.mod_lt _ (by decide)
  have hc : c < 2 ^ 64 := h2 ▸ Nat.mod_lt _ (by decide)
  have hd : d < 2 ^ 64 := h3 ▸ Nat.mod_lt _ (by decide)
  janus64_run [h0, h1, h2, h3, sw64, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, comis_cf, comis_pf,
    comis_zf, lo64, btr63, m63', m63, m64, Nat.mod_one, jb_ge] until [cdivAddr + 0x99]
  all_goals refine out_mono (fixup _ a b c d _ _ (smith false a b c d).1 (smith false a b c d).2 ?_ ?_ rfl rfl ?_ ?_
    (smith_noNaN false a b c d).1 (smith_noNaN false a b c d).2) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  all_goals try (rw [hcd]; try rfl; done)
  all_goals try (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try env_tac hm hra hral hsp hinf hdl)
  all_goals try (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; assumption)
  all_goals try (dsimp only; simp only [setXmmF_apply, setRegF_apply, Nat.reduceEqDiff, reduceIte]; done)
  all_goals try simp only [Bool.not_eq_false, Bool.not_eq_true] at *
  all_goals try dsimp only
  all_goals simp only [smith, abs64, O.mac, O.msc, O.nms, reduceIte, Bool.false_eq_true, *,
    setXmmF_apply, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow, m128, m64, Nat.mod_mod, lo64, mod_div64,
    Nat.zero_mul, Nat.zero_add]
  all_goals try rw [O.mul2_comm (some a) (O.div2 (some d) (some c))]
  all_goals try rw [O.mul2_comm (some b) (O.div2 (some c) (some d))]
  all_goals first
    | exact x_div' (x_add' (x_mul' (Janus.Arm64.FP.r_some b) (x_div' (Janus.Arm64.FP.r_some d) (Janus.Arm64.FP.r_some c) hd hc) hb (by lt64)) (Janus.Arm64.FP.r_some a) (by lt64) ha)
        (x_add' (x_mul' (Janus.Arm64.FP.r_some d) (x_div' (Janus.Arm64.FP.r_some d) (Janus.Arm64.FP.r_some c) hd hc) hd (by lt64)) (Janus.Arm64.FP.r_some c) (by lt64) hc) (by lt64) (by lt64)
    | exact x_div' (x_sub' (Janus.Arm64.FP.r_some b) (x_mul' (x_div' (Janus.Arm64.FP.r_some d) (Janus.Arm64.FP.r_some c) hd hc) (Janus.Arm64.FP.r_some a) (by lt64) ha) hb (by lt64))
        (x_add' (x_mul' (Janus.Arm64.FP.r_some d) (x_div' (Janus.Arm64.FP.r_some d) (Janus.Arm64.FP.r_some c) hd hc) hd (by lt64)) (Janus.Arm64.FP.r_some c) (by lt64) hc) (by lt64) (by lt64)
    | exact x_div' (x_add' (x_mul' (Janus.Arm64.FP.r_some a) (x_div' (Janus.Arm64.FP.r_some c) (Janus.Arm64.FP.r_some d) hc hd) ha (by lt64)) (Janus.Arm64.FP.r_some b) (by lt64) hb)
        (x_add' (x_mul' (Janus.Arm64.FP.r_some c) (x_div' (Janus.Arm64.FP.r_some c) (Janus.Arm64.FP.r_some d) hc hd) hc (by lt64)) (Janus.Arm64.FP.r_some d) (by lt64) hd) (by lt64) (by lt64)
    | exact x_div' (x_sub' (x_mul' (x_div' (Janus.Arm64.FP.r_some c) (Janus.Arm64.FP.r_some d) hc hd) (Janus.Arm64.FP.r_some b) (by lt64) hb) (Janus.Arm64.FP.r_some a) (by lt64) ha)
        (x_add' (x_mul' (Janus.Arm64.FP.r_some c) (x_div' (Janus.Arm64.FP.r_some c) (Janus.Arm64.FP.r_some d) hc hd) hc (by lt64)) (Janus.Arm64.FP.r_some d) (by lt64) hd) (by lt64) (by lt64)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackGuardOK s 40 ∧ StackWritable s 48 8 ∧
        Janus.Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 48) 56 ∧ GoABI.GoMXCSR s ∧
        RuntimeInf s.mem infAddr ∧ Janus.Spec.Disjoint infAddr 8 ((s.regs 4).toNat - 48) 56 ∧
        Extracted.program.DataLoaded s.mem)
      (fun s s' =>
        ResultIs binary64 (cdiv false ((s.xmm 0).toNat % 2 ^ 64) ((s.xmm 1).toNat % 2 ^ 64)
          ((s.xmm 2).toNat % 2 ^ 64) ((s.xmm 3).toNat % 2 ^ 64)).1 ((s'.xmm 0).toNat % 2 ^ 64) ∧
        ResultIs binary64 (cdiv false ((s.xmm 0).toNat % 2 ^ 64) ((s.xmm 1).toNat % 2 ^ 64)
          ((s.xmm 2).toNat % 2 ^ 64) ((s.xmm 3).toNat % 2 ^ 64)).2 ((s'.xmm 1).toNat % 2 ^ 64)) := by
  intro ret hret s hs ⟨hg, ⟨hle, hnw, hacc⟩, hgd, hm, ⟨hi1, hi2, hi3⟩, hid, hdl⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  have ⟨ho1, ho2⟩ := one_loaded hdl
  have hseg : SegLoaded s.mem (Extracted.program.data[0]'(by decide)) := hdl _ (List.getElem_mem _)
  have hdj := hseg.disjoint_of_writable hacc
  have hlen : (Extracted.program.data[0]'(by decide)).bytes.length = 8 := by decide +kernel
  have hbase : (Extracted.program.data[0]'(by decide)).base = 4825504 := rfl
  rw [hlen, hbase] at hdj
  simp only [regSP, regG, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hacc hle hnw hgl hgb hnw2 hgr hgd hid hdj
  have hm' : s.mxcsr.toNat / 64 = 126 := hm
  janus64_run [GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm] calls [cdiv_summary]
  exact ⟨‹_›, ‹_›, ‹_›⟩

end Proof
