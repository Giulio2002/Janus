import Extracted

/-!
# `Div(n, m complex128) complex128`: complex division through `runtime.complex128div` (arm64)

```go
func Div(n, m complex128) complex128 { return n / m }
```

The compiler calls `runtime.complex128div` (`runtime/complex.go`): Smith's algorithm, then, when
both parts come out NaN, the infinity and zero recovery of C99 Annex G.5.1. Its machine code is
executed here, not assumed.

**Guarantee.** For every call with `n = a + bi` in `D0, D1` and `m = c + di` in `D2, D3`
(the binary64 encodings), `FPCR = 0` (round to nearest, no flush-to-zero, no default NaN, no
alternate half-precision, no traps), the stack-growth prologue falling through, 56 bytes of stack
writable and the word `runtime.inf` holding `+∞` (`RuntimeInf`, a stated hypothesis: the variable
is in `.noptrbss`, which the extractor does not copy), `Div` returns and its results are exactly
`cdiv true a b c d` (`Janus.Spec.Complex`): each part is the IEEE result of the algorithm, with the
`FMADD`/`FMSUB`/`FNMSUB` fusions the arm64 compiler emits, or a NaN where the specification has
none.

**How.** The function is cut at its joins: `cdiv_summary` runs Smith's algorithm (both branches of
`abs(c) >= abs(d)`) to the join, `fixup` the NaN tests of `e` and `f`, `test1`–`test3` the three
cases of the recovery and `body1`–`body3` their arithmetic. Every floating-point instruction is
related to the specification by the lifting lemmas of `Janus.Spec.ComplexMachine` (`r_div'`,
`r_fma'`, `r_mul'`, `r_neg`; `fcmp_flags` for `FCMP`), which are proved from the IEEE core.
`Div`'s own code then uses `cdiv_summary` as the callee summary.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Float Janus.Contracts.Misc Janus.Arm64.FP

namespace Proof

abbrev cdivAddr : Nat := segAddr Extracted.program "runtime.complex128div"

def infAddr : Nat :=
  adrpLdTarget (cdivAddr + 0x90) (segWord Extracted.program "runtime.complex128div" 36)
    (segWord Extracted.program "runtime.complex128div" 37) 3

theorem m64 (x : Nat) : x % 18446744073709551616 % 340282366920938463463374607431768211456 = x % 18446744073709551616 := by omega
/-- `Inv` at a later state of a block whose code left `D0`–`D3`, `X0`, `X1`, `X30`, `FPCR` and
memory alone. -/
macro "inv_tac" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | with_reducible assumption
    | (simp only [setVReg_apply, setReg_apply, Nat.reduceEqDiff, reduceIte]; with_reducible assumption)
    | (simp only [setVReg_apply, setReg_apply, Nat.reduceEqDiff, reduceIte]; done)
    | rfl))

/-- The final `Out` facts of a path that returns. -/
macro "out_tac" : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals try (first | rfl | decide | (simp only [setReg_apply]; done) | (simp only [setReg_apply, Nat.reduceEqDiff, reduceIte]; done))))

theorem one64 : vfpExpandImm binary64 112 % 340282366920938463463374607431768211456 = 4607182418800017408 := by
  decide

/-- The bound side conditions of the lifting lemmas. -/
macro "lt64" : tactic => `(tactic| first | with_reducible assumption | exact Nat.mod_lt _ (by decide) | exact copysign_lt _ _ | exact fpNeg_lt _ | decide)

theorem m128 (x : Nat) : x % 340282366920938463463374607431768211456 % 18446744073709551616 = x % 18446744073709551616 :=
  Nat.mod_mod_of_dvd x (by decide)

theorem m63 (x : Nat) : x % 9223372036854775808 % 340282366920938463463374607431768211456 = x % 9223372036854775808 := by omega

/-- What every block of `complex128div` keeps: `FPCR = 0`, the operands in `D0`–`D3` and the
bits of `c`, `d` in `X0`, `X1`, `runtime.inf`, and a return address. -/
structure Inv (S : State) (a b c d : Nat) : Prop where
  fpcr : S.fpcr = 0
  v0 : (S.vregs 0).toNat % 2 ^ 64 = a
  v1 : (S.vregs 1).toNat % 2 ^ 64 = b
  v2 : (S.vregs 2).toNat % 2 ^ 64 = c
  v3 : (S.vregs 3).toNat % 2 ^ 64 = d
  r0 : S.regs 0 = BitVec.ofNat 64 c
  r1 : S.regs 1 = BitVec.ofNat 64 d
  ret : (S.regs 30).toNat < 2 ^ 48
  al : (S.regs 30).toNat % 4 = 0
  inf : RuntimeInf S.mem infAddr

/-- The return of `complex128div` from `S` with results `X` (`D0`) and `Y` (`D1`). -/
def Out (S : State) (X Y : Option Nat) (s' : State) : Prop :=
  (s'.sp = S.sp ∧ s'.mem = S.mem ∧ s'.regs 18 = S.regs 18 ∧ s'.regs 28 = S.regs 28 ∧
    s'.regs 29 = S.regs 29 ∧ s'.fpcr = 0 ∧ s'.tpidr = S.tpidr ∧ s'.dczid = S.dczid ∧
    s'.excl = S.excl ∧ s'.exclPass = S.exclPass) ∧
  ResultIs binary64 X ((s'.vregs 0).toNat % 2 ^ 64) ∧ ResultIs binary64 Y ((s'.vregs 1).toNat % 2 ^ 64)

set_option maxHeartbeats 0 in
/-- `m == 0` and a number in the numerator: `copysign(inf, c) * a`, `copysign(inf, c) * b`. -/
theorem body1 (S : State) (a b c d : Nat) (hpc : S.pc = BitVec.ofNat 64 (cdivAddr + 0x90))
    (h : Inv S a b c d) :
    ReachesRet Extracted.program (S.regs 30) S
      (Out S (O.mul2 (some (copysign infE c)) (some a)) (O.mul2 (some (copysign infE c)) (some b))) := by
  obtain ⟨hf, h0, h1, h2, h3, hr0, hr1, hret, hal, hi1, hi2, hi3⟩ := h
  janus_eval_nat hI : infAddr
  rw [hI] at hi1 hi2 hi3
  have ha : a < 2 ^ 64 := h0 ▸ Nat.mod_lt _ (by decide)
  have hb : b < 2 ^ 64 := h1 ▸ Nat.mod_lt _ (by decide)
  have hc : c < 2 ^ 64 := h2 ▸ Nat.mod_lt _ (by decide)
  janus_run [h0, h1, h2, h3, hr0, hr1, hf, hi3, fcmp_flags, eq64_self, m64, m63, copysign_or, copysign_or']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals try (first | rfl | (simp only [setReg_apply]; done) | simp [hf])
  all_goals simp only [setVReg_apply, BitVec.toNat_ofNat, m64, Nat.mod_mod, infBits, reduceIte,
    Nat.reduceEqDiff, Nat.reduceMod, copysign_mod, Nat.reducePow, infE]
  all_goals try simp only [m64, Nat.mod_mod]
  all_goals rw [O.mul2_comm]
  · exact r_mul' (r_some _) (r_some _) ha (copysign_lt _ _)
  · exact r_mul' (r_some _) (r_some _) hb (copysign_lt _ _)

set_option maxHeartbeats 0 in
/-- An infinite denominator over a finite numerator: zeros. -/
theorem body3 (S : State) (a b c d : Nat) (hpc : S.pc = BitVec.ofNat 64 (cdivAddr + 0x150))
    (h : Inv S a b c d) :
    ReachesRet Extracted.program (S.regs 30) S
      (Out S (O.mul2 (some 0) (O.mac true (some b) (some (inf2one d)) (O.mul2 (some a) (some (inf2one c)))))
        (O.mul2 (some 0) (O.msc true (some a) (some (inf2one d)) (O.mul2 (some b) (some (inf2one c)))))) := by
  obtain ⟨hf, h0, h1, h2, h3, hr0, hr1, hret, hal, hi1, hi2, hi3⟩ := h
  have ha : a < 2 ^ 64 := h0 ▸ Nat.mod_lt _ (by decide)
  have hb : b < 2 ^ 64 := h1 ▸ Nat.mod_lt _ (by decide)
  have hc : c < 2 ^ 64 := h2 ▸ Nat.mod_lt _ (by decide)
  have hd : d < 2 ^ 64 := h3 ▸ Nat.mod_lt _ (by decide)
  janus_run [h0, h1, h2, h3, hr0, hr1, hf, fcmp_flags, eq64_self, m64, m63, copysign_or, copysign_or',
    isNaN_fpSub_self c hc, isNaN_fpSub_self d hd]
  all_goals refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals try (first | rfl | (simp only [setReg_apply]; done) | simp [hf])
  all_goals simp only [setVReg_apply, BitVec.toNat_ofNat, m64, Nat.mod_mod, reduceIte,
    Nat.reduceEqDiff, Nat.reduceMod, copysign_mod, Nat.reducePow, infE]
  all_goals try simp only [m64, Nat.mod_mod]
  all_goals try simp only [Bool.not_eq_true] at *
  all_goals simp only [inf2one, isInf64, isNaN64, O.mac, O.msc, one64, reduceIte, *, Bool.not_true,
    Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, ite_false, ite_true,
    Bool.false_eq_true, copysign_zero]
  all_goals first
    | exact r_mul' (r_some 0) (r_fma' (r_some _) (r_some _)
        (r_mul' (r_some _) (r_some _) (by lt64) (by lt64)) (by lt64) (by lt64) (by lt64)) (by lt64) (by lt64)
    | exact r_mul' (r_some 0) (r_fma' (r_neg (r_some _)) (r_some _)
        (r_mul' (r_some _) (r_some _) (by lt64) (by lt64)) (fpNeg_lt _) (by lt64) (by lt64)) (by lt64) (by lt64)

set_option maxHeartbeats 0 in
/-- An infinite numerator over a finite denominator: infinities (in the operand order of the code). -/
theorem body2 (S : State) (a b c d : Nat) (hpc : S.pc = BitVec.ofNat 64 (cdivAddr + 0x1e8))
    (h : Inv S a b c d) :
    ReachesRet Extracted.program (S.regs 30) S
      (Out S (O.mul2 (O.fma3 (some d) (some (inf2one b)) (O.mul2 (some c) (some (inf2one a)))) (some infE))
        (O.mul2 (O.fma3 (O.neg (some d)) (some (inf2one a)) (O.mul2 (some c) (some (inf2one b)))) (some infE))) := by
  obtain ⟨hf, h0, h1, h2, h3, hr0, hr1, hret, hal, hi1, hi2, hi3⟩ := h
  janus_eval_nat hI : infAddr
  rw [hI] at hi1 hi2 hi3
  have ha : a < 2 ^ 64 := h0 ▸ Nat.mod_lt _ (by decide)
  have hb : b < 2 ^ 64 := h1 ▸ Nat.mod_lt _ (by decide)
  have hc : c < 2 ^ 64 := h2 ▸ Nat.mod_lt _ (by decide)
  have hd : d < 2 ^ 64 := h3 ▸ Nat.mod_lt _ (by decide)
  janus_run [h0, h1, h2, h3, hr0, hr1, hf, fcmp_flags, eq64_self, m64, m63, copysign_or, copysign_or',
    isNaN_fpSub_self a ha, isNaN_fpSub_self b hb, hi3]
  all_goals refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals try (first | rfl | (simp only [setReg_apply]; done) | simp [hf])
  all_goals simp only [setVReg_apply, BitVec.toNat_ofNat, m64, Nat.mod_mod, reduceIte,
    Nat.reduceEqDiff, Nat.reduceMod, copysign_mod, Nat.reducePow, infE]
  all_goals try simp only [m64, Nat.mod_mod]
  all_goals try simp only [Bool.not_eq_true] at *
  all_goals simp only [inf2one, isInf64, isNaN64, O.mac, O.msc, one64, reduceIte, *, Bool.not_true,
    Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, ite_false, ite_true,
    Bool.false_eq_true, copysign_zero]
  all_goals first
    | exact r_mul' (r_fma' (r_some _) (r_some _)
        (r_mul' (r_some _) (r_some _) (by lt64) (by lt64)) (by lt64) (by lt64) (by lt64)) (r_some _) (by lt64) (by lt64)
    | exact r_mul' (r_fma' (r_neg (r_some _)) (r_some _)
        (r_mul' (r_some _) (r_some _) (by lt64) (by lt64)) (fpNeg_lt _) (by lt64) (by lt64)) (r_some _) (by lt64) (by lt64)

/-- `Out` from a later state of the same run (same `SP`, memory, `X18`/`X28`/`X29`, `FPCR`,
`TPIDR`, `DCZID`), with the results rewritten. -/
theorem out_mono {S S' : State} {X Y X' Y' : Option Nat} {r : W64}
    (h : ReachesRet Extracted.program r S' (Out S' X Y)) (hX : X = X') (hY : Y = Y')
    (hsp : S'.sp = S.sp) (hm : S'.mem = S.mem) (h18 : S'.regs 18 = S.regs 18)
    (h28 : S'.regs 28 = S.regs 28) (h29 : S'.regs 29 = S.regs 29)
    (htp : S'.tpidr = S.tpidr) (hdz : S'.dczid = S.dczid)
    (hex : S'.excl = S.excl := by first | rfl | simp_all)
    (hep : S'.exclPass = S.exclPass := by first | rfl | simp_all) :
    ReachesRet Extracted.program r S' (Out S X' Y') := by
  subst hX hY
  obtain ⟨k, s', hs, hpc, ⟨h1, h2, h3, h4, h5, h6, h7, h8, e1, e2⟩, h9, h10⟩ := h
  exact ⟨k, s', hs, hpc, ⟨h1.trans hsp, h2.trans hm, h3.trans h18, h4.trans h28, h5.trans h29,
    h6, h7.trans htp, h8.trans hdz, e1.trans hex, e2.trans hep⟩, h9, h10⟩

set_option maxHeartbeats 0 in
/-- The third case of the recovery (`(isInf(c) || isInf(d)) && isFinite(a) && isFinite(b)`), and
the fall-through that keeps Smith's two NaNs. -/
theorem test3 (S : State) (a b c d e f : Nat) (hpc : S.pc = BitVec.ofNat 64 (cdivAddr + 0x110))
    (h : Inv S a b c d) (h6 : (S.vregs 6).toNat % 2 ^ 64 = e) (h4 : (S.vregs 4).toNat % 2 ^ 64 = f)
    (he : isNaN binary64 e = true) (hf' : isNaN binary64 f = true)
    (hn1 : (isZero64 c && isZero64 d && (!isNaN64 a || !isNaN64 b)) = false)
    (hn2 : ((isInf64 a || isInf64 b) && isFinite64 c && isFinite64 d) = false) :
    ReachesRet Extracted.program (S.regs 30) S
      (Out S (recover true a b c d (none, none)).1 (recover true a b c d (none, none)).2) := by
  janus_eval_nat hcd : cdivAddr
  have hinf := h.inf
  have hel : e < 2 ^ 64 := h6 ▸ Nat.mod_lt _ (by decide)
  have hfl : f < 2 ^ 64 := h4 ▸ Nat.mod_lt _ (by decide)
  obtain ⟨hf, h0, h1, h2, h3, hr0, hr1, hret, hal, hi1, hi2, hi3⟩ := h
  have ha : a < 2 ^ 64 := h0 ▸ Nat.mod_lt _ (by decide)
  have hb : b < 2 ^ 64 := h1 ▸ Nat.mod_lt _ (by decide)
  have hc : c < 2 ^ 64 := h2 ▸ Nat.mod_lt _ (by decide)
  have hd : d < 2 ^ 64 := h3 ▸ Nat.mod_lt _ (by decide)
  janus_run [h0, h1, h2, h3, h6, h4, hr0, hr1, hf, fcmp_flags, eq64_self, m64, m63,
    isNaN_fpSub_self a ha, isNaN_fpSub_self b hb, isNaN_fpSub_self c hc, isNaN_fpSub_self d hd]
    until [cdivAddr + 0x150]
  all_goals try simp only [Bool.not_eq_true] at *
  all_goals try (
       out_tac
       all_goals simp only [recover, hn1, hn2]
       all_goals simp only [isInf64, isNaN64, *, Bool.not_true, Bool.not_false,
         Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.or_true, Bool.true_or,
         Bool.false_or, Bool.or_false, ite_false, ite_true, Bool.false_eq_true, reduceIte, ResultIs,
         setVReg_apply, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.mod_mod, m64]
       all_goals simp only [Nat.reducePow, m64, m128, Nat.mod_eq_of_lt hel, Nat.mod_eq_of_lt hfl, he, hf']
       done)
  all_goals refine out_mono (body3 _ a b c d ?_ ?_) ?_ ?_ rfl rfl rfl rfl rfl rfl rfl
  all_goals try (rw [hcd]; rfl)
  all_goals try inv_tac
  all_goals simp only [recover, hn1, hn2]
  all_goals simp only [isInf64, isNaN64, *, Bool.not_true, Bool.not_false,
    Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.or_true, Bool.true_or,
    Bool.false_or, Bool.or_false, ite_false, ite_true, Bool.false_eq_true, reduceIte]

set_option maxHeartbeats 0 in
/-- The second case of the recovery (`(isInf(a) || isInf(b)) && isFinite(c) && isFinite(d)`). -/
theorem test2 (S : State) (a b c d e f : Nat) (hpc : S.pc = BitVec.ofNat 64 (cdivAddr + 0xd0))
    (h : Inv S a b c d) (h6 : (S.vregs 6).toNat % 2 ^ 64 = e) (h4 : (S.vregs 4).toNat % 2 ^ 64 = f)
    (he : isNaN binary64 e = true) (hf' : isNaN binary64 f = true)
    (hn1 : (isZero64 c && isZero64 d && (!isNaN64 a || !isNaN64 b)) = false)
 :
    ReachesRet Extracted.program (S.regs 30) S
      (Out S (recover true a b c d (none, none)).1 (recover true a b c d (none, none)).2) := by
  janus_eval_nat hcd : cdivAddr
  have hinf := h.inf
  have hel : e < 2 ^ 64 := h6 ▸ Nat.mod_lt _ (by decide)
  have hfl : f < 2 ^ 64 := h4 ▸ Nat.mod_lt _ (by decide)
  obtain ⟨hf, h0, h1, h2, h3, hr0, hr1, hret, hal, hi1, hi2, hi3⟩ := h
  have ha : a < 2 ^ 64 := h0 ▸ Nat.mod_lt _ (by decide)
  have hb : b < 2 ^ 64 := h1 ▸ Nat.mod_lt _ (by decide)
  have hc : c < 2 ^ 64 := h2 ▸ Nat.mod_lt _ (by decide)
  have hd : d < 2 ^ 64 := h3 ▸ Nat.mod_lt _ (by decide)
  janus_run [h0, h1, h2, h3, h6, h4, hr0, hr1, hf, fcmp_flags, eq64_self, m64, m63,
    isNaN_fpSub_self a ha, isNaN_fpSub_self b hb, isNaN_fpSub_self c hc, isNaN_fpSub_self d hd]
    until [cdivAddr + 0x110, cdivAddr + 0x1e8]
  all_goals try simp only [Bool.not_eq_true] at *
  all_goals try simp only [Bool.not_eq_true] at *
  all_goals first
    | (refine out_mono (body2 _ a b c d ?_ ?_) ?_ ?_ rfl rfl rfl rfl rfl rfl rfl
       · (rw [hcd]; try rfl)
       · inv_tac
       all_goals simp only [recover, hn1]
       all_goals simp only [isInf64, isNaN64, *, Bool.not_true, Bool.not_false,
         Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.or_true, Bool.true_or,
         Bool.false_or, Bool.or_false, ite_false, ite_true, Bool.false_eq_true, reduceIte]
       all_goals simp only [O.mac, O.msc, reduceIte]
       all_goals try rw [O.mul2_comm (some infE), O.fma3_comm (some (inf2one b)), O.mul2_comm (some (inf2one a))]
       all_goals try rw [O.mul2_comm (some infE), O.fma3_negswap (some (inf2one a)), O.mul2_comm (some (inf2one b))]
       done)
    | (refine out_mono (test3 _ a b c d e f ?_ ?_ ?_ ?_ he hf' hn1 ?_) rfl rfl rfl rfl rfl rfl rfl rfl rfl
       · (rw [hcd]; try rfl)
       · inv_tac
       · first | with_reducible assumption | (simp only [setVReg_apply, Nat.reduceEqDiff, reduceIte]; with_reducible assumption)
       · first | with_reducible assumption | (simp only [setVReg_apply, Nat.reduceEqDiff, reduceIte]; with_reducible assumption)
       · simp only [isInf64, isNaN64, *, Bool.not_true, Bool.not_false,
         Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.or_true, Bool.true_or,
         Bool.false_or, Bool.or_false, ite_false, ite_true, Bool.false_eq_true, reduceIte])

set_option maxHeartbeats 0 in
/-- The first case of the recovery (`m == 0 && (!isNaN(a) || !isNaN(b))`). -/
theorem test1 (S : State) (a b c d e f : Nat) (hpc : S.pc = BitVec.ofNat 64 (cdivAddr + 0x68))
    (h : Inv S a b c d) (h6 : (S.vregs 6).toNat % 2 ^ 64 = e) (h4 : (S.vregs 4).toNat % 2 ^ 64 = f)
    (he : isNaN binary64 e = true) (hf' : isNaN binary64 f = true) :
    ReachesRet Extracted.program (S.regs 30) S
      (Out S (recover true a b c d (none, none)).1 (recover true a b c d (none, none)).2) := by
  janus_eval_nat hcd : cdivAddr
  have hinf := h.inf
  obtain ⟨hf, h0, h1, h2, h3, hr0, hr1, hret, hal, hi1, hi2, hi3⟩ := h
  janus_run [h0, h1, h2, h3, h6, h4, hr0, hr1, hf, fcmp_flags, eq64_self, m64, m63, cset_and]
    until [cdivAddr + 0x90, cdivAddr + 0xd0]
  all_goals try simp only [Bool.not_eq_true, Bool.not_eq_false, Bool.and_eq_true] at *
  all_goals first
    | (refine out_mono (body1 _ a b c d ?_ ?_) ?_ ?_ rfl rfl rfl rfl rfl rfl rfl
       · (rw [hcd]; try rfl)
       · inv_tac
       all_goals simp only [recover, isZero64, isNaN64, *, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.or_true, Bool.true_or, Bool.false_or, Bool.or_false, ite_false, ite_true, Bool.false_eq_true, reduceIte]
       done)
    | (refine out_mono (test2 _ a b c d e f ?_ ?_ ?_ ?_ he hf' ?_) rfl rfl rfl rfl rfl rfl rfl rfl rfl
       · (rw [hcd]; try rfl)
       · inv_tac
       · first | with_reducible assumption | (simp only [setVReg_apply, Nat.reduceEqDiff, reduceIte]; with_reducible assumption)
       · first | with_reducible assumption | (simp only [setVReg_apply, Nat.reduceEqDiff, reduceIte]; with_reducible assumption)
       · simp only [isZero64, isNaN64, *, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.or_true, Bool.true_or, Bool.false_or, Bool.or_false, ite_false, ite_true, Bool.false_eq_true, reduceIte])

set_option maxHeartbeats 0 in
/-- From the join after Smith's algorithm (`e` in `D6`, `f` in `D4`): the recovery. -/
theorem fixup (S : State) (a b c d e f : Nat) (E F : Option Nat)
    (hpc : S.pc = BitVec.ofNat 64 (cdivAddr + 0x58)) (h : Inv S a b c d)
    (h6 : (S.vregs 6).toNat % 2 ^ 64 = e) (h4 : (S.vregs 4).toNat % 2 ^ 64 = f)
    (hE : ResultIs binary64 E e) (hF : ResultIs binary64 F f) (hnE : NoNaN E) (hnF : NoNaN F) :
    ReachesRet Extracted.program (S.regs 30) S
      (Out S (recover true a b c d (E, F)).1 (recover true a b c d (E, F)).2) := by
  janus_eval_nat hcd : cdivAddr
  have hinv := h
  have hinf := h.inf
  obtain ⟨hf, h0, h1, h2, h3, hr0, hr1, hret, hal, hi1, hi2, hi3⟩ := h
  have hel : e < 2 ^ 64 := h6 ▸ Nat.mod_lt _ (by decide)
  have hfl : f < 2 ^ 64 := h4 ▸ Nat.mod_lt _ (by decide)
  have hne := resultIs_nan_iff hE hnE
  have hnf := resultIs_nan_iff hF hnF
  cases E with
  | some x =>
    simp only [Option.isNone_some] at hne
    janus_run [h0, h1, h2, h3, h6, h4, hr0, hr1, hf, fcmp_flags, eq64_self, m64, m63, hne]
    out_tac
    all_goals simp only [recover, setVReg_apply, Nat.reduceEqDiff, reduceIte, BitVec.toNat_ofNat, Nat.reducePow,
      m128, Nat.mod_eq_of_lt hel, Nat.mod_eq_of_lt hfl]
    · exact hE
    · exact hF
  | none =>
    cases F with
    | some y =>
      simp only [Option.isNone_some, Option.isNone_none] at hne hnf
      janus_run [h0, h1, h2, h3, h6, h4, hr0, hr1, hf, fcmp_flags, eq64_self, m64, m63, hne, hnf]
      out_tac
      all_goals simp only [recover, setVReg_apply, Nat.reduceEqDiff, reduceIte, BitVec.toNat_ofNat,
        Nat.reducePow, m128, Nat.mod_eq_of_lt hel, Nat.mod_eq_of_lt hfl]
      · exact hE
      · exact hF
    | none =>
      simp only [Option.isNone_none] at hne hnf
      janus_run [h0, h1, h2, h3, h6, h4, hr0, hr1, hf, fcmp_flags, eq64_self, m64, m63, hne, hnf]
        until [cdivAddr + 0x68]
      refine out_mono (test1 _ a b c d e f ?_ ?_ h6 h4 hne hnf) rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · rw [hcd]; try rfl
      · inv_tac

/-- The return of `complex128div` with results `X`, `Y`, as an equation (the shape a caller's
symbolic execution uses): back at `X30` with `SP`, memory, `X18`, `X28`, `X29`, `FPCR`, `TPIDR_EL0`
and `DCZID` kept; every other general register, the flags, the SIMD&FP registers `v` and `FPSR`
arbitrary, except `D0`, `D1`, which hold `X`, `Y`. -/
abbrev CRet (s s' : State) (X Y : Option Nat) : Prop :=
  ∃ (r : Nat → W64) (fl : Flags) (v : Nat → BitVec 128) (fs : BitVec 32),
    s' = { s with regs := Contracts.Map.keepABI s.regs r, flags := fl, vregs := v, fpsr := fs, pc := s.regs 30 } ∧
    ResultIs binary64 X ((v 0).toNat % 2 ^ 64) ∧ ResultIs binary64 Y ((v 1).toNat % 2 ^ 64)

theorem out_cret {S : State} {X Y : Option Nat} (hf : S.fpcr = 0)
    (h : ReachesRet Extracted.program (S.regs 30) S (Out S X Y)) :
    ReachesRet Extracted.program (S.regs 30) S (fun s' => CRet S s' X Y) := by
  obtain ⟨k, s', hs, hpc, ⟨h1, h2, h3, h4, h5, h6, h7, h8, hex, hep⟩, h9, h10⟩ := h
  refine ⟨k, s', hs, hpc, ⟨s'.regs, s'.flags, s'.vregs, s'.fpsr, ?_, h9, h10⟩⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs, ex, ep⟩ := s'
  simp only at hpc h1 h2 h3 h4 h5 h6 h7 h8 hex hep ⊢
  subst hpc h1 h2 h7 h8 hex hep
  rw [h6, ← hf]
  congr
  funext i
  simp only [Contracts.Map.keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h3, h4, h5]
  · rfl

theorem abs64 (x : Nat) : abs binary64 x = x % 9223372036854775808 := rfl

set_option maxHeartbeats 0 in
/-- **`runtime.complex128div`** (arm64, `FPCR = 0`): from the call with `n = a + bi` in `D0, D1`
and `m = c + di` in `D2, D3`, it returns `cdiv true a b c d` in `D0, D1` (the encodings, or a NaN
where the specification has none), with `SP`, memory, `X18`, `X28`, `X29`, `FPCR`, `TPIDR_EL0`
and `DCZID` unchanged. -/
theorem cdiv_summary :
    Summary Extracted.program cdivAddr
      (fun s => s.fpcr = 0 ∧ RuntimeInf s.mem infAddr ∧ (s.regs 30).toNat < 2 ^ 48 ∧
        (s.regs 30).toNat % 4 = 0)
      (fun s s' => CRet s s' (cdiv true (s.getV 0 64) (s.getV 1 64) (s.getV 2 64) (s.getV 3 64)).1
        (cdiv true (s.getV 0 64) (s.getV 1 64) (s.getV 2 64) (s.getV 3 64)).2) := by
  intro s hpc ⟨hf, hinf, hret, hal⟩
  apply out_cret hf
  janus_eval_nat hcd : cdivAddr
  simp only [State.getV]
  generalize h0 : (s.vregs 0).toNat % 2 ^ 64 = a
  generalize h1 : (s.vregs 1).toNat % 2 ^ 64 = b
  generalize h2 : (s.vregs 2).toNat % 2 ^ 64 = c
  generalize h3 : (s.vregs 3).toNat % 2 ^ 64 = d
  have ha : a < 2 ^ 64 := h0 ▸ Nat.mod_lt _ (by decide)
  have hb : b < 2 ^ 64 := h1 ▸ Nat.mod_lt _ (by decide)
  have hc : c < 2 ^ 64 := h2 ▸ Nat.mod_lt _ (by decide)
  have hd : d < 2 ^ 64 := h3 ▸ Nat.mod_lt _ (by decide)
  janus_run [h0, h1, h2, h3, hf, fcmp_flags, m64, m63] until [cdivAddr + 0x58]
  all_goals refine out_mono (fixup _ a b c d _ _ (smith true a b c d).1 (smith true a b c d).2 ?_ ?_ rfl rfl ?_ ?_
    (smith_noNaN true a b c d).1 (smith_noNaN true a b c d).2) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  all_goals try (rw [hcd]; try rfl; done)
  all_goals try inv_tac
  all_goals try rw [hi_ge] at *
  all_goals simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.not_eq_false, Bool.not_true,
    Bool.not_false] at *
  all_goals simp only [smith, abs64, O.mac, O.msc, O.nms, reduceIte, Bool.false_eq_true, *,
    setVReg_apply, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow, m128, m64, Nat.mod_mod]
  all_goals first
    | exact r_div' (r_fma' (r_some b) (r_div' (r_some d) (r_some c) hd hc) (r_some a) (by lt64) (by lt64) (by lt64))
        (r_fma' (r_some d) (r_div' (r_some d) (r_some c) hd hc) (r_some c) (by lt64) (by lt64) (by lt64)) (by lt64) (by lt64)
    | exact r_div' (r_fma' (r_neg (r_some a)) (r_div' (r_some d) (r_some c) hd hc) (r_some b) (by lt64) (by lt64) (by lt64))
        (r_fma' (r_some d) (r_div' (r_some d) (r_some c) hd hc) (r_some c) (by lt64) (by lt64) (by lt64)) (by lt64) (by lt64)
    | exact r_div' (r_fma' (r_some a) (r_div' (r_some c) (r_some d) hc hd) (r_some b) (by lt64) (by lt64) (by lt64))
        (r_fma' (r_some c) (r_div' (r_some c) (r_some d) hc hd) (r_some d) (by lt64) (by lt64) (by lt64)) (by lt64) (by lt64)
    | exact r_div' (r_fma' (r_some b) (r_div' (r_some c) (r_some d) hc hd) (r_neg (r_some a)) (by lt64) (by lt64) (by lt64))
        (r_fma' (r_some c) (r_div' (r_some c) (r_some d) hc hd) (r_some d) (by lt64) (by lt64) (by lt64)) (by lt64) (by lt64)


set_option maxHeartbeats 0 in
theorem correctness :
    Ensures Extracted.program Extracted.entry []
      (fun s => GuardOK s 0 ∧ StackOK s 56 0 ∧ Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 56) 56 ∧
        s.fpcr = 0 ∧ RuntimeInf s.mem infAddr ∧ Disjoint infAddr 8 (s.sp.toNat - 56) 56)
      (fun s s' =>
        ResultIs binary64 (cdiv true (s.getV 0 64) (s.getV 1 64) (s.getV 2 64) (s.getV 3 64)).1 (s'.getV 0 64) ∧
        ResultIs binary64 (cdiv true (s.getV 0 64) (s.getV 1 64) (s.getV 2 64) (s.getV 3 64)).2 (s'.getV 1 64)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgd, hf, ⟨hi1, hi2, hi3⟩, hid⟩
  janus_intro hs
  simp only [Disjoint] at hgd hid
  janus_eval_nat hI : infAddr
  have hj1 := hi1; have hj2 := hi2; have hj3 := hi3
  rw [hI] at hi1 hi2 hi3 hid
  janus_run [hf] calls [cdiv_summary]
  simp only [State.getV] at *
  exact ⟨‹_›, ‹_›⟩

end Proof
