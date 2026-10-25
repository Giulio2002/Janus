import Extracted

/-!
# `double k_fp(double a, float b, double c)` (C, arm64): floating-point arguments and result

**Guarantee.** For all binary64 encodings `a`, `c` and binary32 `b`, every AAPCS64 call of the
gcc-compiled `k_fp` whose arguments are where the classification of its prototype puts them
(`CCallA`: `a` in `D0`, `b` in `S1`, `c` in `D2` — the low bytes of `V0`, `V1`, `V2`) and whose
`FPCR` is 0 (Linux's initial value, which Go never changes: round to nearest even, no
flush-to-zero, no default NaN, no traps) returns, restores `SP`, `X19`–`X29`, `D8`–`D15` and
`FPCR` (`CReturn`), and returns in `D0` the bits of `(a - (double)b) * c` as the Arm
floating-point semantics computes them (`FPConvert`, `FPSub`, `FPMul` of the ASL:
`Janus.Arm64.FP`). The code is `fcvt d1, s1; fsub d0, d0, d1; fmul d0, d0, d2; ret`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.C Janus.Float

namespace Proof

def sig : AAPCS64.Sig := ⟨some .double, [.double, .float, .double], none⟩

theorem passing : sig.passing =
    [.direct [⟨0, 8, .vec 0 0⟩], .direct [⟨0, 4, .vec 1 0⟩], .direct [⟨0, 8, .vec 2 0⟩]] := by
  decide

theorem result : AAPCS64.result .double = .direct [⟨0, 8, .vec 0 0⟩] := by decide

/-- `(double)b`, `a - (double)b`, `(a - (double)b) * c` under `fpcr`. -/
def cvt (fpcr : Nat) (b : BitVec 32) := FP.fpConvert binary32 binary64 fpcr (FP.roundingMode fpcr) b.toNat
def sub (fpcr : Nat) (a : BitVec 64) (b : BitVec 32) :=
  FP.fpSub binary64 fpcr a.toNat ((cvt fpcr b).1 % 2 ^ 64)
def mul (fpcr : Nat) (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) :=
  FP.fpMul binary64 fpcr ((sub fpcr a b).1 % 2 ^ 64) c.toNat

/-- A 64-bit value in a 128-bit register. -/
theorem mod64_mod128 (x : Nat) :
    x % 18446744073709551616 % 340282366920938463463374607431768211456 = x % 18446744073709551616 := by
  omega

theorem correctness (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) :
    CEnsuresR Extracted.program Extracted.entry sig [a.toNat, b.toNat, c.toNat]
      (fun s => s.fpcr = 0)
      (fun _ _ v => v = (mul 0 a b c).1 % 2 ^ 64) := by
  intro ret hret s hs ht
  have hpc := hs.pc
  have hlr := hs.lr
  have ha := hs.args
  rw [passing] at ha
  simp only [sig, ArgsAt, ArgAt, PiecesAt, and_true, pieceAt_vec_d, pieceAt_vec_s] at ha
  obtain ⟨h0, h1, h2⟩ := ha
  simp only [Program.withExit] at hlr
  janus_run [h0, h1, h2, ht]
  refine ⟨_, ?_, rfl⟩
  simp only [Returned, sig, result, ResultAt, PiecesAt, and_true, PieceAt, bytesOf, setVReg_apply,
    ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.pow_zero, Nat.div_one, Nat.reducePow,
    mod64_mod128, Nat.mod_mod, mul, sub, cvt]

end Proof
