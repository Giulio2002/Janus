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

/-- The argument values of `k_fp(a, b, c)`. -/
def vals (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) : List Nat := [a.toNat, b.toNat, c.toNat]

/-- What `k_fp` needs (its callee contract's precondition): the arguments where the
classification puts them, `FPCR = 0`, a return address. -/
def SPre (vs : List Nat) (s : State) : Prop :=
  ArgsAt s sig.args vs sig.passing ∧ s.fpcr = 0 ∧ (s.regs 30).toNat % 4 = 0 ∧
    (s.regs 30).toNat < 2 ^ 56

theorem spre_iff (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) (s : State) :
    SPre (vals a b c) s ↔
      (s.vregs 0).toNat % 2 ^ 64 = a.toNat ∧ (s.vregs 1).toNat % 2 ^ 32 = b.toNat ∧
      (s.vregs 2).toNat % 2 ^ 64 = c.toNat ∧ s.fpcr = 0 ∧ (s.regs 30).toNat % 4 = 0 ∧
      (s.regs 30).toNat < 2 ^ 56 := by
  unfold SPre
  rw [passing]
  simp only [vals, sig, ArgsAt, ArgAt, PiecesAt, and_true, pieceAt_vec_d, pieceAt_vec_s, and_assoc]

/-- What it guarantees: the AAPCS64 callee-saved state, memory unchanged, the result in `D0`. -/
abbrev SPost (r : Nat) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 19 = s.regs 19 ∧ s'.regs 20 = s.regs 20 ∧ s'.regs 21 = s.regs 21 ∧
    s'.regs 22 = s.regs 22 ∧ s'.regs 23 = s.regs 23 ∧ s'.regs 24 = s.regs 24 ∧
    s'.regs 25 = s.regs 25 ∧ s'.regs 26 = s.regs 26 ∧ s'.regs 27 = s.regs 27 ∧
    s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.fpcr = s.fpcr ∧
    (s'.vregs 8).toNat % 2 ^ 64 = (s.vregs 8).toNat % 2 ^ 64 ∧
    (s'.vregs 9).toNat % 2 ^ 64 = (s.vregs 9).toNat % 2 ^ 64 ∧
    (s'.vregs 10).toNat % 2 ^ 64 = (s.vregs 10).toNat % 2 ^ 64 ∧
    (s'.vregs 11).toNat % 2 ^ 64 = (s.vregs 11).toNat % 2 ^ 64 ∧
    (s'.vregs 12).toNat % 2 ^ 64 = (s.vregs 12).toNat % 2 ^ 64 ∧
    (s'.vregs 13).toNat % 2 ^ 64 = (s.vregs 13).toNat % 2 ^ 64 ∧
    (s'.vregs 14).toNat % 2 ^ 64 = (s.vregs 14).toNat % 2 ^ 64 ∧
    (s'.vregs 15).toNat % 2 ^ 64 = (s.vregs 15).toNat % 2 ^ 64 ∧
    s'.mem = s.mem ∧ (s'.vregs 0).toNat % 2 ^ 64 = r

/-- The callee contract of `k_fp`. -/
theorem summary (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) :
    Summary Extracted.program Extracted.entry (SPre (vals a b c))
      (SPost ((mul 0 a b c).1 % 2 ^ 64)) := by
  intro s hpc hpre
  obtain ⟨h0, h1, h2, ht, hlra, hlrb⟩ := (spre_iff a b c s).1 hpre
  janus_run [h0, h1, h2, ht]
  simp only [SPost, setVReg_apply, ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow,
    mod64_mod128, Nat.mod_mod, mul, sub, cvt, true_and, ht]
  exact ⟨rfl, trivial⟩

/-- **`k_fp` under the C calling convention.** -/
theorem correctness (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) :
    CEnsuresR Extracted.program Extracted.entry sig (vals a b c)
      (fun s => s.fpcr = 0)
      (fun _ _ v => v = (mul 0 a b c).1 % 2 ^ 64) :=
  CEnsuresA.of_summary (summary a b c)
    (fun _ _ hret hs hf => ⟨hs.args, hf, hs.lr_ok hret⟩)
    (fun _ _ _ ⟨hsp, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hfc, v8, v9, v10, v11, v12,
        v13, v14, v15, _, h0⟩ =>
      ⟨⟨hsp, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hfc, v8, v9, v10, v11, v12, v13,
        v14, v15⟩, _, by
        simp only [Returned, sig, result, ResultAt, PiecesAt, and_true, PieceAt, bytesOf,
          Nat.pow_zero, Nat.div_one, Nat.reducePow] at h0 ⊢
        omega, rfl⟩)

end Proof
