import Extracted

/-!
# `double k_fp(double a, float b, double c)` (C, amd64): floating-point arguments and result

**Guarantee.** For all binary64 encodings `a`, `c` and binary32 `b`, every System V call of the
gcc-compiled `k_fp` whose arguments are where the classification of its prototype puts them
(`CCallA`: three SSE-class scalars, the low bytes of `XMM0`, `XMM1`, `XMM2`) and whose `MXCSR`
has the default control bits (round to nearest even, no `FTZ`/`DAZ`, all exceptions masked:
what Linux gives a process and Go keeps) returns, restores what System V requires (`CReturn`)
and returns in the low 64 bits of `XMM0` the bits of `(a - (double)b) * c` as the SSE
instructions compute them (`CVTSS2SD`, `SUBSD`, `MULSD` of the IEEE core, `Janus.Amd64.FP`).
The code is `cvtss2sd %xmm1,%xmm1; subsd %xmm1,%xmm0; mulsd %xmm2,%xmm0; ret`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.C Janus.Float

namespace Proof

def sig : SysV.Sig := ⟨some .double, [.double, .float, .double], none⟩

theorem passing : sig.passing =
    [.direct [⟨0, 8, .vec 0 0⟩], .direct [⟨0, 4, .vec 1 0⟩], .direct [⟨0, 8, .vec 2 0⟩]] := by
  decide

theorem result : SysV.result .double = .direct [⟨0, 8, .vec 0 0⟩] := by decide

/-- `(double)b`, `a - (double)b`, `(a - (double)b) * c` (round to nearest even, no FTZ/DAZ). -/
def cvt (b : BitVec 32) : Nat :=
  (FP.convert binary32 binary64 ⟨.rne, false, false⟩ b.toNat).res % 2 ^ 64
def sub (a : BitVec 64) (b : BitVec 32) : Nat :=
  (FP.binop .sub binary64 ⟨.rne, false, false⟩ a.toNat (cvt b)).res % 2 ^ 64
def mul (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) : Nat :=
  (FP.binop .mul binary64 ⟨.rne, false, false⟩ (sub a b) c.toNat).res % 2 ^ 64

theorem low64 (x y : Nat) :
    (x / 18446744073709551616 * 18446744073709551616 + y % 18446744073709551616) %
      18446744073709551616 = y % 18446744073709551616 := by omega

def vals (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) : List Nat := [a.toNat, b.toNat, c.toNat]

def SPre (vs : List Nat) (s : State) : Prop :=
  ArgsAt s sig.args vs sig.passing ∧ GoMXCSR s ∧ (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    s.df = false

theorem spre_iff (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) (s : State) :
    SPre (vals a b c) s ↔
      (s.xmm 0).toNat % 2 ^ 64 = a.toNat ∧ (s.xmm 1).toNat % 2 ^ 32 = b.toNat ∧
      (s.xmm 2).toNat % 2 ^ 64 = c.toNat ∧ GoMXCSR s ∧ (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
      s.df = false := by
  unfold SPre
  rw [passing]
  simp only [vals, sig, ArgsAt, ArgAt, PiecesAt, and_true, pieceAt_vec_d, pieceAt_vec_s, and_assoc]

abbrev SPost (r : Nat) (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 3 = s.regs 3 ∧ s'.regs 5 = s.regs 5 ∧
    s'.regs 12 = s.regs 12 ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧
    s'.regs 15 = s.regs 15 ∧ s'.df = false ∧ s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64 ∧
    s'.fpucw = s.fpucw ∧ s'.mem = s.mem ∧ (s'.xmm 0).toNat % 2 ^ 64 = r

theorem summary (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) :
    Summary Extracted.program Extracted.entry (SPre (vals a b c)) (SPost (mul a b c)) := by
  intro s hpc hpre
  obtain ⟨h0, h1, h2, hm, hsb, hsa, hra, hdf⟩ := (spre_iff a b c s).1 hpre
  janus64_run [h0, h1, h2, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  simp only [SPost, setRegF_apply, setXmmF_apply, ↓reduceIte, Nat.reduceEqDiff, true_and,
    BitVec.toNat_ofNat, low64, mul, sub, cvt, Nat.mod_mod, Nat.reducePow, mx_raise_div,
    GoMXCSR.mod hm]
  exact ⟨rfl, by omega⟩

/-- **`k_fp` under the System V calling convention.** -/
theorem correctness (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) :
    CEnsuresR Extracted.program Extracted.entry sig (vals a b c) (fun s => CStack s 0 8 ∧ GoMXCSR s)
      (fun _ _ v => v = mul a b c) :=
  CEnsuresA.of_summary (summary a b c)
    (fun _ s hret hs ⟨⟨_, _, hnw, hst⟩, hm⟩ => by
      simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add] at hnw hst
      exact ⟨hs.args, hm, hnw, Janus.Arm64.Memory.accessible_weaken _ hst, hs.ret_lt hret, hs.df⟩)
    (fun _ _ _ ⟨hsp, h3, h5, h12, h13, h14, h15, hdf, hmx, hfw, _, h0⟩ =>
      ⟨⟨hsp, h3, h5, h12, h13, h14, h15, hdf, hmx, hfw⟩, _, by
        simp only [Returned, sig, result, ResultAt, PiecesAt, and_true, PieceAt, bytesOf,
          Nat.pow_zero, Nat.div_one, Nat.reducePow] at h0 ⊢
        rw [h0, mul, Nat.mod_mod], rfl⟩)

end Proof
