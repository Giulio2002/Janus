import Extracted

/-!
# `struct k_mix k_pmix(struct k_pt a, struct k_pt b, int64_t n)` (C, arm64): structs by value

```c
struct k_pt { double x, y; };           // an HFA of two doubles
struct k_mix { double s; int64_t n; };  // 16 bytes, not an HFA
struct k_mix k_pmix(struct k_pt a, struct k_pt b, int64_t n) {
	struct k_mix r = { (a.x + b.x) * (a.y - b.y), n + 1 };
	return r;
}
```

**Guarantee.** For all binary64 encodings `ax ay bx by` and 64-bit `n`, every AAPCS64 call of
the gcc-compiled `k_pmix` whose arguments are where the classification of its prototype puts
them (`CCallA`: the homogeneous floating-point aggregates `a` and `b` one member per register
in `D0`, `D1` and `D2`, `D3` — rules C.2 — and `n` in `X0`) with `FPCR = 0` returns, restores
what AAPCS64 requires (`CReturn`), and returns the 16-byte struct where the classification of
the result puts it — not an HFA and at most 16 bytes, so in `X0` (the bits of `s`) and `X1`
(`n`) — with `s` the bits of `(ax + bx) * (ay - by)` of the Arm floating-point semantics and
`n + 1` mod 2^64.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.C Janus.Float

namespace Proof

def pt : CType := .struct [.double, .double]
def mix : CType := .struct [.double, .int 8 true]
def sig : AAPCS64.Sig := ⟨some mix, [pt, pt, .int 8 true], none⟩

theorem passing : sig.passing =
    [.direct [⟨0, 8, .vec 0 0⟩, ⟨8, 8, .vec 1 0⟩], .direct [⟨0, 8, .vec 2 0⟩, ⟨8, 8, .vec 3 0⟩],
      .direct [⟨0, 8, .gpr 0⟩]] := by decide

theorem result : AAPCS64.result mix = .direct [⟨0, 8, .gpr 0⟩, ⟨8, 8, .gpr 1⟩] := by decide

/-- `(ax + bx) * (ay - by)` (with `FPCR = 0`). -/
def prod (ax ay bx by_ : BitVec 64) : Nat :=
  (FP.fpMul binary64 0 ((FP.fpAdd binary64 0 ax.toNat bx.toNat).1 % 2 ^ 64)
    ((FP.fpSub binary64 0 ay.toNat by_.toNat).1 % 2 ^ 64)).1 % 2 ^ 64

theorem mod64_mod128 (x : Nat) :
    x % 18446744073709551616 % 340282366920938463463374607431768211456 = x % 18446744073709551616 := by
  omega

/-- The argument values of `k_pmix(a, b, n)`. -/
def vals (ax ay bx by_ n : BitVec 64) : List Nat := [pair ax ay, pair bx by_, n.toNat]

/-- What `k_pmix` needs (its callee contract's precondition). -/
def SPre (vs : List Nat) (s : State) : Prop :=
  ArgsAt s sig.args vs sig.passing ∧ s.fpcr = 0 ∧ (s.regs 30).toNat % 4 = 0 ∧
    (s.regs 30).toNat < 2 ^ 56

theorem spre_iff (ax ay bx by_ n : BitVec 64) (s : State) :
    SPre (vals ax ay bx by_ n) s ↔
      (s.vregs 0).toNat % 2 ^ 64 = ax.toNat ∧ (s.vregs 1).toNat % 2 ^ 64 = ay.toNat ∧
      (s.vregs 2).toNat % 2 ^ 64 = bx.toNat ∧ (s.vregs 3).toNat % 2 ^ 64 = by_.toNat ∧
      s.regs 0 = n ∧ s.fpcr = 0 ∧ (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 := by
  unfold SPre
  rw [passing]
  simp only [vals, sig, ArgsAt, ArgAt, PiecesAt, and_true, pieceAt_gpr_word]
  simp only [PieceAt, bytesOf_pair_lo, bytesOf_pair_hi, Nat.pow_zero, Nat.div_one, and_assoc,
    show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]

/-- What it guarantees: the AAPCS64 callee-saved state, memory unchanged, the struct in `X0`,
`X1`. -/
abbrev SPost (r0 r1 : BitVec 64) (s s' : State) : Prop :=
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
    s'.mem = s.mem ∧ s'.regs 0 = r0 ∧ s'.regs 1 = r1

theorem summary (ax ay bx by_ n : BitVec 64) :
    Summary Extracted.program Extracted.entry (SPre (vals ax ay bx by_ n))
      (SPost (BitVec.ofNat 64 (prod ax ay bx by_)) (n + 1)) := by
  intro s hpc hpre
  obtain ⟨h0, h1, h2, h3, hn, hf, hlra, hlrb⟩ := (spre_iff ax ay bx by_ n s).1 hpre
  simp only [Nat.reducePow] at h0 h1 h2 h3
  janus_run [h0, h1, h2, h3, hf]
  simp only [SPost, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, mod64_mod128, prod,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod, true_and, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    setVReg_apply, hf, and_true]
  rfl

/-- **`k_pmix` under the C calling convention.** -/
theorem correctness (ax ay bx by_ n : BitVec 64) :
    CEnsuresR Extracted.program Extracted.entry sig (vals ax ay bx by_ n) (fun s => s.fpcr = 0)
      (fun _ _ v => v = pair (BitVec.ofNat 64 (prod ax ay bx by_)) (n + 1)) :=
  CEnsuresA.of_summary (summary ax ay bx by_ n)
    (fun _ _ hret hs hf => ⟨hs.args, hf, hs.lr_ok hret⟩)
    (fun _ _ _ ⟨hsp, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hfc, v8, v9, v10, v11, v12,
        v13, v14, v15, _, h0, h1⟩ =>
      ⟨⟨hsp, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hfc, v8, v9, v10, v11, v12, v13,
        v14, v15⟩, _, by
        simp only [Returned, sig, result, ResultAt, PiecesAt, and_true, PieceAt, bytesOf_pair_lo,
          bytesOf_pair_hi, h0, h1, BitVec.toNat_ofNat]
        exact ⟨Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)), Nat.mod_eq_of_lt (BitVec.isLt _)⟩, rfl⟩)

end Proof
