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

theorem correctness (ax ay bx by_ n : BitVec 64) :
    CEnsuresR Extracted.program Extracted.entry sig
      [pair ax ay, pair bx by_, n.toNat] (fun s => s.fpcr = 0)
      (fun _ _ v => v = pair (BitVec.ofNat 64 (prod ax ay bx by_)) (n + 1)) := by
  intro ret hret s hs hf
  have hpc := hs.pc
  have hlr := hs.lr
  have ha := hs.args
  rw [passing] at ha
  simp only [sig, ArgsAt, ArgAt, PiecesAt, and_true, pieceAt_gpr_word] at ha
  obtain ⟨⟨h0, h1⟩, ⟨h2, h3⟩, hn⟩ := ha
  simp only [PieceAt, bytesOf_pair_lo, bytesOf_pair_hi, Nat.pow_zero, Nat.div_one,
    Nat.reducePow] at h0 h1 h2 h3
  simp only [Program.withExit] at hlr
  janus_run [h0, h1, h2, h3, hf]
  refine ⟨_, ?_, rfl⟩
  simp only [Returned, sig, result, ResultAt, PiecesAt, and_true, PieceAt, bytesOf_pair_lo,
    bytesOf_pair_hi, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, mod64_mod128, prod,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]
  constructor
  · trivial
  · exact Nat.mod_eq_of_lt (BitVec.isLt _)

end Proof
