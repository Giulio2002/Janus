import Extracted

/-!
# `struct k_mix k_pmix(struct k_pt a, struct k_pt b, int64_t n)` (C, amd64): structs by value

```c
struct k_pt { double x, y; };           // System V: two SSE eightbytes
struct k_mix { double s; int64_t n; };  // System V: SSE, INTEGER
struct k_mix k_pmix(struct k_pt a, struct k_pt b, int64_t n) {
	struct k_mix r = { (a.x + b.x) * (a.y - b.y), n + 1 };
	return r;
}
```

**Guarantee.** For all binary64 encodings `ax ay bx by` and 64-bit `n`, every System V call of
the gcc-compiled `k_pmix` whose arguments are where the classification puts them (`CCallA`: each
`struct k_pt` is two SSE eightbytes, `a` in `XMM0`, `XMM1`, `b` in `XMM2`, `XMM3`; `n` in `RDI`)
with the default `MXCSR` controls returns, restores what System V requires (`CReturn`), and
returns the struct where the classification of the mixed result puts it: its SSE eightbyte `s`
in `XMM0` — the bits of `(ax + bx) * (ay - by)` — and its INTEGER eightbyte `n + 1` in `RAX`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.C Janus.Float

namespace Proof

def pt : CType := .struct [.double, .double]
def mix : CType := .struct [.double, .int 8 true]
def sig : SysV.Sig := ⟨some mix, [pt, pt, .int 8 true], none⟩

theorem passing : sig.passing =
    [.direct [⟨0, 8, .vec 0 0⟩, ⟨8, 8, .vec 1 0⟩], .direct [⟨0, 8, .vec 2 0⟩, ⟨8, 8, .vec 3 0⟩],
      .direct [⟨0, 8, .gpr 7⟩]] := by decide

theorem result : SysV.result mix = .direct [⟨0, 8, .vec 0 0⟩, ⟨8, 8, .gpr 0⟩] := by decide

/-- `(ax + bx) * (ay - by)`, round to nearest even. -/
def prod (ax ay bx by_ : BitVec 64) : Nat :=
  (FP.binop .mul binary64 ⟨.rne, false, false⟩
    ((FP.binop .add binary64 ⟨.rne, false, false⟩ ax.toNat bx.toNat).res % 2 ^ 64)
    ((FP.binop .sub binary64 ⟨.rne, false, false⟩ ay.toNat by_.toNat).res % 2 ^ 64)).res % 2 ^ 64

theorem low64 (x y : Nat) :
    (x / 18446744073709551616 * 18446744073709551616 + y % 18446744073709551616) %
      18446744073709551616 = y % 18446744073709551616 := by omega

def vals (ax ay bx by_ n : BitVec 64) : List Nat := [pair ax ay, pair bx by_, n.toNat]

def SPre (vs : List Nat) (s : State) : Prop :=
  ArgsAt s sig.args vs sig.passing ∧ GoMXCSR s ∧ (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    s.df = false

theorem spre_iff (ax ay bx by_ n : BitVec 64) (s : State) :
    SPre (vals ax ay bx by_ n) s ↔
      (s.xmm 0).toNat % 2 ^ 64 = ax.toNat ∧ (s.xmm 1).toNat % 2 ^ 64 = ay.toNat ∧
      (s.xmm 2).toNat % 2 ^ 64 = bx.toNat ∧ (s.xmm 3).toNat % 2 ^ 64 = by_.toNat ∧
      s.regs 7 = n ∧ GoMXCSR s ∧ (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
      s.df = false := by
  unfold SPre
  rw [passing]
  simp only [vals, sig, ArgsAt, ArgAt, PiecesAt, and_true, pieceAt_gpr_word]
  simp only [PieceAt, bytesOf_pair_lo, bytesOf_pair_hi, Nat.pow_zero, Nat.div_one, and_assoc,
    show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]

abbrev SPost (r0 : Nat) (r1 : BitVec 64) (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 3 = s.regs 3 ∧ s'.regs 5 = s.regs 5 ∧
    s'.regs 12 = s.regs 12 ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧
    s'.regs 15 = s.regs 15 ∧ s'.df = false ∧ s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64 ∧
    s'.fpucw = s.fpucw ∧ s'.mem = s.mem ∧ (s'.xmm 0).toNat % 2 ^ 64 = r0 ∧ s'.regs 0 = r1

theorem summary (ax ay bx by_ n : BitVec 64) :
    Summary Extracted.program Extracted.entry (SPre (vals ax ay bx by_ n))
      (SPost (prod ax ay bx by_) (n + 1)) := by
  intro s hpc hpre
  obtain ⟨h0, h1, h2, h3, hn, hm, hsb, hsa, hra, hdf⟩ := (spre_iff ax ay bx by_ n s).1 hpre
  simp only [Nat.reducePow] at h0 h1 h2 h3
  janus64_run [h0, h1, h2, h3, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  simp only [SPost, setRegF_apply, setXmmF_apply, ↓reduceIte, Nat.reduceEqDiff, true_and,
    BitVec.toNat_ofNat, low64, prod, Nat.mod_mod, Nat.reducePow, mx_raise_div, GoMXCSR.mod hm]
  exact ⟨rfl, by omega, trivial⟩

/-- **`k_pmix` under the System V calling convention.** -/
theorem correctness (ax ay bx by_ n : BitVec 64) :
    CEnsuresR Extracted.program Extracted.entry sig (vals ax ay bx by_ n)
      (fun s => CStack s 0 8 ∧ GoMXCSR s)
      (fun _ _ v => v = pair (BitVec.ofNat 64 (prod ax ay bx by_)) (n + 1)) :=
  CEnsuresA.of_summary (summary ax ay bx by_ n)
    (fun _ s hret hs ⟨⟨_, _, hnw, hst⟩, hm⟩ => by
      simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add] at hnw hst
      exact ⟨hs.args, hm, hnw, Janus.Arm64.Memory.accessible_weaken _ hst, hs.ret_lt hret, hs.df⟩)
    (fun _ _ _ ⟨hsp, h3, h5, h12, h13, h14, h15, hdf, hmx, hfw, _, h0, h1⟩ =>
      ⟨⟨hsp, h3, h5, h12, h13, h14, h15, hdf, hmx, hfw⟩, _, by
        simp only [Returned, sig, result, ResultAt, PiecesAt, and_true, PieceAt, bytesOf_pair_lo,
          bytesOf_pair_hi, h1, BitVec.toNat_ofNat, Nat.pow_zero, Nat.div_one, Nat.reducePow] at h0 ⊢
        exact ⟨by rw [h0, prod, Nat.mod_mod], Nat.mod_eq_of_lt (BitVec.isLt _)⟩, rfl⟩)

namespace Witness

def ret : Nat := 0x1000
def wsp : Nat := 0x20008  -- addr-ok: a chosen stack window, not a binary address
def ax0 : BitVec 64 := 1#64
def ay0 : BitVec 64 := 2#64
def bx0 : BitVec 64 := 3#64
def by0 : BitVec 64 := 4#64
def n0 : BitVec 64 := 9#64

def smem : Janus.Arm64.Memory :=
  ⟨fun a => if wsp ≤ a ∧ a < wsp + 8 then BitVec.ofNat 8 (ret / 256 ^ (a - wsp)) else 0,
   [⟨wsp - 64, 128, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 7 then n0 else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun i => if i = 0 then BitVec.ofNat 128 ax0.toNat else if i = 1 then BitVec.ofNat 128 ay0.toNat
      else if i = 2 then BitVec.ofNat 128 bx0.toNat else if i = 3 then BitVec.ofNat 128 by0.toNat else 0,
    mem := smem }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem mx : GoMXCSR s0 := by unfold GoMXCSR; decide

theorem spre : SPre (vals ax0 ay0 bx0 by0 n0) s0 :=
  (spre_iff ax0 ay0 bx0 by0 n0 s0).2 ⟨by decide, by decide, by decide, by decide, by decide, mx,
    by decide, by decide, by decide, by decide⟩

theorem call : CCallA (Extracted.program.withExit ret) Extracted.entry sig (vals ax0 ay0 bx0 by0 n0) s0 :=
  ⟨rfl, by decide, by decide, rfl, spre.1, (by intro t ht hr; simp only [sig, Option.some.injEq] at ht; subst ht; rw [result] at hr; cases hr), (by intro h; simp [sig] at h)⟩

theorem pre : CStack s0 0 8 ∧ GoMXCSR s0 := ⟨⟨by decide, by decide, by decide, by decide⟩, mx⟩

/-- The hypotheses of `correctness` hold together and the call returns with its guarantee. -/
theorem nonvacuous : ∃ (ax ay bx by_ n : BitVec 64) (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCallA (Extracted.program.withExit ret) Extracted.entry sig (vals ax ay bx by_ n) s ∧
    (CStack s 0 8 ∧ GoMXCSR s) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => CReturn s s' ∧
      (∃ v, Returned sig s s' v ∧ (v = pair (BitVec.ofNat 64 (prod ax ay bx by_)) (n + 1)))) :=
  ⟨ax0, ay0, bx0, by0, n0, ret, s0, hret, call, pre,
    correctness ax0 ay0 bx0 by0 n0 ret hret s0 call pre⟩

end Witness

end Proof
