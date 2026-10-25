import Extracted

/-!
# `PMix(ax, ay, bx, by float64, n int64) (float64, int64)` (Go) → `k_pmix` (C, structs by value,
# mixed SSE/INTEGER struct result) → back to Go, end to end (amd64)

**Guarantee (`correctness`).** For all binary64 `ax ay bx by` and 64-bit `n`, every Go call of
`example.com/cgo/cabi.PMix` with `ax ay bx by` in the low bits of `X0`–`X3` and `n` in `RAX`
(Go's ABIInternal), the Go `MXCSR` controls (`GoMXCSR`) and `GoPre` returns, restores `RSP`,
`RBP`, `R14`, and returns the bits of `(ax + bx) * (ay - by)` (round to nearest even) in the low
64 bits of `X0` and `n + 1` in `RAX`, under the trusted `CgoCall` contract only.

**How.** The wrapper loads the two `struct k_pt` arguments into `XMM0`–`XMM3` and `n` into `RDI`,
where the System V classification puts them (each `struct k_pt` is two SSE eightbytes), and
takes the mixed result `struct k_mix` from `XMM0` (SSE) and `RAX` (INTEGER), where
`SysV.result` puts it; `wrapper_spec` uses `k_pmix`'s callee contract, whose precondition is
the classified call, proved at the call site.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Spec
  Janus.Amd64.FFI Janus.C Janus.Float

namespace Proof

/-! ## The C function `k_pmix` (as in `KPMix.lean`), as a callee summary -/

abbrev kp : Nat := segAddr Extracted.program "k_pmix"

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
    Summary Extracted.program kp (SPre (vals ax ay bx by_ n))
      (SPost (prod ax ay bx by_) (n + 1)) := by
  intro s hpc hpre
  obtain ⟨h0, h1, h2, h3, hn, hm, hsb, hsa, hra, hdf⟩ := (spre_iff ax ay bx by_ n s).1 hpre
  simp only [Nat.reducePow] at h0 h1 h2 h3
  janus64_run [h0, h1, h2, h3, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  simp only [SPost, setRegF_apply, setXmmF_apply, ↓reduceIte, Nat.reduceEqDiff, true_and,
    BitVec.toNat_ofNat, low64, prod, Nat.mod_mod, Nat.reducePow, mx_raise_div, GoMXCSR.mod hm]
  exact ⟨rfl, by omega, trivial⟩


/-! ## The cgo wrapper -/

abbrev wrapper : Nat := segAddr Extracted.program "_cgo_a66fe0e77ed3_Cfunc_k_pmix"

/-- The cgo frame at `a`: `p0 = {ax, ay}` at `a`, `p1 = {bx, by}` at `a + 16`, `p2 = n` at
`a + 32`, the result `{s, n}` at `a + 40`. -/
def fw (m : Memory) (a k : Nat) : BitVec 64 := BitVec.ofNat 64 (m.readLE (a + 8 * k) 8)

/-- The two result words. -/
def r0 (m : Memory) (a : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (prod (fw m a 0) (fw m a 1) (fw m a 2) (fw m a 3))
def r1 (m : Memory) (a : Nat) : BitVec 64 := fw m a 4 + 1

def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 8 ∧ a.toNat + 56 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 56 true = true ∧
    (a.toNat + 56 ≤ (t.regs 4).toNat - 4096 ∨ (t.regs 4).toNat + 8 ≤ a.toNat) ∧ GoMXCSR t

/-- The wrapper stores the result struct with one 16-byte `movups`. -/
def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 40) 16 (pair (r0 t.mem a.toNat) (r1 t.mem a.toNat))) t'.mem
    [((t.regs 4).toNat - 4096, (t.regs 4).toNat)]

set_option maxHeartbeats 4000000 in
theorem wrapper_spec (T a : BitVec 64) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd, hm⟩
  apply ReturnsC.of_reaches
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : t.regs 7 = a := hs.reg (i := 0) (by simp)
  simp only [Amd64.Program.withExit] at h_ret
  simp only [CABI.regSP] at hal hb htop hacc
  have h56 : (t.regs 4 - 56#64).toNat = (t.regs 4).toNat - 56 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h64 : (t.regs 4 - 64#64).toNat = (t.regs 4).toNat - 64 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h64]; omega
  · janus64_simp [h64]; janus64_disch
  rintro s₁ ⟨-, f₁, rfl⟩
  apply ReturnsC.of_reaches
  have hm' : t.mxcsr.toNat / 64 = 126 := hm
  janus64_run [spre_iff, fw, BitVec.toNat_ofNat, hm'] calls [summary (fw t.mem a.toNat 0)
    (fw t.mem a.toNat 1) (fw t.mem a.toNat 2) (fw t.mem a.toNat 3) (fw t.mem a.toNat 4)]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h64]; omega
  · janus64_simp [h64]; janus64_disch
  rintro s₂ ⟨-, f₂, rfl⟩
  apply ReturnsC.of_reaches
  have hal56 : ((t.regs 4).toNat - 56) % 16 = 0 := by omega
  janus64_run [readLE_16, hal56]
  have hres : (s'.xmm 0).toNat % 18446744073709551616 =
      prod (fw t.mem a.toNat 0) (fw t.mem a.toNat 1) (fw t.mem a.toNat 2) (fw t.mem a.toNat 3) := by
    simp only [fw, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]; assumption
  refine ⟨⟨by assumption, by assumption⟩, ?_⟩
  have e : (s'.xmm 0).toNat % 18446744073709551616 +
      18446744073709551616 * ((t.mem.readLE (a.toNat + 32) 8 + 1) % 18446744073709551616) =
      pair (r0 t.mem a.toNat) (r1 t.mem a.toNat) := by
    have hp := Nat.mod_lt (prod (fw t.mem a.toNat 0) (fw t.mem a.toNat 1) (fw t.mem a.toNat 2)
      (fw t.mem a.toNat 3)) (show 0 < 2 ^ 64 by decide)
    simp only [pair, r0, r1, BitVec.toNat_ofNat, BitVec.toNat_add, hres]
    simp only [fw, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, BitVec.toNat_ofNat,
      BitVec.reduceToNat, Nat.reducePow] at hp ⊢
    omega
  simp only [WPost, e]
  apply Janus.MemFrame.writeLE_both
  janus_frame

/-! ## The Go side: `PMix` → `_Cfunc_k_pmix` → `runtime.cgocall` -/

def fnVar : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_pmix.abi0" + 0x2f)

def alwaysFalse : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_pmix.abi0" + 0x48)

/-- At the `cgocall`: the 56-byte frame is Go memory the runtime leaves alone, and the `MXCSR`
controls are Go's. -/
def G (s : State) : Prop :=
  (s.regs 3).toNat + 56 ≤ 2 ^ 48 ∧ GoKept s (s.regs 3).toNat 56 true ∧ GoMXCSR s

def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 3).toNat + 40) 16 (pair (r0 s.mem (s.regs 3).toNat) (r1 s.mem (s.regs 3).toNat))

/-- The Go caller's precondition: `ax ay bx by` in the low bits of `X0`–`X3` (ABIInternal), Go's
`MXCSR`. -/
def GoPre (ax ay bx by_ : BitVec 64) (s : State) : Prop :=
  (s.xmm 0).toNat % 2 ^ 64 = ax.toNat ∧ (s.xmm 1).toNat % 2 ^ 64 = ay.toNat ∧
  (s.xmm 2).toNat % 2 ^ 64 = bx.toNat ∧ (s.xmm 3).toNat % 2 ^ 64 = by_.toNat ∧ GoMXCSR s ∧
  StackGuardOK s 72 ∧ StackWritable s 112 8 ∧ TlsG s ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 = 0 ∧
  Outside (s.regs 14).toNat 456 [((s.regs 4).toNat - 112, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat - 8) 8 [((s.regs 4).toNat - 112, (s.regs 4).toNat + 8)] ∧
  Outside fnVar 8 [((s.regs 4).toNat - 112, (s.regs 4).toNat + 8)] ∧
  Outside alwaysFalse 1 [((s.regs 4).toNat - 1136, (s.regs 4).toNat + 8),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)]

set_option maxHeartbeats 4000000 in
theorem go_spec (ax ay bx by_ n : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [n] (GoPre ax ay bx by_)
      (fun _ s' => (s'.xmm 0).toNat % 2 ^ 64 = prod ax ay bx by_ ∧ s'.regs 0 = n + 1) := by
  intro ret hret s hs ⟨hax, hay, hbx, hby, hm, ⟨hg1, hg2, hg3⟩, ⟨hb, htop, hst⟩, ⟨hfs, hfsr, hfsg⟩,
    hfa, hfv, haa, hav, hdg, hdt, hdf, hda⟩
  apply ReturnsC.of_reaches
  janus64_intro hs
  janus_eval_nat h_fv : fnVar
  janus_eval_nat h_af : alwaysFalse
  rw [h_fv] at hfa hfv hdf
  rw [h_af] at haa hav hda
  simp only [outside_cons, outside_nil, and_true, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
    stackguard0, stackguard0Offset] at *
  have hfsa : (s.fsBase + BitVec.ofNat 64 18446744073709551608).toNat = s.fsBase.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h64 : (s.regs 4 - 64#64).toNat = (s.regs 4).toNat - 64 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h104 : (s.regs 4 - 104#64).toNat = (s.regs 4).toNat - 104 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h112 : (s.regs 4 - 112#64).toNat = (s.regs 4).toNat - 112 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run [hfsa]
  refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
  · simp only [G, GoKept, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
      cgoStackScratch, gStructSize, outside_cons, outside_nil, and_true]
    janus64_simp [h64, h112]
    refine ⟨by omega, ⟨?_, by omega, by omega, by omega, by omega⟩, hm⟩
    janus64_disch
  rintro s' ⟨-, m, ⟨regs, fl, xm, yh, _, mx, x87, rfl, h4, h5, h14, h15, ⟨⟨hfs1, hfs2⟩, hfsr', hfsg'⟩, -⟩, hmf⟩
  rename_i fsb
  simp only [E, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
    Janus.Amd64.GoABI.regFP, Janus.Amd64.GoABI.xmmZero, cgoStackScratch, gStructSize, setRegF,
    ↓reduceIte, Nat.reduceEqDiff, h64, h112] at hmf h4 h5 h14 h15 hfs1 hfs2 hfsr' hfsg'
  have hfsa' : (fsb + BitVec.ofNat 64 18446744073709551608).toNat = fsb.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [hmf.accessible] at hfsr'
  simp only [Janus.Arm64.Memory.accessible_writeLE] at hfsr'
  have hr : m.readLE (s.regs 4).toNat 8 = ret := by
    rw [hmf.readLE (s.regs 4).toNat 8 (by simp only [outside_cons, outside_nil, and_true]; omega)]
    janus64_simp [h_ret]
  apply ReturnsC.of_reaches
  janus64_run [h4, h5, h14, h15, hfsa', hfsg', hax, hay, hbx, hby, hr]
  have hz : (s.regs 4).toNat - 24 - ((s.regs 4).toNat - 64 + 40) = 0 := by omega
  simp only [hz, r0, r1, fw, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
  janus64_simp
  have h8 : (s.regs 4).toNat - 16 - ((s.regs 4).toNat - 64 + 40) = 8 := by omega
  simp only [Nat.reducePow] at hax hay hbx hby
  rw [h8, hax, hay, hbx, hby]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hl := bytesOf_pair_lo (BitVec.ofNat 64 (prod ax ay bx by_)) (n + 1#64)
  have hh := bytesOf_pair_hi (BitVec.ofNat 64 (prod ax ay bx by_)) (n + 1#64)
  simp only [bytesOf, Nat.pow_zero, Nat.reducePow] at hl hh
  rw [hl, hh]
  have hp : prod ax ay bx by_ < 2 ^ 64 := Nat.mod_lt _ (by decide)
  refine ⟨rfl, ?_, BitVec.ofNat_toNat _ _ |>.trans (BitVec.setWidth_eq _)⟩
  simp only [BitVec.toNat_ofNat]; omega

/-! ## Composition -/

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · rintro s t ret ⟨hb, ⟨hacc, hout⟩, hm⟩ he
    have hsep := he.stackSep _ _ _ hacc
    simp only [outside_cons, outside_nil, and_true, Janus.Amd64.GoABI.regSP] at hsep
    exact ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩,
      by have := hsep; unfold cgoCStack at this; omega, he.mxcsr.trans hm⟩
  · intro s _; rfl
  · rintro s t ret t' ⟨hb, ⟨hacc, hout⟩, -⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by
      simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep ⊢; omega)
    simp only [Janus.Arm64.Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Janus.Arm64.Memory.bytes_writeLE, Janus.Arm64.Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 3).toNat ≤ c → c + n ≤ (s.regs 3).toNat + 56 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    have hr : r1 t.mem (s.regs 3).toNat = r1 s.mem (s.regs 3).toNat ∧
        r0 t.mem (s.regs 3).toNat = r0 s.mem (s.regs 3).toNat := by
      simp only [r0, r1, fw, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
      rw [hk (s.regs 3).toNat 8 (Nat.le_refl _) (by omega),
        hk ((s.regs 3).toNat + 8) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 16) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 24) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 32) 8 (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    rw [hr.1, hr.2]
    split
    · rfl
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, -⟩ b _ hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`PMix` end to end**, under the trusted `CgoCall` contract only. -/
theorem correctness (ax ay bx by_ n : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [n] (GoPre ax ay bx by_)
      (fun _ s' => (s'.xmm 0).toNat % 2 ^ 64 = prod ax ay bx by_ ∧ s'.regs 0 = n + 1) :=
  (go_spec ax ay bx by_ n).refine refines

end Proof
