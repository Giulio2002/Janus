import Extracted

/-!
# `FP(a float64, b float32, c float64) float64` (Go) → `k_fp` (C, floating-point arguments and
# result) → back to Go, end to end (amd64)

**Guarantee (`correctness`).** For all binary64 `a`, `c` and binary32 `b`, every Go call of
`example.com/cgo/cabi.FP` with `a`, `b`, `c` in the low bits of `X0`, `X1`, `X2` (Go's
ABIInternal), the Go `MXCSR` controls (`GoMXCSR`) and `GoPre` returns, restores `RSP`, `RBP`,
`R14`, and leaves in the low 64 bits of `X0` the bits of `(a - (double)b) * c` (round to nearest
even), under the trusted `CgoCall` contract only.

**How.** The wrapper loads the three values into `XMM0`–`XMM2`, which is where the System V
classification puts them (three SSE-class scalars); `wrapper_spec` uses `k_fp`'s callee
contract, whose precondition is the classified call, proved at the call site. The C code runs
with the Go caller's `MXCSR` control bits (`CgoEntry.mxcsr`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Spec
  Janus.Amd64.FFI Janus.C Janus.Float

namespace Proof

/-! ## The C function `k_fp` (as in `KFP.lean`), as a callee summary -/

abbrev kf : Nat := segAddr Extracted.program "k_fp"

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
    Summary Extracted.program kf (SPre (vals a b c)) (SPost (mul a b c)) := by
  intro s hpc hpre
  obtain ⟨h0, h1, h2, hm, hsb, hsa, hra, hdf⟩ := (spre_iff a b c s).1 hpre
  janus64_run [h0, h1, h2, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  simp only [SPost, setRegF_apply, setXmmF_apply, ↓reduceIte, Nat.reduceEqDiff, true_and,
    BitVec.toNat_ofNat, low64, mul, sub, cvt, Nat.mod_mod, Nat.reducePow, mx_raise_div,
    GoMXCSR.mod hm]
  exact ⟨rfl, by omega⟩


/-! ## The cgo wrapper -/

abbrev wrapper : Nat := segAddr Extracted.program "_cgo_a66fe0e77ed3_Cfunc_k_fp"

def fd (m : Memory) (a k : Nat) : BitVec 64 := BitVec.ofNat 64 (m.readLE (a + 8 * k) 8)
def fs (m : Memory) (a : Nat) : BitVec 32 := BitVec.ofNat 32 (m.readLE (a + 8) 4)

def res (m : Memory) (a : Nat) : Nat := mul (fd m a 0) (fs m a) (fd m a 2)

def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 8 ∧ a.toNat + 32 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 32 true = true ∧
    (a.toNat + 32 ≤ (t.regs 4).toNat - 4096 ∨ (t.regs 4).toNat + 8 ≤ a.toNat) ∧ GoMXCSR t

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 24) 8 (res t.mem a.toNat)) t'.mem
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
  have h24 : (t.regs 4 - 24#64).toNat = (t.regs 4).toNat - 24 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h48 : (t.regs 4 - 48#64).toNat = (t.regs 4).toNat - 48 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h48]; omega
  · janus64_simp [h48]; janus64_disch
  rintro s₁ ⟨-, f₁, rfl⟩
  apply ReturnsC.of_reaches
  have hm' : t.mxcsr.toNat / 64 = 126 := hm
  janus64_run [spre_iff, fd, fs, BitVec.toNat_ofNat, hm'] calls [summary (fd t.mem a.toNat 0)
    (fs t.mem a.toNat) (fd t.mem a.toNat 2)]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h48]; omega
  · janus64_simp [h48]; janus64_disch
  rintro s₂ ⟨-, f₂, rfl⟩
  apply ReturnsC.of_reaches
  janus64_run
  have hres : (s'.xmm 0).toNat % 18446744073709551616 = res t.mem a.toNat := by
    simp only [res, fd, fs, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]; assumption
  refine ⟨⟨by assumption, by assumption⟩, ?_⟩
  have e : (s'.xmm 0).toNat % 18446744073709551616 % 340282366920938463463374607431768211456 =
      res t.mem a.toNat := by rw [← hres]; omega
  simp only [WPost, e]
  apply Janus.MemFrame.writeLE_both
  janus_frame

/-! ## The Go side: `FP` → `_Cfunc_k_fp` → `runtime.cgocall` -/

def fnVar : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_fp.abi0" + 0x2e)

def alwaysFalse : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_fp.abi0" + 0x47)

/-- At the `cgocall`: the 32-byte frame is Go memory the runtime leaves alone, and the `MXCSR`
controls are Go's. -/
def G (s : State) : Prop :=
  (s.regs 3).toNat + 32 ≤ 2 ^ 48 ∧ GoKept s (s.regs 3).toNat 32 true ∧ GoMXCSR s

def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 3).toNat + 24) 8 (res s.mem (s.regs 3).toNat)

/-- The Go caller's precondition: `a`, `b`, `c` in the low bits of `X0`–`X2` (ABIInternal), Go's
`MXCSR`. -/
def GoPre (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) (s : State) : Prop :=
  (s.xmm 0).toNat % 2 ^ 64 = a.toNat ∧ (s.xmm 1).toNat % 2 ^ 32 = b.toNat ∧
  (s.xmm 2).toNat % 2 ^ 64 = c.toNat ∧ GoMXCSR s ∧
  StackGuardOK s 48 ∧ StackWritable s 88 8 ∧ TlsG s ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 = 0 ∧
  Outside (s.regs 14).toNat 456 [((s.regs 4).toNat - 88, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat - 8) 8 [((s.regs 4).toNat - 88, (s.regs 4).toNat + 8)] ∧
  Outside fnVar 8 [((s.regs 4).toNat - 88, (s.regs 4).toNat + 8)] ∧
  Outside alwaysFalse 1 [((s.regs 4).toNat - 1112, (s.regs 4).toNat + 8),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)]

set_option maxHeartbeats 4000000 in
theorem go_spec (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [] (GoPre a b c)
      (fun _ s' => (s'.xmm 0).toNat % 2 ^ 64 = mul a b c) := by
  intro ret hret s hs ⟨ha, hbv, hc, hm, ⟨hg1, hg2, hg3⟩, ⟨hb, htop, hst⟩, ⟨hfs, hfsr, hfsg⟩, hfa, hfv,
    haa, hav, hdg, hdt, hdf, hda⟩
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
  have h40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h80 : (s.regs 4 - 80#64).toNat = (s.regs 4).toNat - 80 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h88 : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run [hfsa]
  refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
  · simp only [G, GoKept, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
      cgoStackScratch, gStructSize, outside_cons, outside_nil, and_true]
    janus64_simp [h40, h88]
    refine ⟨by omega, ⟨?_, by omega, by omega, by omega, by omega⟩, hm⟩
    janus64_disch
  rintro s' ⟨-, m, ⟨regs, fl, xm, yh, _, mx, x87, rfl, h4, h5, h14, h15, ⟨⟨hfs1, hfs2⟩, hfsr', hfsg'⟩, -⟩, hmf⟩
  rename_i fsb
  simp only [E, res, fd, fs, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
    Janus.Amd64.GoABI.regFP, Janus.Amd64.GoABI.xmmZero, cgoStackScratch, gStructSize, setRegF,
    ↓reduceIte, Nat.reduceEqDiff, h40, h88] at hmf h4 h5 h14 h15 hfs1 hfs2 hfsr' hfsg'
  have hfsa' : (fsb + BitVec.ofNat 64 18446744073709551608).toNat = fsb.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [hmf.accessible] at hfsr'
  simp only [Janus.Arm64.Memory.accessible_writeLE] at hfsr'
  apply ReturnsC.of_reaches
  have hr : m.readLE (s.regs 4).toNat 8 = ret := by
    rw [hmf.readLE (s.regs 4).toNat 8 (by simp only [outside_cons, outside_nil, and_true]; omega)]
    janus64_simp [h_ret]
  janus64_run [h4, h5, h14, h15, hfsa', hfsg', ha, hbv, hc, hr]
  have hb' : BitVec.ofNat 32 (b.toNat % 4294967296) = b := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]
    exact Nat.mod_eq_of_lt b.isLt
  refine ⟨rfl, ?_⟩
  rw [hb']; unfold mul; omega

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
    have hk : ∀ c n, (s.regs 3).toNat ≤ c → c + n ≤ (s.regs 3).toNat + 32 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    split
    · simp only [res, fd, fs, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
      rw [hk (s.regs 3).toNat 8 (Nat.le_refl _) (by omega),
        hk ((s.regs 3).toNat + 8) 4 (by omega) (by omega),
        hk ((s.regs 3).toNat + 16) 8 (by omega) (by omega)]
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, -⟩ b _ hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`FP` end to end**, under the trusted `CgoCall` contract only. -/
theorem correctness (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [] (GoPre a b c)
      (fun _ s' => (s'.xmm 0).toNat % 2 ^ 64 = mul a b c) :=
  (go_spec a b c).refine refines

end Proof
