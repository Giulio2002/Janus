import Extracted

/-!
# `FP(a float64, b float32, c float64) float64` (Go) → `k_fp` (C, floating-point arguments and
# result) → back to Go, end to end (arm64)

```go
func FP(a float64, b float32, c float64) float64 { return float64(C.k_fp(C.double(a), C.float(b), C.double(c))) }
```

**Guarantee (`correctness`).** For all binary64 `a`, `c` and binary32 `b`, every Go call of
`example.com/cgo/cabi.FP` with `a`, `b`, `c` in `D0`, `S1`, `D2` (Go's ABIInternal), `FPCR = 0`
and `GoPre` (the stack checks fall through, 112 bytes of stack below `SP` writable, the cgo
globals as statically initialised and away from the stack, `g` and the TLS slot away from the
stack) returns, restores `SP`, `g` and the frame pointer, and leaves in `D0` the bits of
`(a - (double)b) * c` as the Arm floating-point semantics computes them, under the trusted
`CgoCall` contract only.

**How.** As `GoStack10.lean`: the wrapper calls `k_fp` with `D0`, `S1`, `D2` loaded from the cgo
frame, and `wrapper_spec` uses `k_fp`'s callee contract, whose precondition is the classified
call (`ArgsAt … sig.passing`), proved at the call site; the result comes back in `D0`, which the
wrapper stores in the frame. The C code runs with the Go caller's `FPCR` (`CgoEntry.fpcr`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.Spec Janus.FFI Janus.C Janus.Float

namespace Proof

/-! ## The C function `k_fp` (as in `KFP.lean`), as a callee summary -/

abbrev kf : Nat := segAddr Extracted.program "k_fp"

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
    Summary Extracted.program kf (SPre (vals a b c))
      (SPost ((mul 0 a b c).1 % 2 ^ 64)) := by
  intro s hpc hpre
  obtain ⟨h0, h1, h2, ht, hlra, hlrb⟩ := (spre_iff a b c s).1 hpre
  janus_run [h0, h1, h2, ht]
  simp only [SPost, setVReg_apply, ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow,
    mod64_mod128, Nat.mod_mod, mul, sub, cvt, true_and, ht]
  exact ⟨rfl, trivial⟩


/-! ## The cgo wrapper -/

abbrev wrapper : Nat := segAddr Extracted.program "_cgo_a66fe0e77ed3_Cfunc_k_fp"

/-- The cgo frame at `a`: `p0` (double) at `a`, `p1` (float) at `a + 8`, `p2` at `a + 16`, the
result at `a + 24`. -/
def fd (m : Memory) (a k : Nat) : BitVec 64 := BitVec.ofNat 64 (m.readLE (a + 8 * k) 8)
def fs (m : Memory) (a : Nat) : BitVec 32 := BitVec.ofNat 32 (m.readLE (a + 8) 4)

def res (m : Memory) (a : Nat) : Nat := (mul 0 (fd m a 0) (fs m a) (fd m a 2)).1 % 2 ^ 64

def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 0 ∧ a.toNat + 32 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 32 true = true ∧
    (a.toNat + 32 ≤ t.sp.toNat - 4096 ∨ t.sp.toNat ≤ a.toNat) ∧ t.fpcr = 0

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 24) 8 (res t.mem a.toNat)) t'.mem
    [(t.sp.toNat - 4096, t.sp.toNat)]

theorem wrapper_spec (T a : BitVec 64)
    (hex : s'.excl = s.excl := by first | rfl | simp_all) (hep : s'.exclPass = s.exclPass := by first | rfl | simp_all) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd, hf⟩
  apply ReturnsC.of_reaches
  janus_intro hs.call
  simp only [Nat.add_zero] at htop hacc
  janus_run
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₁ ⟨-, f₁, m₁, rfl, hm₁⟩
  have h48 : (t.sp - 48#64).toNat = t.sp.toNat - 48 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  apply ReturnsC.of_reaches
  janus_run [spre_iff, h48, fd, fs, BitVec.toNat_ofNat, hf] until [wrapper + 0x28]
    calls [summary (fd t.mem a.toNat 0) (fs t.mem a.toNat) (fd t.mem a.toNat 2)]
  dsimp only at *
  obtain ⟨regs', sp', pc', fl', mem', dz', vr', tp', fc', fsr', ex, ep⟩ := s'
  dsimp only at *
  subst sp' pc' mem' fc' hex hep
  simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff] at *
  have h19' : regs' 19 = a := by assumption
  have h20' : regs' 20 = T := by assumption
  have h29' : regs' 29 = t.sp - 48#64 := by assumption
  janus_run [h48, h19', h20', h29']
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp [h48]
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₂ ⟨-, f₂, m₂, rfl, hm₂⟩
  dsimp only at hm₁ hm₂
  apply ReturnsC.of_reaches
  janus_run [h19', h20', h29']
  refine ⟨?_, ?_⟩
  · repeat' (apply And.intro)
    all_goals assumption
  have hres : (vr' 0).toNat % 18446744073709551616 = res t.mem a.toNat := by
    simp only [res, fd, fs, Nat.reducePow, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]; assumption
  have hr : res t.mem a.toNat < 340282366920938463463374607431768211456 := by
    unfold res; have := Nat.mod_lt ((mul 0 (fd t.mem a.toNat 0) (fs t.mem a.toNat)
      (fd t.mem a.toNat 2)).1) (show 0 < 2 ^ 64 by decide); omega
  simp only [WPost, hres, writeLE_mod_8, Nat.mod_eq_of_lt hr]
  have hT : (18446744073709551616 - T.toNat + T.toNat) % 18446744073709551616 = 0 := by
    have := T.isLt; omega
  simp only [hT, Nat.add_zero]
  have hf : MemFrame t.mem m₂ [(t.sp.toNat - 4096, t.sp.toNat)] := by
    refine MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)])
      (MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)])
        (rs' := [(t.sp.toNat - 4096, t.sp.toNat)])
        (MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)]) ?_ hm₁ ?_) ?_ ?_) hm₂ ?_
    all_goals first
      | janus_frame
      | (intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  exact hf.writeLE_both _ _ _

/-! ## The Go side: `FP` → `_Cfunc_k_fp` → `runtime.cgocall` -/

def fnVar : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_fp.abi0" + 0x28)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_fp.abi0" 10)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_fp.abi0" 11) 3

def alwaysFalse : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_fp.abi0" + 0x34)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_fp.abi0" 13)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_fp.abi0" 14) 0

/-- At the `cgocall`: the 32-byte frame is Go memory the runtime leaves alone, and `FPCR = 0`. -/
def G (s : State) : Prop :=
  (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ GoKept s (s.regs 1).toNat 32 true ∧ s.fpcr = 0

def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 1).toNat + 24) 8 (res s.mem (s.regs 1).toNat)

def GoPre (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) (s : State) : Prop :=
  (s.vregs 0).toNat % 2 ^ 64 = a.toNat ∧ (s.vregs 1).toNat % 2 ^ 32 = b.toNat ∧
  (s.vregs 2).toNat % 2 ^ 64 = c.toNat ∧ s.fpcr = 0 ∧
  GuardOK s 48 ∧ StackOK s 112 0 ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 % 2 = 0 ∧
  Outside (s.regs 28).toNat 456 [(s.sp.toNat - 112, s.sp.toNat)] ∧
  Outside (s.tpidr.toNat + 16) 8 [(s.sp.toNat - 112, s.sp.toNat)] ∧
  Outside fnVar 8 [(s.sp.toNat - 112, s.sp.toNat)] ∧
  Outside alwaysFalse 1 [(s.sp.toNat - 1120, s.sp.toNat), ((s.regs 28).toNat, (s.regs 28).toNat + 456),
    (s.tpidr.toNat + 16, s.tpidr.toNat + 24)]

set_option maxHeartbeats 4000000 in
theorem go_spec (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [] (GoPre a b c)
      (fun _ s' => (s'.vregs 0).toNat % 2 ^ 64 = (mul 0 a b c).1 % 2 ^ 64) := by
  intro ret hret s hs ⟨ha, hbv, hc, hf, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, htop, hst⟩, hfa, hfv, haa, hav, hdg,
    hdt, hdf, hda⟩
  apply ReturnsC.of_reaches
  janus_intro hs
  janus_eval_nat h_fv : fnVar
  janus_eval_nat h_af : alwaysFalse
  rw [h_fv] at hfa hfv hdf
  rw [h_af] at haa hav hda
  simp only [outside_cons, outside_nil, and_true, Nat.add_zero] at *
  have h40 : (s.sp - 40#64).toNat = s.sp.toNat - 40 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h96 : (s.sp - 96#64).toNat = s.sp.toNat - 96 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus_run
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus_simp [hfv]
  · simp only [G, GoKept, cgoClobber, GoABI.regG, cgoStackScratch, gStructSize, tlsGOffset,
      outside_cons, outside_nil, and_true]
    janus_simp [h40, h96]
    refine ⟨by omega, ?_, by omega, by omega, by omega, by omega⟩
    janus_disch
  rintro s' ⟨-, m, ⟨regs, fl, vr, tp, fs', rfl, hg, hfp⟩, hmf⟩
  simp only [E, res, fd, fs, cgoClobber, GoABI.regG, GoABI.regFP, cgoStackScratch, gStructSize,
    tlsGOffset, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h40, h96] at hmf hg hfp
  apply ReturnsC.of_reaches
  janus_run [hg, hfp, ha, hbv, hc]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, mod64_mod128]

/-! ## Composition -/

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · rintro s t ret ⟨hb, ⟨hacc, hout⟩, hf⟩ he
    have hsep := he.stackSep _ _ _ hacc
    simp only [outside_cons, outside_nil, and_true] at hsep
    exact ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩,
      by have := hsep; unfold cgoCStack at this; omega, he.fpcr.trans hf⟩
  · intro s _; rfl
  · rintro s t ret t' ⟨hb, ⟨hacc, hout⟩, _⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by simpa [cgoCStack] using hsep)
    simp only [Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Memory.bytes_writeLE, Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 1).toNat ≤ c → c + n ≤ (s.regs 1).toNat + 32 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    split
    · simp only [res, fd, fs, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
      rw [hk _ 8 (Nat.le_refl _) (by omega), hk (_ + 8) 4 (by omega) (by omega),
        hk (_ + 16) 8 (by omega) (by omega)]
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, _⟩ b _ hna
    rw [E, Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`FP` end to end**, under the trusted `CgoCall` contract only. -/
theorem correctness (a : BitVec 64) (b : BitVec 32) (c : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [] (GoPre a b c)
      (fun _ s' => (s'.vregs 0).toNat % 2 ^ 64 = (mul 0 a b c).1 % 2 ^ 64) :=
  (go_spec a b c).refine refines

end Proof
