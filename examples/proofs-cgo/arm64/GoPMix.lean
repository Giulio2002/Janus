import Extracted

/-!
# `PMix(ax, ay, bx, by float64, n int64) (float64, int64)` (Go) → `k_pmix` (C, structs by value
# in and out) → back to Go, end to end (arm64)

```go
func PMix(ax, ay, bx, by float64, n int64) (float64, int64) {
	r := C.k_pmix(C.struct_k_pt{x: C.double(ax), y: C.double(ay)},
		C.struct_k_pt{x: C.double(bx), y: C.double(by)}, C.int64_t(n))
	return float64(r.s), int64(r.n)
}
```

**Guarantee (`correctness`).** For all binary64 `ax ay bx by` and 64-bit `n`, every Go call of
`example.com/cgo/cabi.PMix` with the floats in `D0`–`D3`, `n` in `X0`, `FPCR = 0` and `GoPre`
returns, restores `SP`, `g` and the frame pointer, and returns in `D0` the bits of
`(ax + bx) * (ay - by)` (Arm floating-point semantics) and in `X0` `n + 1`, under the trusted
`CgoCall` contract only.

**How.** The C wrapper passes the two `struct k_pt` (homogeneous floating-point aggregates) one
member per register in `D0`–`D3` and `n` in `X0`, and takes the 16-byte non-HFA result from
`X0`, `X1`: exactly what the callee contract `summary` of `k_pmix` states in terms of Janus's
classification (`ArgsAt … sig.passing`, `AAPCS64.result`), proved at the call site.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.Spec Janus.FFI Janus.C Janus.Float

namespace Proof

/-! ## The C function `k_pmix` (as in `KPMix.lean`), as a callee summary -/

abbrev kp : Nat := segAddr Extracted.program "k_pmix"

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
    Summary Extracted.program kp (SPre (vals ax ay bx by_ n))
      (SPost (BitVec.ofNat 64 (prod ax ay bx by_)) (n + 1)) := by
  intro s hpc hpre
  obtain ⟨h0, h1, h2, h3, hn, hf, hlra, hlrb⟩ := (spre_iff ax ay bx by_ n s).1 hpre
  simp only [Nat.reducePow] at h0 h1 h2 h3
  janus_run [h0, h1, h2, h3, hf]
  simp only [SPost, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, mod64_mod128, prod,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod, true_and, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    setVReg_apply, hf, and_true]
  rfl


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
  CStack t 4096 0 ∧ a.toNat + 56 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 56 true = true ∧
    (a.toNat + 56 ≤ t.sp.toNat - 4096 ∨ t.sp.toNat ≤ a.toNat) ∧ t.fpcr = 0

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame ((t.mem.writeLE (a.toNat + 40) 8 (r0 t.mem a.toNat).toNat).writeLE (a.toNat + 48) 8
      (r1 t.mem a.toNat).toNat) t'.mem [(t.sp.toNat - 4096, t.sp.toNat)]

theorem wrapper_spec (T a : BitVec 64) :
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
  apply ReturnsC.of_reaches
  janus_run [spre_iff, fw, BitVec.toNat_ofNat, hf] calls [summary (fw t.mem a.toNat 0)
    (fw t.mem a.toNat 1) (fw t.mem a.toNat 2) (fw t.mem a.toNat 3) (fw t.mem a.toNat 4)]
  have h48 : (t.sp - 48#64).toNat = t.sp.toNat - 48 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp [h48]
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₂ ⟨-, f₂, m₂, rfl, hm₂⟩
  dsimp only at hm₁ hm₂
  try rw [h48] at hm₂
  apply ReturnsC.of_reaches
  janus_run
  refine ⟨?_, ?_⟩
  · repeat' constructor
    all_goals assumption
  simp only [WPost, r0, r1, fw, Nat.reducePow, writeLE_mod_8, Nat.mul_zero, Nat.add_zero,
    Nat.reduceMul, BitVec.toNat_ofNat]
  have hT : (18446744073709551616 - T.toNat + T.toNat) % 18446744073709551616 = 0 := by
    have := T.isLt; omega
  simp only [hT, Nat.add_zero]
  have hf : MemFrame t.mem m₂ [(t.sp.toNat - 4096, t.sp.toNat)] := by
    refine MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)])
      (MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)]) ?_ hm₁ ?_) hm₂ ?_
    all_goals first
      | janus_frame
      | (intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  have e : (BitVec.ofNat 64 (t.mem.readLE (a.toNat + 32) 8) + 1).toNat =
      (t.mem.readLE (a.toNat + 32) 8 + 1) % 18446744073709551616 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega
  rw [e, writeLE_mod_8]
  exact (hf.writeLE_both _ _ _).writeLE_both _ _ _

/-! ## The Go side: `PMix` → `_Cfunc_k_pmix` → `runtime.cgocall` -/

def fnVar : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_pmix.abi0" + 0x2c)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_pmix.abi0" 11)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_pmix.abi0" 12) 3

def alwaysFalse : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_pmix.abi0" + 0x38)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_pmix.abi0" 14)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_pmix.abi0" 15) 0

def G (s : State) : Prop :=
  (s.regs 1).toNat + 56 ≤ 2 ^ 48 ∧ GoKept s (s.regs 1).toNat 56 true ∧ s.fpcr = 0

def E (s : State) : Memory :=
  (s.mem.writeLE ((s.regs 1).toNat + 40) 8 (r0 s.mem (s.regs 1).toNat).toNat).writeLE
    ((s.regs 1).toNat + 48) 8 (r1 s.mem (s.regs 1).toNat).toNat

def GoPre (ax ay bx by_ : BitVec 64) (s : State) : Prop :=
  (s.vregs 0).toNat % 2 ^ 64 = ax.toNat ∧ (s.vregs 1).toNat % 2 ^ 64 = ay.toNat ∧
  (s.vregs 2).toNat % 2 ^ 64 = bx.toNat ∧ (s.vregs 3).toNat % 2 ^ 64 = by_.toNat ∧ s.fpcr = 0 ∧
  GuardOK s 80 ∧ StackOK s 144 0 ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 % 2 = 0 ∧
  Outside (s.regs 28).toNat 456 [(s.sp.toNat - 144, s.sp.toNat)] ∧
  Outside (s.tpidr.toNat + 16) 8 [(s.sp.toNat - 144, s.sp.toNat)] ∧
  Outside fnVar 8 [(s.sp.toNat - 144, s.sp.toNat)] ∧
  Outside alwaysFalse 1 [(s.sp.toNat - 1152, s.sp.toNat), ((s.regs 28).toNat, (s.regs 28).toNat + 456),
    (s.tpidr.toNat + 16, s.tpidr.toNat + 24)]

set_option maxHeartbeats 4000000 in
theorem go_spec (ax ay bx by_ n : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [n] (GoPre ax ay bx by_)
      (fun _ s' => (s'.vregs 0).toNat % 2 ^ 64 = prod ax ay bx by_ ∧ s'.regs 0 = n + 1) := by
  intro ret hret s hs ⟨hax, hay, hbx, hby, hf, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, htop, hst⟩, hfa, hfv, haa,
    hav, hdg, hdt, hdf, hda⟩
  apply ReturnsC.of_reaches
  janus_intro hs
  janus_eval_nat h_fv : fnVar
  janus_eval_nat h_af : alwaysFalse
  rw [h_fv] at hfa hfv hdf
  rw [h_af] at haa hav hda
  simp only [outside_cons, outside_nil, and_true, Nat.add_zero] at *
  have h72 : (s.sp - 72#64).toNat = s.sp.toNat - 72 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h128 : (s.sp - 128#64).toNat = s.sp.toNat - 128 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus_run
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus_simp [hfv]
  · simp only [G, GoKept, cgoClobber, GoABI.regG, cgoStackScratch, gStructSize, tlsGOffset,
      outside_cons, outside_nil, and_true]
    janus_simp [h72, h128]
    refine ⟨by omega, ?_, by omega, by omega, by omega, by omega⟩
    janus_disch
  rintro s' ⟨-, m, ⟨regs, fl, vr, tp, fs', rfl, hg, hfp⟩, hmf⟩
  simp only [E, r0, r1, fw, cgoClobber, GoABI.regG, GoABI.regFP, cgoStackScratch, gStructSize,
    tlsGOffset, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h72, h128] at hmf hg hfp
  apply ReturnsC.of_reaches
  janus_run [hg, hfp, hax, hay, hbx, hby]
  have hp : prod ax ay bx by_ < 2 ^ 64 := Nat.mod_lt _ (by decide)
  refine ⟨by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow, Nat.mod_mod]

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
    rw [BitVec.eq_of_toNat_eq h1, E, Memory.bytes_writeLE, Memory.bytes_writeLE,
      Memory.bytes_writeLE, Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 1).toNat ≤ c → c + n ≤ (s.regs 1).toNat + 56 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    have hr : r1 t.mem (s.regs 1).toNat = r1 s.mem (s.regs 1).toNat ∧
        r0 t.mem (s.regs 1).toNat = r0 s.mem (s.regs 1).toNat := by
      simp only [r0, r1, fw, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
      rw [hk (s.regs 1).toNat 8 (Nat.le_refl _) (by omega),
        hk ((s.regs 1).toNat + 8) 8 (by omega) (by omega),
        hk ((s.regs 1).toNat + 16) 8 (by omega) (by omega),
        hk ((s.regs 1).toNat + 24) 8 (by omega) (by omega),
        hk ((s.regs 1).toNat + 32) 8 (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    rw [hr.1, hr.2]
    split
    · rfl
    · split
      · rfl
      · have := he.kept b 1 ⟨hbacc, hb'⟩
        simp only [Memory.readLE_one] at this
        exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, _⟩ b _ hna
    have hb1 : ¬ ((s.regs 1).toNat ≤ b ∧ b < (s.regs 1).toNat + 56) := by
      intro ⟨h1, h2⟩
      have := Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
      rw [this] at hna; cases hna
    rw [E, Memory.bytes_writeLE, Memory.bytes_writeLE, if_neg (by omega), if_neg (by omega)]

/-- **`PMix` end to end**, under the trusted `CgoCall` contract only. -/
theorem correctness (ax ay bx by_ n : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [n] (GoPre ax ay bx by_)
      (fun _ s' => (s'.vregs 0).toNat % 2 ^ 64 = prod ax ay bx by_ ∧ s'.regs 0 = n + 1) :=
  (go_spec ax ay bx by_ n).refine refines

end Proof
