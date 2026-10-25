import Extracted

/-!
# `Stack10(a, b, c, d, e, f, g, h int64, i int32, j int64) int64` (Go) → `k_stack10` (C, ten
# arguments, two on the stack) → back to Go, end to end (arm64)

```go
func Stack10(a, b, c, d, e, f, g, h int64, i int32, j int64) int64 {
	return int64(C.k_stack10(C.int64_t(a), …, C.int32_t(i), C.int64_t(j)))
}
```

**Guarantee (`correctness`).** For all `a … h`, `j` and 32-bit `i`, every Go call of
`example.com/cgo/cabi.Stack10` satisfying `GoPre` (the stack checks fall through, 160 bytes of
stack below `SP` are writable, the cgo globals hold their static values and are not on the
stack, the `g` struct and the TLS `g` slot are not on the stack) returns, restores `SP`, `g` and
the frame pointer, and leaves `a + 2b + … + 9i + 10j` (mod 2^64, `i` sign-extended) in `X0`,
under the trusted `CgoCall` contract only.

**How.** The C wrapper `_cgo_<hash>_Cfunc_k_stack10` loads the ten arguments from the cgo frame
and calls `k_stack10` with the AAPCS64 calling convention: `wrapper_spec` uses the callee
contract `summary` of `k_stack10` (as in `KStack10.lean`), whose precondition is Janus's
classification of the prototype (`ArgsAt … sig.passing`: `X0`–`X7`, then `i` in the low half
of `[SP]` and `j` at `[SP + 8]`); `janus_run` proves it at the wrapper's call site, so the code
gcc generated for the call is checked against the classification. `go_spec`, `refines` and
`correctness` are as in `GoAdd.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.Spec Janus.FFI Janus.C

namespace Proof

/-! ## The C function `k_stack10` (as in `KStack10.lean`), as a callee summary -/

abbrev ks : Nat := segAddr Extracted.program "k_stack10"

/-- The prototype. -/
def sig : AAPCS64.Sig :=
  ⟨some (.int 8 true), List.replicate 8 (.int 8 true) ++ [.int 4 true, .int 8 true], none⟩

/-- Where Janus's classification puts the arguments. -/
theorem passing : sig.passing =
    ((List.range 8).map fun r => .direct [⟨0, 8, .gpr r⟩]) ++
      [.direct [⟨0, 4, .stack 0⟩], .direct [⟨0, 8, .stack 8⟩]] := by decide

/-- The result is `X0`. -/
theorem result : AAPCS64.result (.int 8 true) = .direct [⟨0, 8, .gpr 0⟩] := by decide

/-- The specification. -/
def spec (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) : BitVec 64 :=
  a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9 * i.signExtend 64 + 10 * j

/-- The argument values of the call `k_stack10(a, …, j)`. -/
def vals (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) : List Nat :=
  [a, b, c, d, e, f, g, h].map BitVec.toNat ++ [i.toNat, j.toNat]

/-- What `k_stack10` needs (the callee contract's precondition): its arguments where the
classification puts them, an aligned `SP` and a return address. -/
def SPre (vs : List Nat) (s : State) : Prop :=
  ArgsAt s sig.args vs sig.passing ∧ s.sp.toNat % 16 = 0 ∧ (s.regs 30).toNat % 4 = 0 ∧
    (s.regs 30).toNat < 2 ^ 56

/-- `SPre` with the classification evaluated: the equations a call site has to establish. -/
theorem spre_iff (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) (s : State) :
    SPre (vals a b c d e f g h i j) s ↔
      s.regs 0 = a ∧ s.regs 1 = b ∧ s.regs 2 = c ∧ s.regs 3 = d ∧ s.regs 4 = e ∧ s.regs 5 = f ∧
      s.regs 6 = g ∧ s.regs 7 = h ∧
      (s.sp.toNat + 4 ≤ 2 ^ 48 ∧ s.mem.accessible s.sp.toNat 4 false = true ∧
        s.mem.readLE s.sp.toNat 4 = i.toNat) ∧
      (s.sp.toNat + 8 + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat + 8) 8 false = true ∧
        s.mem.readLE (s.sp.toNat + 8) 8 = j.toNat) ∧
      s.sp.toNat % 16 = 0 ∧ (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 := by
  unfold SPre
  rw [passing]
  simp only [vals, sig, List.map, List.range, List.range.loop, List.cons_append, List.nil_append,
    ArgsAt, ArgAt, PiecesAt, and_true, List.replicate, pieceAt_gpr_word, pieceAt_stack_word]
  simp only [PieceAt, bytesOf, Nat.pow_zero, Nat.div_one, Nat.add_zero, Nat.reducePow,
    Nat.mod_eq_of_lt i.isLt, and_assoc]

/-- What it guarantees, as plain equations (for a caller's `janus_run`). -/
abbrev SPost (r : BitVec 64) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 19 = s.regs 19 ∧ s'.regs 20 = s.regs 20 ∧ s'.regs 21 = s.regs 21 ∧
    s'.regs 22 = s.regs 22 ∧ s'.regs 23 = s.regs 23 ∧ s'.regs 24 = s.regs 24 ∧
    s'.regs 25 = s.regs 25 ∧ s'.regs 26 = s.regs 26 ∧ s'.regs 27 = s.regs 27 ∧
    s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.fpcr = s.fpcr ∧ s'.vregs = s.vregs ∧
    s'.mem = s.mem ∧ s'.regs 0 = r

/-- The callee contract of `k_stack10`. -/
theorem summary (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) :
    Summary Extracted.program ks (SPre (vals a b c d e f g h i j))
      (SPost (spec a b c d e f g h i j)) := by
  intro s hpc hpre
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, ⟨hib, hia, hi⟩, ⟨hjb, hja, hj⟩, hal, hlra, hlrb⟩ :=
    (spre_iff a b c d e f g h i j s).1 hpre
  janus_run
  simp only [SPost, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, true_and]
  rw [hi, hj]
  have hw : BitVec.setWidth 32 (BitVec.ofNat 64 i.toNat) = i := by
    apply BitVec.eq_of_toNat_eq; simp
  have hse : BitVec.ofInt 64 i.toInt = i.signExtend 64 := by
    rw [← BitVec.toInt_signExtend_of_le (x := i) (v := 64) (by decide), BitVec.ofInt_toInt]
  rw [hw, BitVec.ofInt_add, BitVec.ofInt_mul, hse, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [spec, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, BitVec.reduceToNat, Nat.add_mod_mod, Nat.mod_add_mod,
    Nat.mod_mul_mod, show (BitVec.ofInt 64 9).toNat = 9 from rfl]
  generalize (i.signExtend 64).toNat = I
  omega


/-! ## The cgo wrapper -/

abbrev wrapper : Nat := segAddr Extracted.program "_cgo_a66fe0e77ed3_Cfunc_k_stack10"

/-- The cgo argument frame at `a`: `p0`–`p7` at `a + 8k`, `p8` (32-bit) at `a + 64`, `p9` at
`a + 72`, the result at `a + 80`. -/
def fw (m : Memory) (a k : Nat) : BitVec 64 := BitVec.ofNat 64 (m.readLE (a + 8 * k) 8)
def fi (m : Memory) (a : Nat) : BitVec 32 := BitVec.ofNat 32 (m.readLE (a + 64) 4)

/-- The result the wrapper stores. -/
def res (m : Memory) (a : Nat) : Nat :=
  (spec (fw m a 0) (fw m a 1) (fw m a 2) (fw m a 3) (fw m a 4) (fw m a 5) (fw m a 6) (fw m a 7)
    (fi m a) (fw m a 9)).toNat

def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 0 ∧ a.toNat + 88 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 88 true = true ∧
    (a.toNat + 88 ≤ t.sp.toNat - 4096 ∨ t.sp.toNat ≤ a.toNat)

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 80) 8 (res t.mem a.toNat)) t'.mem
    [(t.sp.toNat - 4096, t.sp.toNat)]

theorem wrapper_spec (T a : BitVec 64) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd⟩
  apply ReturnsC.of_reaches
  janus_intro hs.call
  simp only [Nat.add_zero] at htop hacc
  janus_run
  -- first `bl _cgo_topofstack`
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₁ ⟨-, f₁, m₁, rfl, hm₁⟩
  apply ReturnsC.of_reaches
  janus_run [spre_iff, fw, fi, BitVec.toNat_ofNat] calls [summary (fw t.mem a.toNat 0) (fw t.mem a.toNat 1) (fw t.mem a.toNat 2)
    (fw t.mem a.toNat 3) (fw t.mem a.toNat 4) (fw t.mem a.toNat 5) (fw t.mem a.toNat 6)
    (fw t.mem a.toNat 7) (fi t.mem a.toNat) (fw t.mem a.toNat 9)]
  -- second `bl _cgo_topofstack`
  have h64 : (t.sp - 64#64).toNat = t.sp.toNat - 64 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp [h64]
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₂ ⟨-, f₂, m₂, rfl, hm₂⟩
  dsimp only at hm₁ hm₂
  try rw [h64] at hm₂
  apply ReturnsC.of_reaches
  janus_run
  refine ⟨?_, ?_⟩
  · have hv : s'.vregs = t.vregs := by assumption
    simp only [hv, and_self]
  simp only [WPost, res, fw, fi, Nat.reducePow, writeLE_mod_8, Nat.mul_zero, Nat.add_zero,
    Nat.reduceMul]
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

/-! ## The Go side: `Stack10` → `_Cfunc_k_stack10` → `runtime.cgocall` -/

/-- The cgo function-pointer variable (`ADRP`+`LDR` at `_Cfunc_k_stack10+0x24`). -/
def fnVar : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_stack10.abi0" + 0x24)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_stack10.abi0" 9)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_stack10.abi0" 10) 3

/-- `runtime.cgoAlwaysFalse` (`ADRP`+`LDRB` at `_Cfunc_k_stack10+0x30`). -/
def alwaysFalse : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_stack10.abi0" + 0x30)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_stack10.abi0" 12)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_stack10.abi0" 13) 0

/-- At the `cgocall`: the 88-byte frame `X1` is Go memory the runtime leaves alone. -/
def G (s : State) : Prop := (s.regs 1).toNat + 88 ≤ 2 ^ 48 ∧ GoKept s (s.regs 1).toNat 88 true

/-- The effect the Go side assumes: the frame's result slot gets the weighted sum. -/
def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 1).toNat + 80) 8 (res s.mem (s.regs 1).toNat)

def GoPre (s : State) : Prop :=
  GuardOK s 112 ∧ StackOK s 176 0 ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 % 2 = 0 ∧
  Outside (s.regs 28).toNat 456 [(s.sp.toNat - 176, s.sp.toNat)] ∧
  Outside (s.tpidr.toNat + 16) 8 [(s.sp.toNat - 176, s.sp.toNat)] ∧
  Outside fnVar 8 [(s.sp.toNat - 176, s.sp.toNat)] ∧
  Outside alwaysFalse 1 [(s.sp.toNat - 1184, s.sp.toNat), ((s.regs 28).toNat, (s.regs 28).toNat + 456),
    (s.tpidr.toNat + 16, s.tpidr.toNat + 24)]

set_option maxHeartbeats 4000000 in
theorem go_spec (a b c d e f g h i j : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [a, b, c, d, e, f, g, h, i, j]
      GoPre (fun _ s' => s'.regs 0 = spec a b c d e f g h (i.setWidth 32) j) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, htop, hst⟩, hfa, hfv, haa, hav, hdg, hdt, hdf, hda⟩
  apply ReturnsC.of_reaches
  janus_intro hs
  janus_eval_nat h_fv : fnVar
  janus_eval_nat h_af : alwaysFalse
  rw [h_fv] at hfa hfv hdf
  rw [h_af] at haa hav hda
  simp only [outside_cons, outside_nil, and_true, Nat.add_zero] at *
  have h104 : (s.sp - 104#64).toNat = s.sp.toNat - 104 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h160 : (s.sp - 160#64).toNat = s.sp.toNat - 160 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus_run
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus_simp [hfv]
  · simp only [G, GoKept, cgoClobber, GoABI.regG, cgoStackScratch, gStructSize, tlsGOffset,
      outside_cons, outside_nil, and_true]
    janus_simp [h104, h160]
    refine ⟨by omega, ?_, by omega, by omega, by omega, by omega⟩
    janus_disch
  rintro s' ⟨-, m, ⟨regs, fl, vr, tp, fs, rfl, hg, hfp⟩, hmf⟩
  simp only [E, res, fw, fi, cgoClobber, GoABI.regG, GoABI.regFP, cgoStackScratch, gStructSize,
    tlsGOffset, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h104, h160] at hmf hg hfp
  apply ReturnsC.of_reaches
  janus_run [hg, hfp]
  have hw : BitVec.ofNat 32 (i.toNat % 4294967296) = BitVec.setWidth 32 i := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.reducePow, Nat.mod_mod]
  rw [hw]

/-! ## Composition: the C wrapper's theorem discharges the assumption -/

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · rintro s t ret ⟨hb, hacc, hout⟩ he
    have hsep := he.stackSep _ _ _ hacc
    simp only [outside_cons, outside_nil, and_true] at hsep
    exact ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩, by have := hsep; unfold cgoCStack at this; omega⟩
  · intro s _; rfl
  · rintro s t ret t' ⟨hb, hacc, hout⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by simpa [cgoCStack] using hsep)
    simp only [Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Memory.bytes_writeLE, Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 1).toNat ≤ c → c + n ≤ (s.regs 1).toNat + 88 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    split
    · simp only [res, fw, fi, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
      rw [hk _ 8 (Nat.le_refl _) (by omega), hk (_ + 8) 8 (by omega) (by omega),
        hk (_ + 16) 8 (by omega) (by omega), hk (_ + 24) 8 (by omega) (by omega),
        hk (_ + 32) 8 (by omega) (by omega), hk (_ + 40) 8 (by omega) (by omega),
        hk (_ + 48) 8 (by omega) (by omega), hk (_ + 56) 8 (by omega) (by omega),
        hk (_ + 64) 4 (by omega) (by omega), hk (_ + 72) 8 (by omega) (by omega)]
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, hacc, hout⟩ b _ hna
    rw [E, Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`Stack10` end to end**, under the trusted `CgoCall` contract only. -/
theorem correctness (a b c d e f g h i j : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [a, b, c, d, e, f, g, h, i, j]
      GoPre (fun _ s' => s'.regs 0 = spec a b c d e f g h (i.setWidth 32) j) :=
  (go_spec a b c d e f g h i j).refine refines

end Proof
