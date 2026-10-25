import Extracted

/-!
# `Add(x, y uint64) uint64` (Go) → `c_add` (C) → back to Go, end to end (arm64)

```go
func Add(x, y uint64) uint64 { return uint64(C.c_add(C.uint64_t(x), C.uint64_t(y))) }
```

**Guarantee (`correctness`).** For all 64-bit `x` and `y` and every Go call of
`example.com/cgo.Add` satisfying `GoPre` — the stack-growth checks of `Add` and `_Cfunc_c_add`
fall through (`GuardOK s 48`), 112 bytes of stack below `SP` are writable, the cgo function-pointer
variable holds the address of the C wrapper and `runtime.cgoAlwaysFalse` is false (both are
statically initialised globals no code writes), and the `g` struct, the TLS `g` slot and those
globals are not on the stack — every run returns to the caller, restores `SP`, `g` and the frame
pointer, and leaves `(x + y) mod 2^64` in `X0`.

The statement is under `CgoCall Extracted.program`, the **trusted** contract of `runtime.cgocall`
(`Janus.FFI`): the Go code (`Add`, `_Cfunc_c_add`), the C wrapper and `c_add` are all executed by
the model from the bytes of the binary; only the stack and scheduler switch of `cgocall` (and the
value of `_cgo_topofstack`) are assumed, as `CgoCall` and `TopOfStack` state them.

**How.**
1. `wrapper_spec`: the cgo wrapper `_cgo_<hash>_Cfunc_c_add(frame)` (C, AAPCS64) under the
   `TopOfStack T` contract for every `T`: it returns with `X19`–`X29` and `SP` restored, and its
   only write outside its stack is `p0 + p1` into the frame's result slot (`WPost`).
2. `go_spec`: `Add` under the Go-side assumption `CgoSpec wrapper G E`: "`cgocall` of the wrapper
   with a frame that is Go memory (`G`) returns with the result slot set (`E`)".
3. `refines`: `CgoCall.refines` turns 1 into "the trusted contract implies the assumption of 2",
   and `correctness` is 2 under the trusted contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.Spec Janus.FFI

namespace Proof

/-- The cgo wrapper `_cgo_<hash>_Cfunc_c_add(void *frame)`, which `cgocall` calls on the system
stack. -/
abbrev wrapper : Nat := segAddr Extracted.program "_cgo_2306a0143858_Cfunc_c_add"

/-- The cgo argument frame of `c_add` at `a`: `p0` at `a`, `p1` at `a + 8`, the result at
`a + 16`. -/
def addFrameResult (m : Memory) (a : Nat) : Nat := (m.readLE a 8 + m.readLE (a + 8) 8) % 2 ^ 64

/-- What the wrapper needs: its stack (the system stack), and the frame writable and away from
it. -/
def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 0 ∧ a.toNat + 24 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 24 true = true ∧
    (a.toNat + 24 ≤ t.sp.toNat - 4096 ∨ t.sp.toNat ≤ a.toNat)

/-- What the wrapper does: stores `p0 + p1` in the result slot; besides that it only writes its
stack. -/
def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 16) 8 (addFrameResult t.mem a.toNat)) t'.mem
    [(t.sp.toNat - 4096, t.sp.toNat)]

theorem wrapper_spec (T a : BitVec 64) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd⟩
  apply ReturnsC.of_reaches
  janus_intro hs.call
  simp only [Nat.add_zero] at htop hacc
  janus_run
  -- first `bl _cgo_topofstack`: the contract
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₁ ⟨-, f₁, m₁, rfl, hm₁⟩
  apply ReturnsC.of_reaches
  janus_run
  -- second `bl _cgo_topofstack`
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₂ ⟨-, f₂, m₂, rfl, hm₂⟩
  apply ReturnsC.of_reaches
  janus_run
  -- the result: one store into the frame, and the stack frames of the wrapper and the callees
  simp only [WPost, addFrameResult, Nat.reducePow, writeLE_mod_8]
  have hT : (18446744073709551616 - T.toNat + T.toNat) % 18446744073709551616 = 0 := by
    have := T.isLt; omega
  simp only [hT, Nat.add_zero]
  dsimp only at hm₁ hm₂
  have h48 : (t.sp - 48#64).toNat = t.sp.toNat - 48 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  rw [h48] at hm₁ hm₂
  have hf : MemFrame t.mem m₂ [(t.sp.toNat - 4096, t.sp.toNat)] := by
    refine MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)])
      (MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)]) ?_ hm₁ ?_) hm₂ ?_
    · janus_frame
    all_goals intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  exact hf.writeLE_both _ _ _

/-! ## The Go side: `Add` → `_Cfunc_c_add` → `runtime.cgocall` -/

/-- The cgo function-pointer variable `example.com/cgo._cgo_<hash>_Cfunc_c_add` (`.data`), read
by `ADRP`+`LDR` at `_Cfunc_c_add+0x24`: it holds the address of the C wrapper. -/
def fnVar : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo._Cfunc_c_add.abi0" + 0x24)
    (segWord Extracted.program "example.com/cgo._Cfunc_c_add.abi0" 9)
    (segWord Extracted.program "example.com/cgo._Cfunc_c_add.abi0" 10) 3

/-- `runtime.cgoAlwaysFalse` (`.noptrbss`), the byte behind cgo's `if _Cgo_always_false`, read
by `ADRP`+`LDRB` at `_Cfunc_c_add+0x30`. -/
def alwaysFalse : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo._Cfunc_c_add.abi0" + 0x30)
    (segWord Extracted.program "example.com/cgo._Cfunc_c_add.abi0" 12)
    (segWord Extracted.program "example.com/cgo._Cfunc_c_add.abi0" 13) 0

/-- What the Go side needs at the `cgocall`: the argument frame `X1` is Go memory the runtime
leaves alone. -/
def G (s : State) : Prop := (s.regs 1).toNat + 24 ≤ 2 ^ 48 ∧ GoKept s (s.regs 1).toNat 24 true

/-- The effect the Go side assumes of the C call: the frame's result slot gets `p0 + p1`. -/
def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 1).toNat + 16) 8 (addFrameResult s.mem (s.regs 1).toNat)

/-- The Go caller's precondition. -/
def GoPre (s : State) : Prop :=
  GuardOK s 48 ∧ StackOK s 112 0 ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 % 2 = 0 ∧
  -- the `g` struct and the TLS `g` slot are not on this stack; the globals are elsewhere
  Outside (s.regs 28).toNat 456 [(s.sp.toNat - 112, s.sp.toNat)] ∧
  Outside (s.tpidr.toNat + 16) 8 [(s.sp.toNat - 112, s.sp.toNat)] ∧
  Outside fnVar 8 [(s.sp.toNat - 112, s.sp.toNat)] ∧
  Outside alwaysFalse 1 [(s.sp.toNat - 1120, s.sp.toNat), ((s.regs 28).toNat, (s.regs 28).toNat + 456),
    (s.tpidr.toNat + 16, s.tpidr.toNat + 24)]

theorem go_spec (x y : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [x, y] GoPre
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, htop, hst⟩, hfa, hfv, haa, hav, hdg, hdt, hdf, hda⟩
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
  rintro s' ⟨-, m, ⟨regs, fl, vr, tp, fs, rfl, hg, hfp⟩, hmf⟩
  simp only [E, addFrameResult, cgoClobber, GoABI.regG, GoABI.regFP, cgoStackScratch, gStructSize,
    tlsGOffset, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h40, h96] at hmf hg hfp
  apply ReturnsC.of_reaches
  janus_run [hg, hfp]

/-! ## Composition: the C wrapper's theorem discharges the assumption -/

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · -- the wrapper's precondition, from the trusted facts about the C call state
    rintro s t ret ⟨hb, hacc, hout⟩ he
    have hsep := he.stackSep _ _ _ hacc
    simp only [outside_cons, outside_nil, and_true] at hsep
    exact ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩, by have := hsep; unfold cgoCStack at this; omega⟩
  · intro s _; rfl
  · -- on Go memory the C state's final memory is `E s`
    rintro s t ret t' ⟨hb, hacc, hout⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by simpa [cgoCStack] using hsep)
    simp only [Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Memory.bytes_writeLE, Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 1).toNat ≤ c → c + n ≤ (s.regs 1).toNat + 24 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    split
    · simp only [addFrameResult, hk _ 8 (Nat.le_refl _) (by omega),
        hk ((s.regs 1).toNat + 8) 8 (by omega) (by omega)]
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · -- bytes that are not Go memory are not touched by `E`
    rintro s ⟨hb, hacc, hout⟩ b _ hna
    rw [E, Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`Add` end to end.** -/
theorem correctness (x y : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [x, y] GoPre
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) :=
  (go_spec x y).refine refines

end Proof
