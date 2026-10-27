import Extracted

/-!
# `Add(x, y uint64) uint64` (Go) → `c_add` (C) → back to Go, end to end (amd64)

```go
func Add(x, y uint64) uint64 { return uint64(C.c_add(C.uint64_t(x), C.uint64_t(y))) }
```

**Guarantee (`correctness`).** For all 64-bit `x` and `y` and every Go call of
`example.com/cgo.Add` satisfying `GoPre` — the stack-growth checks of `Add` and `_Cfunc_c_add`
fall through (`StackGuardOK s 40`), 80 bytes of stack below `RSP` (and the return address) are
writable, the TLS `g` slot holds `g` (`TlsG`), the cgo function-pointer variable holds the address
of the C wrapper and `runtime.cgoAlwaysFalse` is 0 (statically initialised globals no code
writes), and the `g` struct, the TLS slot and those globals are not on the stack — every run
returns to the caller, restores `RSP + 8`, `RBP`, `R14` and `X15` (`ABIReturn`), and leaves
`(x + y) mod 2^64` in `RAX`.

The statement is under `CgoCall Extracted.program`, the **trusted** contract of `runtime.cgocall`
(`Janus.Amd64.FFI`): the Go code, the C wrapper and `c_add` are executed by the model from the
bytes of the binary; only the stack and scheduler switch of `cgocall` (and the value of
`_cgo_topofstack`) are assumed, as `CgoCall` and `TopOfStack` state them. After the call the Go
code reloads `R14` from `FS:-8`, which `cgocall`'s contract guarantees holds `g` on whatever
thread the goroutine resumes.

**How.** `wrapper_spec` (the C wrapper under `TopOfStack T`, for every `T`), `go_spec` (`Add`
under the Go-side assumption `CgoSpec wrapper G E`), `refines` (`CgoCall.refines` with 1), and
`correctness` = 2 under the trusted contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Spec
  Janus.Amd64.FFI

namespace Proof

/-- The cgo wrapper `_cgo_<hash>_Cfunc_c_add(void *frame)`, which `cgocall` calls on the system
stack. -/
abbrev wrapper : Nat := segAddr Extracted.program "_cgo_ad79fd856801_Cfunc_c_add"

/-- The result of the cgo argument frame of `c_add` at `a`: `p0 + p1` (`p0` at `a`, `p1` at
`a + 8`; the result slot is `a + 16`). -/
def addFrameResult (m : Memory) (a : Nat) : Nat := (m.readLE a 8 + m.readLE (a + 8) 8) % 2 ^ 64

/-- What the wrapper needs: its stack (the system stack) and the frame, writable and away from
it. -/
def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 8 ∧ a.toNat + 24 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 24 true = true ∧
    (a.toNat + 24 ≤ (t.regs 4).toNat - 4096 ∨ (t.regs 4).toNat + 8 ≤ a.toNat)

/-- What the wrapper does: stores `p0 + p1` in the result slot; otherwise it only writes the
stack below `RSP`. -/
def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 16) 8 (addFrameResult t.mem a.toNat)) t'.mem
    [((t.regs 4).toNat - 4096, (t.regs 4).toNat)]

theorem wrapper_spec (T a : BitVec 64) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd⟩
  apply ReturnsC.of_reaches
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : t.regs 7 = a := hs.reg (i := 0) (by simp)
  simp only [Amd64.Program.withExit] at h_ret
  simp only [CABI.regSP] at hal hb htop hacc
  have h32 : (t.regs 4 - 32#64).toNat = (t.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run
  -- first `call _cgo_topofstack`: the contract
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h32]; omega
  · janus64_simp [h32]; janus64_disch
  rintro s₁ ⟨-, f₁, rfl⟩
  apply ReturnsC.of_reaches
  janus64_run
  -- second `call _cgo_topofstack`
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h32]; omega
  · janus64_simp [h32]; janus64_disch
  rintro s₂ ⟨-, f₂, rfl⟩
  apply ReturnsC.of_reaches
  janus64_run
  -- the result: one store into the frame, besides the wrapper's pushes and return addresses
  simp only [WPost, addFrameResult, Nat.reducePow, writeLE_mod_8]
  apply Janus.MemFrame.writeLE_both
  janus_frame

/-! ## The Go side: `Add` → `_Cfunc_c_add` → `runtime.cgocall` -/

/-- The cgo function-pointer variable `example.com/cgo._cgo_<hash>_Cfunc_c_add` (`.data`), the
RIP-relative operand of `MOVQ …(SB), AX` at `_Cfunc_c_add+0x2e`; it holds the C wrapper's
address. -/
def fnVar : Nat := ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo._Cfunc_c_add.abi0" + 0x2e)

/-- `runtime.cgoAlwaysFalse` (`.noptrbss`), the byte compared at `_Cfunc_c_add+0x47`. -/
def alwaysFalse : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo._Cfunc_c_add.abi0" + 0x47)

/-- What the Go side needs at the `cgocall`: the argument frame `RBX` is Go memory the runtime
leaves alone. -/
def G (s : State) : Prop := (s.regs 3).toNat + 24 ≤ 2 ^ 48 ∧ GoKept s (s.regs 3).toNat 24 true

/-- The effect the Go side assumes of the C call: the frame's result slot gets `p0 + p1`. -/
def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 3).toNat + 16) 8 (addFrameResult s.mem (s.regs 3).toNat)

/-- The Go caller's precondition. -/
def GoPre (s : State) : Prop :=
  StackGuardOK s 40 ∧ StackWritable s 80 8 ∧ TlsG s ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 = 0 ∧
  -- the `g` struct and the TLS `g` slot are not on this stack; the globals are elsewhere
  Outside (s.regs 14).toNat 456 [((s.regs 4).toNat - 80, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat - 8) 8 [((s.regs 4).toNat - 80, (s.regs 4).toNat + 8)] ∧
  Outside fnVar 8 [((s.regs 4).toNat - 80, (s.regs 4).toNat + 8)] ∧
  Outside alwaysFalse 1 [((s.regs 4).toNat - 1104, (s.regs 4).toNat + 8),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)]

set_option maxHeartbeats 2000000 in
theorem go_spec (x y : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [x, y] GoPre
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, htop, hst⟩, ⟨hfs, hfsr, hfsg⟩, hfa, hfv, haa, hav, hdg,
    hdt, hdf, hda⟩
  apply ReturnsC.of_reaches
  janus64_intro hs
  janus_eval_nat h_fv : fnVar
  janus_eval_nat h_af : alwaysFalse
  rw [h_fv] at hfa hfv hdf
  rw [h_af] at haa hav hda
  simp only [outside_cons, outside_nil, and_true, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG, stackguard0, stackguard0Offset] at *
  have hfsa : (s.fsBase + BitVec.ofNat 64 18446744073709551608).toNat = s.fsBase.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h32 : (s.regs 4 - 32#64).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h80 : (s.regs 4 - 80#64).toNat = (s.regs 4).toNat - 80 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run [hfsa]
  refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
  · simp only [G, GoKept, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
      cgoStackScratch, gStructSize, outside_cons, outside_nil, and_true]
    janus64_simp [h32, h80]
    refine ⟨by omega, ?_, by omega, by omega, by omega, by omega⟩
    janus64_disch
  rintro s' ⟨-, m, ⟨regs, fl, xm, yh, fs, mx, x87, zh, kr, rfl, h4, h5, h14, h15, ⟨⟨hfs1, hfs2⟩, hfsr', hfsg'⟩, -⟩, hmf⟩
  simp only [E, addFrameResult, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
    Janus.Amd64.GoABI.regFP, Janus.Amd64.GoABI.xmmZero, cgoStackScratch, gStructSize, setRegF,
    ↓reduceIte, Nat.reduceEqDiff, h32, h80] at hmf h4 h5 h14 h15 hfs1 hfs2 hfsr' hfsg'
  have hfsa' : (fs + BitVec.ofNat 64 18446744073709551608).toNat = fs.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [hmf.accessible] at hfsr'
  simp only [Janus.Arm64.Memory.accessible_writeLE] at hfsr'
  apply ReturnsC.of_reaches
  janus64_run [h4, h5, h14, h15, hfsa', hfsg']

/-! ## Composition: the C wrapper's theorem discharges the assumption -/

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · -- the wrapper's precondition, from the trusted facts about the C call state
    rintro s t ret ⟨hb, hacc, hout⟩ he
    have hsep := he.stackSep _ _ _ hacc
    simp only [outside_cons, outside_nil, and_true, Janus.Amd64.GoABI.regSP] at hsep
    exact ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩, by have := hsep; unfold cgoCStack at this; omega⟩
  · intro s _; rfl
  · -- on Go memory the C state's final memory is `E s`
    rintro s t ret t' ⟨hb, hacc, hout⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by
      simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep ⊢; omega)
    simp only [Janus.Arm64.Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Janus.Arm64.Memory.bytes_writeLE, Janus.Arm64.Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 3).toNat ≤ c → c + n ≤ (s.regs 3).toNat + 24 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    split
    · simp only [addFrameResult, hk _ 8 (Nat.le_refl _) (by omega),
        hk ((s.regs 3).toNat + 8) 8 (by omega) (by omega)]
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · -- bytes that are not Go memory are not touched by `E`
    rintro s ⟨hb, hacc, hout⟩ b _ hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`Add` end to end.** -/
theorem correctness (x y : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [x, y] GoPre
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) :=
  (go_spec x y).refine refines

end Proof
