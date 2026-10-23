import Janus.GoABI

/-! Tests for the Go ABIInternal layer and the specification vocabulary. These use only
ISA-independent facts (exit address and stubs), so they do not depend on `step`. -/

namespace JanusTests.GoABI

open Janus Janus.Arm64 Janus.GoABI

/-- A degenerate program whose entry is its exit address: the call returns immediately. -/
def idProg : Program := { segments := [], stubs := [], exitAddr := 0x1000 }

/-- Every call state with any arguments returns at once, obeys the ABI, and leaves the
argument registers as results. Quantifies over all call states, not one zeroed state. -/
example (x y : W64) :
    EnsuresResults idProg 0x1000 [x, y] 2 (fun _ => True) (fun r => r = [x, y]) := by
  intro s hs _
  refine returns_of_steps (.refl s) ?_ ⟨ABIReturn.refl s, ?_⟩
  · rw [hs.pc_toNat (by decide)]; rfl
  · simp [results_two, hs.reg (i := 0) (by simp), hs.reg (i := 1) (by simp)]

/-- A program whose entry is a panic stub. -/
def panicProg : Program :=
  { segments := [], stubs := [{ name := "runtime.panicIndex", addr := 0x2000, kind := .panic }],
    exitAddr := 0x1000 }

example (s : State) (hs : CallSetup panicProg 0x2000 [] s) : Panics panicProg s := by
  refine panics_of_steps (st := panicProg.stubs[0]) (.refl s) ?_ ?_ rfl <;>
    rw [hs.pc_toNat (by decide)] <;> first | decide | rfl

example (s : State) (hs : CallSetup panicProg 0x2000 [] s) : ¬ Returns panicProg s (fun _ => True) :=
  Panics.not_returns (by
    refine panics_of_steps (st := panicProg.stubs[0]) (.refl s) ?_ ?_ rfl <;>
      rw [hs.pc_toNat (by decide)] <;> first | decide | rfl)

/-- `Ensures` implies `NeverPanics`. -/
example (x : W64) (s : State) (hs : CallSetup idProg 0x1000 [x] s) : NeverPanics idProg s := by
  have h : Ensures idProg 0x1000 [x] (fun _ => True) (fun _ _ => True) := fun s hs _ =>
    returns_of_steps (.refl s) (by rw [hs.pc_toNat (by decide)]; rfl) ⟨ABIReturn.refl s, trivial⟩
  exact h.neverPanics hs trivial

/-- `CallSetup` is satisfiable from any state. -/
example (s : State) (a b c : W64) : CallSetup idProg 0x84500 [a, b, c] (setup idProg 0x84500 [a, b, c] s) :=
  setup_callSetup s (by simp [numIntRegs])

example (s : State) (a b : W64) (hs : CallSetup idProg 0x84500 [a, b] s) :
    s.regs 1 = b ∧ (s.regs 30).toNat = 0x1000 :=
  ⟨hs.reg (by simp), hs.lr_toNat (by decide)⟩

/-! Results. -/
example (s : State) : results 3 s = [s.regs 0, s.regs 1, s.regs 2] := rfl
example (s : State) : (results 16 s).length = 16 := by simp

/-! Stack guard on a concrete g / stack layout. -/

/-- `g` at 0x5000 with `stackguard0 = 0x8000` (byte 1 = 0x80); `SP = 0x9000`. -/
def gState : State :=
  { regs := fun i => if i = 28 then 0x5000 else 0
    sp := 0x9000
    pc := 0x84500
    flags := ⟨false, false, false, false⟩
    mem := ⟨fun a => if a = 0x5011 then 0x80 else 0, [⟨0x5000, 0x100, true⟩, ⟨0x8000, 0x1000, true⟩]⟩ }

example : stackguard0 gState = 0x8000 := by decide

example : StackGuardOK gState 0 :=
  ⟨by decide, by decide, by decide⟩

/-- The medium-frame form `SUB $k, RSP, R17` with `k = 0x400` still falls through. -/
example : StackGuardOK gState 0x400 := ⟨by decide, by decide, by decide⟩
example : ¬ StackGuardOK gState 0x1000 := fun h => by have := h.below; revert this; decide

example : (gState.sp - BitVec.ofNat 64 0x400).toNat = 0x9000 - 0x400 :=
  StackGuardOK.sub_toNat (s := gState) ⟨by decide, by decide, by decide⟩

example : prologueAdj 16048 = 15920 := rfl
example : prologueAdj 32 = 0 := rfl

example : StackWritable gState 0x1000 0 := ⟨by decide, by decide⟩
example : SPAligned gState := by unfold SPAligned; decide

end JanusTests.GoABI
