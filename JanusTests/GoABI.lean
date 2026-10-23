import Janus

/-! Tests for the Go ABIInternal layer and the specification vocabulary: return addresses
(`RetAddr`, `Program.withExit`), the outcome predicates (`Returns`, `Panics`, `Faults`,
`NeverPanics`) and the stack predicates. -/

namespace JanusTests.GoABI

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-- A function that is a single `ret` (`0xd65f03c0`) at `0x1000`. -/
def retProg : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }

/-- Every call state with any arguments and any admissible return address returns at once,
obeys the ABI, and leaves the argument registers as results. -/
example (x y : W64) :
    EnsuresResults retProg 0x1000 [x, y] 2 (fun _ => True) (fun r => r = [x, y]) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  simp [results_two, h_x0, h_x1]

/-- Admissible return addresses: decided on a concrete program. -/
example : RetAddr retProg 0x2000 := RetAddr.of_check (by decide)
example : RetAddr retProg 0 := RetAddr.of_check (by decide)
example : ¬ RetAddr retProg 0x1000 := fun h => h.ne_of_fetch (pc := 0x1000) (w := 0xd65f03c0) rfl rfl
example : ¬ RetAddr retProg 0x1002 := fun h => by have := h.aligned; omega
example : ¬ RetAddr retProg (2 ^ 56) := fun h => by have := h.user; omega

/-- A program whose entry is a panic stub. -/
def panicProg : Program :=
  { segments := [], stubs := [{ name := "runtime.panicIndex", addr := 0x2000, kind := .panic }],
    exitAddr := 0x1000 }

example (ret : Nat) (hret : RetAddr panicProg ret) (s : State)
    (hs : CallSetup (panicProg.withExit ret) 0x2000 [] s) : Panics (panicProg.withExit ret) s := by
  janus_intro hs
  janus_run

example (ret : Nat) (hret : RetAddr panicProg ret) (s : State)
    (hs : CallSetup (panicProg.withExit ret) 0x2000 [] s) :
    ¬ Returns (panicProg.withExit ret) s (fun _ => True) :=
  Panics.not_returns (by janus_intro hs; janus_run)

/-- `Ensures` implies `NeverPanics`. -/
example (x : W64) (ret : Nat) (hret : RetAddr retProg ret) (s : State)
    (hs : CallSetup (retProg.withExit ret) 0x1000 [x] s) : NeverPanics (retProg.withExit ret) s := by
  have h : Ensures retProg 0x1000 [x] (fun _ => True) (fun _ _ => True) := by
    intro ret hret s hs _; janus_intro hs; janus_run
  exact h.neverPanics hret hs trivial

/-! Faults are not "never panics": `ldr x3, [x1]` (`0xf9400023`) with `x1 = 0` (a nil pointer)
and no memory faults, which Go reports as a nil-dereference panic. -/

def nilProg : Program where
  segments := [⟨"f", 0x1000, [0xf9400023, 0xd65f03c0]⟩]
  stubs := []
  exitAddr := 0

theorem nil_faults (ret : Nat) (s : State) (hs : CallSetup (nilProg.withExit ret) 0x1000 [0, 0] s)
    (hm : s.mem.regions = []) (hr : ret ≠ 0x1000) : Faults (nilProg.withExit ret) s := by
  have hpc : s.pc.toNat = 0x1000 := hs.pc_toNat (by decide)
  have hx1 : s.regs 1 = 0 := hs.reg (i := 1) (by simp)
  refine faults_of_steps (w := 0xf9400023) (e := .outsideAllocation 0 8) (.refl s) (by rw [hpc]; exact hr.symm)
    (by rw [hpc]; rfl) (by rw [hpc]; rfl) ?_ (by decide)
  rw [Arm64.step_of_decode (i := .ldstUImm 3 1 0 1 3) (by decide)]
  simp [Arm64.exec, Arm64.memIndexed, Arm64.baseAddr, Arm64.memSingle, Arm64.load,
    Memory.accessible, hm, hx1]

example (ret : Nat) (s : State) (hs : CallSetup (nilProg.withExit ret) 0x1000 [0, 0] s)
    (hm : s.mem.regions = []) (hr : ret ≠ 0x1000) : ¬ NeverPanics (nilProg.withExit ret) s :=
  fun h => h.not_faults (nil_faults ret s hs hm hr)

/-- `CallSetup` is satisfiable from any state, for any return address. -/
example (s : State) (a b c : W64) (ret : Nat) :
    CallSetup (retProg.withExit ret) 0x84500 [a, b, c] (setup (retProg.withExit ret) 0x84500 [a, b, c] s) :=
  setup_callSetup s (by simp [numIntRegs])

example (s : State) (a b : W64) (hs : CallSetup (retProg.withExit 0x2000) 0x84500 [a, b] s) :
    s.regs 1 = b ∧ (s.regs 30).toNat = 0x2000 :=
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
