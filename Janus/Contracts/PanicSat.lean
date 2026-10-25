import Janus.Contracts.Panic

/-!
# The panic/defer/recover contracts are satisfiable (arm64)

For every returning contract of `Janus.Contracts.Panic` (`DeferprocContract`, `DeferreturnContract`,
`GorecoverContract`, …): a model `P0` of the panic runtime whose laws hold (`P0_laws`), a tiny
implementation (a single `RET`) placed at an address `A0` of a program with no other code, a proof
that it meets the contract for `P0`, and a call state (`wstate`) that satisfies the contract's
precondition. So no contract is contradictory (`<contract>_satisfiable`). The model code just
returns; the contract only promises a return with the ABI preserved and memory confined to the
runtime, which a `RET` trivially satisfies.
-/

namespace Janus.Contracts.PanicSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

/-! ## The model -/

/-- A distinct non-zero type word for each runtime-error kind (so `P0.err` is injective with
non-nil type words). -/
def errTyp : ErrKind → Nat
  | .bounds => 0x10008 | .divide => 0x10010 | .shift => 0x10018 | .overflow => 0x10020
  | .float => 0x10028 | .mem => 0x10030 | .simdImm => 0x10038 | .dottype => 0x10040
  | .makeslice => 0x10048 | .unsafeOp => 0x10050 | .wrap => 0x10058 | .rangeState => 0x10060

/-- The model of the panic runtime: one readable metadata range, stack depth 64, every runtime
error a distinct non-nil `error`. -/
def P0 : PanicRuntime where
  err k := ⟨errTyp k, 0⟩
  priv := [(0x10000, 0x11000)]
  depth := 64
  Env m := m.accessible 0x10000 0x1000 false = true

@[simp] theorem P0_priv : P0.priv = [(0x10000, 0x11000)] := rfl
@[simp] theorem P0_depth : P0.depth = 64 := rfl
@[simp] theorem P0_env (m : Memory) : P0.Env m = (m.accessible 0x10000 0x1000 false = true) := rfl

theorem P0_laws : P0.Laws where
  err_typ_ne k := by cases k <;> simp [P0, errTyp]
  err_inj k k' h := by
    have : (P0.err k).typ = (P0.err k').typ := by rw [h]
    cases k <;> cases k' <;> first | rfl | (simp only [P0, errTyp] at this; omega)
  depth_pos := by decide

/-! ## The toy program and the model code (a single `RET`) -/

/-- A program with no code, stubs or data of its own. -/
def toy : Program := { segments := [], stubs := [], exitAddr := 0 }

/-- Where the model `RET` is placed. -/
def A0 : Nat := 0x100000

/-- The model implementation: `ret` at `A0`. -/
def retCode : List Nat := [0xd65f03c0]

def at0 (ws : List Nat) : List Segment := [{ name := "model", base := A0, words := ws }]
def withCode (ws : List Nat) : Program := { segments := at0 ws, stubs := [], exitAddr := 0 }
theorem link_at0 (ws : List Nat) : toy.link (at0 ws) = withCode ws := rfl

/-! ## The witness call state -/

def wg : Nat := 0x50000
def wsp : Nat := 0x48000
def wret : Nat := 0x200000

/-- The witness memory: the runtime metadata `[0x10000, 0x11000)` readable, a stack
`[0x40000, 0x50000)` writable, the goroutine `[0x50000, 0x50100)` readable (its `stackguard0`
at `+16` is `0`, far below `SP`). All bytes zero. -/
def wmem : Memory :=
  ⟨fun _ => 0,
    [⟨0x10000, 0x1000, false⟩, ⟨0x40000, 0x10000, true⟩, ⟨0x50000, 0x100, false⟩]⟩

/-- The witness call state: goroutine in `X28`, return address `wret` in `X30`, stack pointer
`wsp`, the rest zero. -/
def wstate : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret
      else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
    mem := wmem }

theorem wstate_pre (nargs : Nat) (hn : nargs ≤ 2) : PanicPre P0 nargs wstate := by
  have hsp : wstate.sp = BitVec.ofNat 64 wsp := rfl
  have hg28 : wstate.regs 28 = BitVec.ofNat 64 wg := rfl
  have h30 : wstate.regs 30 = BitVec.ofNat 64 wret := rfl
  have hm : wstate.mem = wmem := rfl
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show wstate.mem.accessible 0x10000 0x1000 false = true; rw [hm]; decide
  · simp only [regG, stackguard0Offset, hg28]; decide
  · simp only [regG, stackguard0Offset, hg28, hm]; decide
  · simp only [stackguard0, regG, stackguard0Offset, hg28, hm, hsp, P0_depth]; decide
  · simp only [h30]; decide
  · simp only [h30]; decide
  · simp only [hsp]; decide
  · simp only [hsp, P0_depth]; decide
  · decide
  · simp only [hsp, P0_depth]; rw [BitVec.toNat_ofNat]; simp only [wsp]; omega
  · simp only [hsp, hm, P0_depth]
    refine Memory.accessible_mono _
      (show wmem.accessible (wsp - 64) (64 + 8 + 8 * 2) true = true by decide) ?_ ?_
    · rw [BitVec.toNat_ofNat]; simp [wsp]
    · rw [BitVec.toNat_ofNat]; simp only [wsp]; omega
  · simp only [hsp, P0_priv, P0_depth, outside_cons, outside_nil, and_true]
    rw [BitVec.toNat_ofNat]; simp only [wsp]; omega

/-- The model `RET` meets every returning panic contract for `P0`: from any state at `A0` in
`PanicPre`, it returns to `X30` with the ABI preserved and memory unchanged (so confined to
`P0.priv` and the callee stack). -/
theorem ret_summary (n : Nat) :
    Summary (toy.link (at0 retCode)) A0 (PanicPre P0 n) (PanicRet P0 n) := by
  rw [link_at0]
  intro s hpc ⟨henv, hg, ⟨h30a, h30b, hsp, hst, h8, hwin, hacc⟩, hout⟩
  janus_run
  refine ⟨s.regs, s.flags, s.vregs, s.mem, ?_, MemFrame.refl _ _, henv⟩
  show _ = retState s s.regs [] s.flags s.vregs s.mem
  simp only [retState]
  congr 1
  funext i; simp only [callRegs_apply, List.getD_nil]; split <;> rfl

theorem deferproc_satisfiable : ∃ (P : PanicRuntime) (impl : List Segment), P.Laws ∧
    DeferprocContract (toy.link impl) A0 P ∧ ∃ s, s.pc = BitVec.ofNat 64 A0 ∧ PanicPre P 1 s :=
  ⟨P0, _, P0_laws, ret_summary 1, wstate, rfl, wstate_pre 1 (by decide)⟩

theorem deferprocStack_satisfiable : ∃ (P : PanicRuntime) (impl : List Segment), P.Laws ∧
    DeferprocStackContract (toy.link impl) A0 P ∧ ∃ s, s.pc = BitVec.ofNat 64 A0 ∧ PanicPre P 1 s :=
  ⟨P0, _, P0_laws, ret_summary 1, wstate, rfl, wstate_pre 1 (by decide)⟩

theorem deferprocat_satisfiable : ∃ (P : PanicRuntime) (impl : List Segment), P.Laws ∧
    DeferprocatContract (toy.link impl) A0 P ∧ ∃ s, s.pc = BitVec.ofNat 64 A0 ∧ PanicPre P 2 s :=
  ⟨P0, _, P0_laws, ret_summary 2, wstate, rfl, wstate_pre 2 (by decide)⟩

theorem deferrangefunc_satisfiable : ∃ (P : PanicRuntime) (impl : List Segment), P.Laws ∧
    DeferrangefuncContract (toy.link impl) A0 P ∧ ∃ s, s.pc = BitVec.ofNat 64 A0 ∧ PanicPre P 0 s :=
  ⟨P0, _, P0_laws, ret_summary 0, wstate, rfl, wstate_pre 0 (by decide)⟩

theorem deferreturn_satisfiable : ∃ (P : PanicRuntime) (impl : List Segment), P.Laws ∧
    DeferreturnContract (toy.link impl) A0 P ∧ ∃ s, s.pc = BitVec.ofNat 64 A0 ∧ PanicPre P 0 s :=
  ⟨P0, _, P0_laws, ret_summary 0, wstate, rfl, wstate_pre 0 (by decide)⟩

theorem gorecover_satisfiable : ∃ (P : PanicRuntime) (impl : List Segment), P.Laws ∧
    GorecoverContract (toy.link impl) A0 P ∧ ∃ s, s.pc = BitVec.ofNat 64 A0 ∧ PanicPre P 1 s :=
  ⟨P0, _, P0_laws, ret_summary 1, wstate, rfl, wstate_pre 1 (by decide)⟩

end Janus.Contracts.PanicSat
