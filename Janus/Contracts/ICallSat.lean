import Janus.Contracts.ICall
import Janus.Tactic

/-!
# The abstract-callee contract is satisfiable (arm64)

`ICallContract` is a hypothesis about code that is not extracted. This file shows it is not contradictory: a
writer written in A64 (its words below), placed at `A0` of a program with no other code, meets the contract with the
callee memory `rt = [0x30000, 0x31000)`, the results related to the arguments by `R` (`n = len`, `err = nil`), and the
call-site property `P := True`; and a call state satisfying the precondition exists. So a theorem that assumes
`ICallContract` is not vacuous, and the contract's frame, register and stack clauses are consistent.

```
mov x0, x2 ; mov x1, xzr ; mov x2, xzr ; ret      -- (len, nil)
```
-/

set_option linter.unusedSimpArgs false

namespace Janus.Contracts.ICallSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Contracts.ICall

def toy : Program := { segments := [], stubs := [], exitAddr := 0 }

abbrev A0 : Nat := 0x100000

def code : List Nat := [0xaa0203e0, 0xaa1f03e1, 0xaa1f03e2, 0xd65f03c0]

def impl : List Segment := [{ name := "writer", base := A0, words := code }]

def prog : Program := { segments := impl, stubs := [], exitAddr := 0 }

theorem link_eq : toy.link impl = prog := rfl

/-- The callee's memory. -/
def rt0 : List (Nat × Nat) := [(0x30000, 0x31000)]

/-- The results the writer returns: `n = len`, `err = nil`. -/
def R0 : Res := fun _ _ a2 _ n e1 e2 => n = a2 ∧ e1 = 0 ∧ e2 = 0

/-- The return of the writer as `ICallRet`. -/
theorem ret_of (pr : State → Memory → Prop) (s : State) (hpr : pr s s.mem) (R : Nat → W64) (F : Flags) (h0 : R 0 = s.regs 2) (h1 : R 1 = 0) (h2 : R 2 = 0)
    (h18 : R 18 = s.regs 18) (h28 : R 28 = s.regs 28) (h29 : R 29 = s.regs 29) (hF : F = s.flags) :
    ICallRetP 4 16 rt0 (fun _ => []) R0 pr s { s with regs := R, flags := F, pc := s.regs 30 } := by
  refine ⟨R, F, s.vregs, s.mem, s.excl, s.exclPass, ?_, MemFrame.refl _ _, by simp, ?_, hpr⟩
  · simp only [retStateX]
    congr 1
    funext i
    simp only [callRegs]
    by_cases h : i = 18 ∨ i = 28 ∨ i = 29
    · rcases h with rfl | rfl | rfl <;> simp [h18, h28, h29]
    · simp only [h, ite_false, List.getD_nil]
  · exact ⟨h0, h1, h2⟩

theorem impl_okP (pr : State → Memory → Prop) (hpr : ∀ s, pr s s.mem) :
    ICallContract (toy.link impl) A0 4 16 48 rt0 (fun _ => []) R0 (fun _ => True) pr := by
  rw [link_eq]
  intro s hpc ⟨⟨hr1, hr2, _⟩, _⟩
  have hpc' : s.pc = 0x100000#64 := hpc
  janus_run [hpc']
  all_goals
    apply ret_of pr _ (hpr _)
    all_goals simp [setReg]

theorem impl_ok : ICallContract (toy.link impl) A0 4 16 48 rt0 (fun _ => []) R0 (fun _ => True) :=
  impl_okP (fun _ _ => True) (fun _ => trivial)

/-- The witness call state: `SP = 0x1800` in a writable region, `X30` outside the code. -/
def wstate : State :=
  { regs := fun i => if i = 30 then 0x200000#64 else 0#64, sp := 0x1800#64,
    pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨0x1000, 0x1000, true⟩]⟩ }

theorem wstate_pre : ICallPre 4 16 48 rt0 (fun _ => True) wstate := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, by decide, ?_, trivial⟩
  show Outside 0x17f8 56 rt0
  simp [rt0]

/-- `ICallContract` is satisfiable: an implementation meets it (with a non-trivial `R`) and a call state satisfies
its precondition. -/
theorem iCall_satisfiable : ∃ impl : List Segment,
    ICallContract (toy.link impl) A0 4 16 48 rt0 (fun _ => []) R0 (fun _ => True) ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ ICallPre 4 16 48 rt0 (fun _ => True) s :=
  ⟨impl, impl_ok, wstate, rfl, wstate_pre⟩

/-- **The `preserves` parameter is satisfiable (U-ICALL-PRESERVES).** The same writer meets
`ICallContract … (RtPreserves R2)` for EVERY runtime model `R2` (it leaves the memory as it found it, so any invariant of
the view still holds), and a call state satisfies the precondition. The allocating shapes (a callee that writes the heap
and re-establishes `R2.inv`) are the consumer's hypothesis about its own callee. -/
theorem iCallPreserves_satisfiable (R2 : RtInv) : ∃ impl : List Segment,
    ICallContract (toy.link impl) A0 4 16 48 rt0 (fun _ => []) R0 (fun _ => True) (RtPreserves R2) ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ ICallPre 4 16 48 rt0 (fun _ => True) s :=
  ⟨impl, impl_okP _ (fun _ b L h => h), wstate, rfl, wstate_pre⟩

end Janus.Contracts.ICallSat
