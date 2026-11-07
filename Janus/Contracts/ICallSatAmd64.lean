import Janus.Contracts.ICallAmd64
import Janus.Contracts.ICallSat

/-!
# The abstract-callee contract is satisfiable (amd64)

As `Janus.Contracts.ICallSat`: a writer in x86-64 machine code at `A0` meets `ICallContract64` (results
`(len, nil)` in `RAX`, `RBX`, `RCX`, related to the arguments by `ICallSat.R0`), and a call state satisfying its
precondition exists.

```
MOV RAX, RCX ; XOR EBX, EBX ; XOR ECX, ECX ; RET      -- (len, nil)
```
-/

set_option linter.unusedSimpArgs false

namespace Janus.Contracts.ICallSatAmd64

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.ICallSat

def toy : Janus.Amd64.Program := { segments := [], stubs := [], exitAddr := 0 }

abbrev A0 : Nat := 0x100000

def code : List Nat := [0x48, 0x89, 0xc8, 0x31, 0xdb, 0x31, 0xc9, 0xc3]

def impl : List Janus.Amd64.Segment := [{ name := "writer", base := A0, bytes := code }]

def prog : Janus.Amd64.Program := { segments := impl, stubs := [], exitAddr := 0 }

theorem link_eq : toy.link impl = prog := rfl

theorem ret_of {nargs stack : Nat} (pr : State → Janus.Arm64.Memory → Prop) (s : State) (hpr : pr s s.mem) (R : Nat → W64) (F : Flags) (h0 : R 0 = s.regs 1) (h3 : R 3 = 0) (h1 : R 1 = 0)
    (h4 : R 4 = s.regs 4 + 8#64) (h5 : R 5 = s.regs 5) (h14 : R 14 = s.regs 14) :
    ICallRetP64 nargs stack rt0 (fun _ => []) R0 pr s { s with regs := R, flags := F, rip := retAddrOf s } := by
  refine ⟨R, F, s.xmm, s.ymmHi, s.mem, s.zmmHi, s.kreg, ?_, MemFrame.refl _ _, by simp, ?_, hpr⟩
  · simp only [retState64]
    congr 1
    · funext i
      simp only [callRegs64]
      by_cases e4 : i = 4
      · subst e4; simp [h4]
      by_cases e5 : i = 5 ∨ i = 14
      · rcases e5 with rfl | rfl <;> simp [h5, h14]
      simp only [e4, e5, ite_false]
      by_cases e0 : i = 0
      · subst e0; simp [h0]
      by_cases e3 : i = 3
      · subst e3; simp [h3]
      by_cases e1 : i = 1
      · subst e1; simp [h1]
      simp [e0, e3, e1]
    · funext i; split <;> simp_all
  · exact ⟨h0, h3, h1⟩

theorem impl_okP {nargs stack above : Nat} {P : State → Prop} (pr : State → Janus.Arm64.Memory → Prop) (hpr : ∀ s, pr s s.mem) :
    ICallContract64 (toy.link impl) A0 nargs stack above rt0 (fun _ => []) R0 P pr := by
  rw [link_eq]
  intro s hpc ⟨⟨hr, _, hst, _, hw⟩, _⟩
  have hacc : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hw) (by omega) (by omega)
  have hpc' : s.rip = 0x100000#64 := hpc
  janus64_run [hpc']
  all_goals
    apply ret_of pr _ (hpr _)
    all_goals simp [setRegF]

theorem impl_ok : ICallContract64 (toy.link impl) A0 4 16 48 rt0 (fun _ => []) R0 (fun _ => True) :=
  impl_okP (fun _ _ => True) (fun _ => trivial)

def wstate : State :=
  { regs := fun i => if i = 4 then 0x1800#64 else 0#64, rip := BitVec.ofNat 64 A0,
    flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0, mem := ⟨fun _ => 0, [⟨0x1000, 0x1000, true⟩]⟩,
    ymmHi := fun _ => 0, fsBase := 0, df := false, mxcsr := 0x1F80 }

theorem wstate_pre : ICallPre64 4 16 48 rt0 (fun _ => True) wstate := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, by decide, ?_, trivial⟩
  show Outside 0x1800 48 rt0
  simp [rt0]

/-- `ICallContract64` is satisfiable. -/
theorem iCall64_satisfiable : ∃ impl : List Janus.Amd64.Segment,
    ICallContract64 (toy.link impl) A0 4 16 48 rt0 (fun _ => []) R0 (fun _ => True) ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧ ICallPre64 4 16 48 rt0 (fun _ => True) s :=
  ⟨impl, impl_ok, wstate, rfl, wstate_pre⟩

/-- The `preserves` parameter is satisfiable (amd64): the writer leaves the memory as it found it, so it meets
`ICallContract64 … (RtPreserves64 R2)` for every runtime model `R2`. -/
theorem iCallPreserves64_satisfiable (R2 : RtInv) : ∃ impl : List Janus.Amd64.Segment,
    ICallContract64 (toy.link impl) A0 4 16 48 rt0 (fun _ => []) R0 (fun _ => True) (RtPreserves64 R2) ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧ ICallPre64 4 16 48 rt0 (fun _ => True) s :=
  ⟨impl, impl_okP _ (fun _ b L h => h), wstate, rfl, wstate_pre⟩

end Janus.Contracts.ICallSatAmd64
