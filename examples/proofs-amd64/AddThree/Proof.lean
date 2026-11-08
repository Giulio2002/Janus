import Janus
import Extracted

/-! `example.com/basic.AddThree` on amd64: `Add(Add(x, y), z)`, through the stack-check
prologue and two calls.

The callee `Add` (`ADDQ BX, AX; RET`, extracted with `AddThree`) is proved once, from any state
at its entry, as a `Summary`; `janus64_run calls [add_summary]` uses it at both call sites. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `Add` as a callee: from any state at its entry whose return-address slot `[RSP]` is readable
and holds an address below `2^47`, it returns there with `RAX = RAX + RBX`. -/
theorem add_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.Add")
      (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => ∃ f, s' = { s with regs := setRegF (setRegF s.regs 0 (s.regs 0 + s.regs 3)) 4
                                         (s.regs 4 + 8), rip := retAddrOf s, flags := f }) := by
  intro s hpc ⟨h1, h2⟩
  janus64_run
  exact ⟨_, rfl⟩

theorem correctness (x y z : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y, z] 1
      (fun s => StackGuardOK s 0 ∧ StackWritable s 32 32)
      (fun r => r = [x + y + z]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hg, hle, hnw, hacc⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run calls [add_summary]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def x : BitVec 64 := 1#64
def y : BitVec 64 := 2#64
def z : BitVec 64 := 3#64

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 3 then y else if i = 1 then z else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y, z] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackGuardOK s 0 ∧ StackWritable s 32 32) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y, z] s ∧ (StackGuardOK s 0 ∧ StackWritable s 32 32) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ (results 1 s') = [x + y + z]) :=
  ⟨ret, s0, x, y, z, hret, setup, hpre, correctness x y z ret hret s0 setup hpre⟩

end Witness

end Proof
