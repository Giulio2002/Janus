import Janus
import Extracted

/-! `example.com/basic.DeferAdd(x, y)` on amd64: `r = x` and an open-coded `defer` of a closure
that adds `y` to `r`; the call returns `x + y`.

For every call state whose stack-growth check falls through, with `[RSP-64, RSP+8)` writable, the
call returns `[x + y]`. The deferred closure's funcval is built in the frame and called at the
exit (`CALL AX`, context in `DX`), so its target is read back from the stack. The
`CALL runtime.deferreturn` block (reached only after a recovered panic) is not extracted, and the
theorem shows it is not reached. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (x y : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y] 1
      (fun s => StackGuardOK s 0 ∧ StackWritable s 64 8)
      (fun r => r = [x + y]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hg, hle, hnw, hacc⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run
  first | with_reducible congr 1 | congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def x : BitVec 64 := 1#64
def y : BitVec 64 := 2#64

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 3 then y else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackGuardOK s 0 ∧ StackWritable s 64 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (StackGuardOK s 0 ∧ StackWritable s 64 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ (results 1 s') = [x + y]) :=
  ⟨ret, s0, x, y, hret, setup, hpre, correctness x y ret hret s0 setup hpre⟩

end Witness

end Proof
