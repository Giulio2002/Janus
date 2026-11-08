import Janus
import Extracted

/-! `example.com/basic.Compose(a, b, x uint64) uint64` on amd64: a non-escaping closure.

For every call state whose stack-growth checks fall through (`StackGuardOK s 56`; the deeper
check is in the callee `twice`) with `[RSP-80, RSP+8)` writable and the guard word outside it,
the call returns `f(f(x)) = a·(a·x + b) + b mod 2^64` for the closure `f(v) = a·v + b`.

The closure captures `a` and `b` and does not escape, so `Compose` builds its funcval (the code
address of `Compose.func1`, then `a`, `b`) in its own frame, without allocating. `twice` calls it
twice (`CALL CX` with the funcval in `DX`), and `Compose.func1` reads the captured variables
through `DX`. Everything the indirect calls depend on is written by the code being proved, so
no hypothesis about the closure is needed. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (a b x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, x]
      (fun s => StackGuardOK s 56 ∧ StackWritable s 80 8 ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 80))
      (fun _ s' => (s'.regs 0).toNat = (a.toNat * (a.toNat * x.toNat + b.toNat) + b.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨hg, ⟨hle, hnw, hacc⟩, hgd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run
  simp only [BitVec.toNat_mul, BitVec.toNat_add]
  janus64_arith

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def a : BitVec 64 := 2#64
def b : BitVec 64 := 3#64
def x : BitVec 64 := 5#64

def s0 : State :=
  { regs := fun i => if i = 0 then a else if i = 3 then b else if i = 1 then x else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackGuardOK s 56 ∧ StackWritable s 80 8 ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 80)) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (a : BitVec 64) (b : BitVec 64) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b, x] s ∧ (StackGuardOK s 56 ∧ StackWritable s 80 8 ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 80)) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ (s'.regs 0).toNat = (a.toNat * (a.toNat * x.toNat + b.toNat) + b.toNat) % 2 ^ 64) :=
  ⟨ret, s0, a, b, x, hret, setup, hpre, correctness a b x ret hret s0 setup hpre⟩

end Witness

end Proof
