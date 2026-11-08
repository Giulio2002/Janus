import Janus
import Extracted

/-! `example.com/basic.IncTwice(c *Counter, d uint64) uint64` on amd64: static calls of a
pointer-receiver method.

For every pointer `c` to 8 writable bytes (`c.N`) outside the stack window `[RSP-40, RSP+24)`
and the guard word, and every call state whose stack-growth check falls through with that window
writable: with `N` the value of `c.N` before the call, afterwards `c.N = N + 2d` and the result
is `(N + d) + (N + 2d)`, modulo `2^64`. `c.Inc(d)` is a direct `CALL (*Counter).Inc` with the
receiver in `RAX`; the second call sees the first one's store. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (c d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, d]
      (fun s => Buffer s c 8 true ∧ StackGuardOK s 0 ∧ StackWritable s 40 24 ∧
        ((s.regs 4).toNat + 24 ≤ c.toNat ∨ c.toNat + 8 ≤ (s.regs 4).toNat - 40) ∧
        ((s.regs 14).toNat + 24 ≤ c.toNat ∨ c.toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        ((s.regs 4).toNat + 24 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 40))
      (fun s s' => s'.mem.readLE c.toNat 8 = (s.mem.readLE c.toNat 8 + 2 * d.toNat) % 2 ^ 64 ∧
        (s'.regs 0).toNat = ((s.mem.readLE c.toNat 8 + d.toNat) + (s.mem.readLE c.toNat 8 + 2 * d.toNat)) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hcb, hc⟩, hg, ⟨hle, hnw, hacc⟩, hd, hcg, hgd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run
  constructor <;> omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def c : BitVec 64 := 0x30800#64
def d : BitVec 64 := 3#64

def s0 : State :=
  { regs := fun i => if i = 0 then c else if i = 3 then d else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [c, d] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => Buffer s c 8 true ∧ StackGuardOK s 0 ∧ StackWritable s 40 24 ∧
        ((s.regs 4).toNat + 24 ≤ c.toNat ∨ c.toNat + 8 ≤ (s.regs 4).toNat - 40) ∧
        ((s.regs 14).toNat + 24 ≤ c.toNat ∨ c.toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        ((s.regs 4).toNat + 24 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 40)) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (c : BitVec 64) (d : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [c, d] s ∧ (Buffer s c 8 true ∧ StackGuardOK s 0 ∧ StackWritable s 40 24 ∧
        ((s.regs 4).toNat + 24 ≤ c.toNat ∨ c.toNat + 8 ≤ (s.regs 4).toNat - 40) ∧
        ((s.regs 14).toNat + 24 ≤ c.toNat ∨ c.toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        ((s.regs 4).toNat + 24 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 40)) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ s'.mem.readLE c.toNat 8 = (s.mem.readLE c.toNat 8 + 2 * d.toNat) % 2 ^ 64 ∧
        (s'.regs 0).toNat = ((s.mem.readLE c.toNat 8 + d.toNat) + (s.mem.readLE c.toNat 8 + 2 * d.toNat)) % 2 ^ 64) :=
  ⟨ret, s0, c, d, hret, setup, hpre, correctness c d ret hret s0 setup hpre⟩

end Witness

end Proof
