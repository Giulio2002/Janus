import Janus
import Extracted

/-! `example.com/basic.DotBoth(a, b, c, d uint64) uint64` on amd64: a method value and a method
expression on a value receiver.

For every call state whose memory holds the function's read-only data (`DataLoaded`; the static
funcval of `Vec2.Dot`), whose stack-growth checks fall through (`StackGuardOK s 120`; the
deepest check is in the wrapper `Vec2.Dot-fm`) with `[RSP-168, RSP+40)` writable (the frames
and the caller's spill area for the four arguments) and the guard word outside it, the call
returns `(a, b)·(c, d) + (a, b)·(d, c) mod 2^64`.

The method value `v.Dot` is a closure over a copy of `v` built in `DotBoth`'s frame (the address
of `Vec2.Dot-fm`, then `a`, `b`), called by `applyVec` through `CALL SI` with the funcval in `DX`;
the wrapper reads the receiver through `DX` and calls `Vec2.Dot` directly. The method
expression `Vec2.Dot` is the static funcval `Vec2.Dot·f` in `.rodata`, whose code word is
`Vec2.Dot`; `applyVec2` calls it through `CALL R8`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (a b c d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, c, d]
      (fun s => Extracted.program.DataLoaded s.mem ∧ StackGuardOK s 120 ∧ StackWritable s 168 40 ∧
        ((s.regs 4).toNat + 40 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 168))
      (fun _ s' => (s'.regs 0).toNat =
        (a.toNat * c.toNat + b.toNat * d.toNat + (a.toNat * d.toNat + b.toNat * c.toNat)) % 2 ^ 64) := by
  intro ret hret s hs ⟨hd, hg, ⟨hle, hnw, hacc⟩, hgd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_data hd [hacc]
  set_option maxRecDepth 4000 in janus64_run
  simp only [BitVec.toNat_mul, BitVec.toNat_add]
  janus64_arith

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def a : BitVec 64 := 1#64
def b : BitVec 64 := 2#64
def c : BitVec 64 := 3#64
def d : BitVec 64 := 4#64

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then a else if r_ = 3 then b else if r_ = 1 then c else if r_ = 7 then d else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := withData Extracted.program.data wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b, c, d] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩
set_option maxRecDepth 100000 in
theorem hpre : (fun s => Extracted.program.DataLoaded s.mem ∧ StackGuardOK s 120 ∧ StackWritable s 168 40 ∧
        ((s.regs 4).toNat + 40 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 168)) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Amd64.Program.DataLoaded]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (a : BitVec 64) (b : BitVec 64) (c : BitVec 64) (d : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b, c, d] s ∧ (Extracted.program.DataLoaded s.mem ∧ StackGuardOK s 120 ∧ StackWritable s 168 40 ∧
        ((s.regs 4).toNat + 40 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 168)) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ (s'.regs 0).toNat =
        (a.toNat * c.toNat + b.toNat * d.toNat + (a.toNat * d.toNat + b.toNat * c.toNat)) % 2 ^ 64) :=
  ⟨ret, s0, a, b, c, d, hret, setup, hpre, correctness a b c d ret hret s0 setup hpre⟩

end Witness

end Proof
