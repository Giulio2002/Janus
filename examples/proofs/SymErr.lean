import Extracted

/-!
# `SymErr() error`: a sentinel error read through the named link-time words

**Guarantee.** For every Go call state `s` of `example.com/basic.SymErr` whose memory holds the
package variable `example.com/basic.errSym` (16 bytes in `.data`) with the contents the linker
gave it, the call returns (never faulting or panicking), obeys the ABI, and returns the interface
value: `X0` is the type word and `X1` the data word of the variable.

The variable, its type word (the `*errors.errorString` descriptor) and its data word (the static
`errorString` it points to) are `Extracted.dataAddr.«example.com/basic.errSym»`,
`…«example.com/basic.errSym→type»` and `…«example.com/basic.errSym→data»`, generated from the
binary's symbol table and link-time image: no address of this file depends on the layout.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

abbrev v : Nat := Extracted.dataAddr.«example.com/basic.errSym»
abbrev typeWord : Nat := Extracted.dataAddr.«example.com/basic.errSym→type»
abbrev dataWord : Nat := Extracted.dataAddr.«example.com/basic.errSym→data»

/-- The variable's memory holds its link-time image. -/
def ErrHolds (m : Janus.Arm64.Memory) : Prop :=
  m.accessible v Extracted.dataSize.«example.com/basic.errSym» false = true ∧
    m.readLE v 8 = typeWord ∧ m.readLE (v + 8) 8 = dataWord

theorem correctness :
    Ensures Extracted.program Extracted.entry [] (fun s => ErrHolds s.mem)
      (fun _ s' => (s'.regs 0).toNat = typeWord ∧ (s'.regs 1).toNat = dataWord) := by
  intro ret hret s hs ht
  janus_intro hs
  simp only [ErrHolds, v, typeWord, dataWord, Extracted.dataAddr.«example.com/basic.errSym»,
    Extracted.dataAddr.«example.com/basic.errSym→type», Extracted.dataAddr.«example.com/basic.errSym→data»,
    Extracted.dataSize.«example.com/basic.errSym»] at ht ⊢
  obtain ⟨hacc, h0, h1⟩ := ht
  janus_run
  exact ⟨h0, h1⟩


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000


def wbytes (a : Nat) : Byte := if v ≤ a ∧ a < v + 8 then BitVec.ofNat 8 (typeWord / 256 ^ (a - v) % 256) else if v + 8 ≤ a ∧ a < v + 16 then BitVec.ofNat 8 (dataWord / 256 ^ (a - v - 8) % 256) else 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩, ⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩, ⟨v, Extracted.dataSize.«example.com/basic.errSym», false⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    omega⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem hpre : ErrHolds s0.mem := by
  unfold ErrHolds
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧ (ErrHolds s.mem) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = typeWord ∧ (s'.regs 1).toNat = dataWord)) :=
  ⟨ret, s0, hret, setup, hpre, correctness ret hret s0 setup hpre⟩

end Witness

end Proof
