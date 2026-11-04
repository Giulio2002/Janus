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

end Proof
