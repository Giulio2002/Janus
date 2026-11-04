import Janus
import Extracted

/-! `example.com/basic.SymErr()` on amd64: returns the interface value of the package variable
`example.com/basic.errSym`, a sentinel error the linker initialised: the two words are the named
`Extracted.dataAddr.«example.com/basic.errSym→type»` and `…→data»` (generated from the binary's link-time
image), the variable is `Extracted.dataAddr.«example.com/basic.errSym»`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

abbrev v : Nat := Extracted.dataAddr.«example.com/basic.errSym»
abbrev typeWord : Nat := Extracted.dataAddr.«example.com/basic.errSym→type»
abbrev dataWord : Nat := Extracted.dataAddr.«example.com/basic.errSym→data»

def ErrHolds (m : Janus.Arm64.Memory) : Prop :=
  m.accessible v Extracted.dataSize.«example.com/basic.errSym» false = true ∧
    m.readLE v 8 = typeWord ∧ m.readLE (v + 8) 8 = dataWord

theorem correctness :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ ErrHolds s.mem)
      (fun _ s' => results 2 s' = [BitVec.ofNat 64 typeWord, BitVec.ofNat 64 dataWord]) := by
  intro ret hret s hs hpre
  janus64_addrs
  janus64_intro hs
  obtain ⟨⟨-, hnw, hstk⟩, hacc, h0, h1⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hstk hnw
  simp only [v, typeWord, dataWord, Extracted.dataAddr.«example.com/basic.errSym»,
    Extracted.dataAddr.«example.com/basic.errSym→type», Extracted.dataAddr.«example.com/basic.errSym→data»,
    Extracted.dataSize.«example.com/basic.errSym»] at hacc h0 h1 ⊢
  janus64_run
  done

end Proof
