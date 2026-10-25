import Janus
import Extracted

/-! `example.com/basic.ClearArray(p *[5]uint64)` on amd64: `clear` on an array.

For every pointer `p` to 40 writable bytes (`Buffer`) that do not overlap the return-address
slot, all 40 bytes of `*p` are zero after the call (the 320-bit value at `p` is `0`) and nothing
outside `[p, p + 40)` changes (`OnlyWrites`). `clear(p[:])` compiles to three overlapping 16-byte
stores of the zero register `X15` (`MOVUPS X15, 0/16/24(AX)`); `X15 = 0` is part of the Go ABI
call state. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec

theorem correctness (p : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p]
      (fun s => StackWritable s 0 8 ∧ Buffer s p 40 true ∧ GoABI.Disjoint p 40 (s.regs regSP) 8)
      (fun s s' => s'.mem.readLE p.toNat 40 = 0 ∧ OnlyWrites s.mem s'.mem p.toNat 40) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hpw, hp⟩, hd⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add, GoABI.Disjoint] at hacc hnw hd
  janus64_run
  have z : (BitVec.toNat (OfNat.ofNat 0 : BitVec 128)) = 0 := rfl
  simp only [z]
  refine ⟨?_, by janus64_simp [onlyWrites_writeLE_iff, onlyWrites_self]⟩
  rw [show (40 : Nat) = 16 + (8 + 16) from rfl, Janus.Arm64.Memory.readLE_add, Janus.Arm64.Memory.readLE_add]
  janus64_simp [Janus.Tactic.readLE_writeLE_inside, Nat.zero_div, Nat.zero_mod]

end Proof
