import Janus
import Extracted

/-! `example.com/basic.Bump(d)` on amd64: `counter += d; return counter`, for the writable global `example.com/basic.counter`, which the precondition must provide. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- Address of `example.com/basic.counter` (`.noptrbss`) in this binary, as reported in
`identity.json` (`skippedData`). -/
def counter : Nat := 0x576258

theorem correctness (d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [d]
      (fun s => StackWritable s 0 8 ∧ s.mem.accessible counter 8 true = true ∧
        Disjoint (s.regs regSP) 8 (BitVec.ofNat 64 counter) 8)
      (fun s s' => s'.regs 0 = d + BitVec.ofNat 64 (s.mem.readLE counter 8) ∧
        s'.mem.readLE counter 8 = (s'.regs 0).toNat) := by
  intro ret hret s hs hpre
  simp only [counter] at *
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, hc, hd⟩ := hpre
  simp only [Disjoint, regSP, Nat.sub_zero, Nat.zero_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hacc hd hnw
  janus64_run

end Proof
