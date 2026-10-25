import Janus
import Extracted

/-! `example.com/basic.Sum3(a, b, c uint64) uint64` on amd64: a variadic call.

For every call state whose stack-growth check falls through (`StackGuardOK s 0`) with
`[RSP-64, RSP+8)` writable and the guard word outside it, the call returns `a + b + c mod 2^64`.
`sumv(a, b, c)` receives its variadic arguments as a slice: `Sum3` stores them in a
`[3]uint64` in its own frame (no allocation) and passes `(&arr, 3, 3)` in `RAX`, `RBX`, `RCX`;
`sumv`'s `range` loop over it has the literal length 3, so the run executes it. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (a b c : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, c]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 64 8 ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 64))
      (fun _ s' => (s'.regs 0).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨hg, ⟨hle, hnw, hacc⟩, hgd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run
  omega

end Proof
