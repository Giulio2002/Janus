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

end Proof
