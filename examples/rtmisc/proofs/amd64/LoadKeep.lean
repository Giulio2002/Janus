import Janus
import Extracted

/-!
# `LoadKeep(p *uint64) uint64`: a load followed by `runtime.KeepAlive(p)` (amd64)

```go
func LoadKeep(p *uint64) uint64 { v := *p; runtime.KeepAlive(p); return v }
```

**Guarantee.** For every pointer `p` whose 8 bytes are readable and every Go call state whose
spill slot `[RSP+8, RSP+16)` is writable and does not overlap them, the call returns, obeys the
ABI, returns the word at `p` read before the call in `RAX`, and its only write is `p` itself
into the spill slot.

**What `KeepAlive` is.** A compiler intrinsic (`ssagen` `OpKeepAlive`): no call and no runtime
code; its only machine-level effect is that `p` stays live until it, here the store of `p` into
its spill slot. See the arm64 proof and docs/RUNTIME-CONTRACTS.md, "Remaining runtime".
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (p : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p]
      (fun s => StackWritable s 0 16 ∧ Buffer s p 8 false ∧ Janus.Spec.Disjoint p.toNat 8 ((s.regs regSP).toNat + 8) 8)
      (fun s s' => (s'.regs 0).toNat = valueAt s p 8 ∧
        s'.mem = s.mem.writeLE ((s.regs regSP).toNat + 8) 8 p.toNat) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hpb, hp⟩, hd⟩
  janus64_intro hs
  simp only [regSP] at hacc hnw hd ⊢
  simp only [Janus.Spec.Disjoint] at hd
  simp only [valueAt]
  janus64_run
end Proof
