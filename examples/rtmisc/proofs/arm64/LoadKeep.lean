import Extracted

/-!
# `LoadKeep(p *uint64) uint64`: a load followed by `runtime.KeepAlive(p)` (arm64)

```go
func LoadKeep(p *uint64) uint64 { v := *p; runtime.KeepAlive(p); return v }
```

**Guarantee.** For every pointer `p` whose 8 bytes are readable and every Go call state whose
spill slot `[SP+8, SP+16)` is writable and does not overlap them, the call returns, obeys the
ABI, returns the word at `p` read before the call, and its only write is `p` itself into the
spill slot.

**What `KeepAlive` is.** `runtime.KeepAlive` is a compiler intrinsic (`ssagen` `OpKeepAlive`):
there is no call and no runtime code. Its only effect on the machine code is that `p` stays
live until the intrinsic, which here is the store of `p` into its argument spill slot (a stack
slot the garbage collector scans). The model has no garbage collector, so the guarantee is this
machine-level one: the store happens, nothing else does. That the object stays reachable is a
property of the collector and is not stated (docs/RUNTIME-CONTRACTS.md, "Remaining runtime").
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (p : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p]
      (fun s => Ptr s.mem p 8 false ∧ StackOK s 0 16 ∧ Disjoint p.toNat 8 (s.sp.toNat + 8) 8)
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE p.toNat 8 ∧
        s'.mem = s.mem.writeLE (s.sp.toNat + 8) 8 p.toNat) := by
  intro ret hret s hs ⟨⟨hp, hp'⟩, ⟨hal, _, hb, hw⟩, hd⟩
  simp only [Disjoint] at hd
  janus_intro hs
  janus_run

end Proof
