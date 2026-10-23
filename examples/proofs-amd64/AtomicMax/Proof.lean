import Janus
import Extracted

/-! `example.com/basic.AtomicMax(p *uint64, v uint64) uint64` on amd64: a compare-and-swap
retry loop.

```
      JMP load
retry: MOVQ DX, AX
load:  MOVQ 0(AX), CX ; CMPQ CX, BX ; JAE done          // old := *p; old >= v: done
       MOVQ AX, DX ; MOVQ CX, AX
       LOCK CMPXCHGQ BX, 0(DX) ; SETEQ SI               // CompareAndSwap(p, old, v)
       NOPL ; TESTL SI, SI ; JEQ retry
done:  MOVQ CX, AX ; RET
```

The model is single-threaded: nothing changes `*p` between the load and the `CMPXCHG`, so the
compare-and-swap succeeds the first time and the retry edge is never taken (the symbolic
execution proves the failure branch infeasible). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `AtomicMax(p, v)` returns the old value of `*p` and leaves `*p = max(old, v)` (unsigned).
The word must be writable and must not overlap the return-address slot. -/
theorem correctness (p v : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, v]
      (fun s => StackWritable s 0 8 ∧ Buffer s p 8 true ∧ Disjoint p 8 (s.regs regSP) 8)
      (fun s s' => s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE p.toNat 8) ∧
        s'.mem.readLE p.toNat 8 = max (s.mem.readLE p.toNat 8) v.toNat) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hpw, hp⟩, hd⟩ := hpre
  simp only [Disjoint, regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hd
  janus64_run
  all_goals omega

end Proof
