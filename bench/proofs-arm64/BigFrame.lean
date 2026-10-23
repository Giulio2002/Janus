import Extracted

/-!
# Benchmark `BigFrame(x, k uint64) uint64` on arm64: a 528-byte stack frame

```go
var buf [64]uint64
for i := range buf { buf[i] = x + uint64(i) }
return buf[k&63]
```

The frame is large enough for the `sub x17, sp, #400` form of the stack-guard prologue
(`GuardOK s 400`). The zeroing loop (8 × 4 `STP`) and the fill loop (64 stores) have constant
trip counts, so the run executes them completely (about 400 instructions, 128 stores into one
memory chain). The final load is at a symbolic index; after the run, `janus_cases` splits it
into 64 cases, each resolved through the store chain. The epilogue recomputes `X29 = SP + 520`
instead of reloading it, so the precondition states Go's frame-pointer invariant at entry,
`X29 = SP - 8`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

set_option janus.aliasInfo false in
set_option maxHeartbeats 20000000 in
theorem correctness (x k : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, k]
      (fun s => GuardOK s 400 ∧ StackOK s 536 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 536) 536 ∧ s.regs 29 = s.sp - 8)
      (fun _ s' => s'.regs 0 = x + BitVec.ofNat 64 (k.toNat % 64)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hfp⟩
  janus_intro hs
  simp only [Disjoint] at hd
  janus_run
  generalize hj : k.toNat % 64 = j
  have hlt : j < 64 := hj ▸ Nat.mod_lt _ (by decide)
  janus_cases hlt
  all_goals janus_simp
  all_goals bv_omega

end Proof
