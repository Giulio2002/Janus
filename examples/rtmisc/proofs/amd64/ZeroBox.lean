import Janus
import Extracted

/-!
# `ZeroBox() any`: a zero value boxed through `runtime.zeroVal` (amd64)

```go
func ZeroBox() any { return [4]uint64{} }
```

**Guarantee.** For every Go call state, the call returns, obeys the ABI, changes no memory, and
returns the interface `(arrType, zeroAddr)` in `RAX`, `RBX`: the `[4]uint64` type descriptor the
code loads and the address of `runtime.zeroVal` (no allocation). If that variable holds what
the runtime keeps there (`Misc.ZeroVal`: 1024 readable zero bytes), the box is `[4]uint64{}`.

**Assumption.** `runtime.zeroVal` is in `.noptrbss` (not copied by the extractor); `ZeroVal`
is a hypothesis about the runtime's data at the address the code computes
(docs/RUNTIME-CONTRACTS.md, "Remaining runtime").
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts.Misc

/-- The type word: the RIP-relative `LEAQ` at `ZeroBox+0x0` (`type:[4]uint64`). -/
def arrType : Nat := ripTarget Extracted.program Extracted.entry

/-- The data word: the RIP-relative `LEAQ` at `ZeroBox+0x7` (`runtime.zeroVal`, `.noptrbss`). -/
def zeroAddr : Nat := ripTarget Extracted.program (Extracted.entry + 7)

theorem correctness :
    Ensures Extracted.program Extracted.entry [] (fun s => StackWritable s 0 8)
      (fun s s' => (s'.regs 0).toNat = arrType ∧ (s'.regs 3).toNat = zeroAddr ∧ s'.mem = s.mem ∧
        (ZeroVal s.mem zeroAddr → s'.mem.accessible (s'.regs 3).toNat 32 false = true ∧
          s'.mem.readLE (s'.regs 3).toNat 32 = 0)) := by
  intro ret hret s hs ⟨_, hnw, hacc⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus_eval_nat hT : arrType
  janus_eval_nat hZ : zeroAddr
  janus64_run
  rw [hT, hZ]
  refine ⟨rfl, rfl, fun hz => ?_⟩
  exact ⟨by simpa using hz.accessible (off := 0) (n := 32) (by decide),
    by simpa using hz.read (off := 0) (n := 32) (by decide)⟩

end Proof
