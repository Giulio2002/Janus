import Extracted

/-!
# `ZeroBox() any`: a zero value boxed through `runtime.zeroVal` (arm64)

```go
func ZeroBox() any { return [4]uint64{} }
```

**Guarantee.** For every Go call state, the call returns, obeys the ABI, changes no memory, and
returns the interface `(arrType, zeroAddr)`: the type word is the `[4]uint64` type descriptor the
code loads, and the data word is the address of `runtime.zeroVal`, the runtime's read-only zero
value (no allocation). If that variable holds what the runtime keeps there (`Misc.ZeroVal`:
1024 readable zero bytes), the box is the value `[4]uint64{}`: its 32 bytes are readable and
zero.

**Assumption.** `runtime.zeroVal` lives in `.noptrbss` (writable, contents not fixed by the
binary), so the extractor does not copy it; `ZeroVal s.mem zeroAddr` is a hypothesis about the
runtime's data, at the address the code computes (docs/RUNTIME-CONTRACTS.md, "Remaining
runtime").
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.Misc

namespace Proof

/-- The type word: `ADRP`+`ADD` at `ZeroBox+0x0` (`type:[4]uint64`). -/
def arrType : Nat :=
  adrpLdTarget Extracted.entry (segWord Extracted.program "example.com/rtmisc.ZeroBox" 0)
    (segWord Extracted.program "example.com/rtmisc.ZeroBox" 1) 0

/-- The data word: `ADRP`+`ADD` at `ZeroBox+0x8` (`runtime.zeroVal`, `.noptrbss`). -/
def zeroAddr : Nat :=
  adrpLdTarget (Extracted.entry + 8) (segWord Extracted.program "example.com/rtmisc.ZeroBox" 2)
    (segWord Extracted.program "example.com/rtmisc.ZeroBox" 3) 0

theorem correctness :
    Ensures Extracted.program Extracted.entry [] (fun _ => True)
      (fun s s' => (s'.regs 0).toNat = arrType ∧ (s'.regs 1).toNat = zeroAddr ∧ s'.mem = s.mem ∧
        (ZeroVal s.mem zeroAddr → s'.mem.accessible (s'.regs 1).toNat 32 false = true ∧
          s'.mem.readLE (s'.regs 1).toNat 32 = 0)) := by
  intro ret hret s hs _
  janus_intro hs
  janus_eval_nat hT : arrType
  janus_eval_nat hZ : zeroAddr
  janus_run
  rw [hT, hZ]
  refine ⟨rfl, rfl, fun hz => ?_⟩
  exact ⟨by simpa using hz.accessible (off := 0) (n := 32) (by decide),
    by simpa using hz.read (off := 0) (n := 32) (by decide)⟩

end Proof
