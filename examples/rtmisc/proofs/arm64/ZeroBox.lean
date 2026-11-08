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

namespace Witness

def ret : Nat := 0x1000
def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000


def dataByte (a : Nat) : Option (BitVec 8) :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def bytes0 (a : Nat) : BitVec 8 :=
  match dataByte a with
  | some v => v
  | none =>
  0

def mem0 : Janus.Arm64.Memory := ⟨bytes0, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x1000, false⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call, and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : Janus.Arm64.State) , RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧ (True) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = arrType ∧ (s'.regs 1).toNat = zeroAddr ∧ s'.mem = s.mem ∧
        (ZeroVal s.mem zeroAddr → s'.mem.accessible (s'.regs 1).toNat 32 false = true ∧
          s'.mem.readLE (s'.regs 1).toNat 32 = 0))) := by
  refine ⟨ret, s0, , hret, setup, ?pre, correctness  ret hret s0 setup ?pre⟩
  case pre =>
    simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, mem0, bytes0, sp0, g0] <;> decide

end Witness

end Proof
