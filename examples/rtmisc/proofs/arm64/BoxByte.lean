import Extracted

/-!
# `BoxByte(b uint8) any`: a byte boxed through `runtime.staticuint64s` (arm64)

```go
func BoxByte(b uint8) any { return b }
```

**Guarantee.** For every byte `b` and every Go call state whose memory holds the program's
read-only data (`Program.DataLoaded`: among it the extracted `runtime.staticuint64s` and the
`uint8` type descriptor), the call returns, obeys the ABI, changes no memory, and returns the
interface `(uint8Type, ptr)` with `ptr = &staticuint64s[b]`, a readable word holding `b`: the
conversion does not allocate.

**Assumptions.** None beyond `DataLoaded`: `runtime.staticuint64s` is a read-only object of the
binary (`.rodata`), copied by the extractor, and `staticAddr_holds` checks its bytes against
`Misc.staticuint64sBytes` (the words `0 … 255`) by evaluation.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.Misc

namespace Proof

/-- The type word: the address `ADRP`+`ADD` at `BoxByte+0x10` compute (`type:uint8`). -/
def uint8Type : Nat :=
  adrpLdTarget (Extracted.entry + 0x10) (segWord Extracted.program "example.com/rtmisc.BoxByte" 4)
    (segWord Extracted.program "example.com/rtmisc.BoxByte" 5) 0

/-- `runtime.staticuint64s`, the extracted read-only object. -/
def staticAddr : Nat := dataAddr Extracted.program.data "runtime.staticuint64s"

/-- The table the code indexes (`ADRP`+`ADD` at `BoxByte+0x4`) is `runtime.staticuint64s`. -/
theorem staticAddr_code :
    adrpLdTarget (Extracted.entry + 4) (segWord Extracted.program "example.com/rtmisc.BoxByte" 1)
      (segWord Extracted.program "example.com/rtmisc.BoxByte" 2) 0 = staticAddr := by decide

/-- With the program's data loaded, `staticAddr` holds the table `0, 1, …, 255`. -/
theorem staticAddr_holds {m : Memory} (h : Extracted.program.DataLoaded m) : StaticUint64s m staticAddr :=
  StaticUint64s.of_loaded (ds := Extracted.program.data) h (d := Extracted.data1) rfl (by decide +kernel)

theorem correctness (b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [b] (fun s => Extracted.program.DataLoaded s.mem)
      (fun s s' => (s'.regs 0).toNat = uint8Type ∧ (s'.regs 1).toNat = staticAddr + 8 * (b.toNat % 256) ∧
        s'.mem.accessible (s'.regs 1).toNat 8 false = true ∧
        s'.mem.readLE (s'.regs 1).toNat 8 = b.toNat % 256 ∧ s'.mem = s.mem) := by
  intro ret hret s hs hd
  have hst := staticAddr_holds hd
  janus_intro hs
  janus_eval_nat hT : uint8Type
  janus_eval_nat hA : staticAddr
  rw [hA] at hst
  janus_run
  have hr : b.rotateRight 0 = b := by simp [BitVec.rotateRight_def]
  have hlt : b.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [hr, hT, hA]
  exact ⟨rfl, rfl, hst.accessible hlt, hst.read hlt⟩

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
  { regs := fun i => if i = 0 then (0x42 : BitVec 64) else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x42 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0) with rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call, and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : Janus.Arm64.State) (b : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [b] s ∧ (Extracted.program.DataLoaded s.mem) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = uint8Type ∧ (s'.regs 1).toNat = staticAddr + 8 * (b.toNat % 256) ∧
        s'.mem.accessible (s'.regs 1).toNat 8 false = true ∧
        s'.mem.readLE (s'.regs 1).toNat 8 = b.toNat % 256 ∧ s'.mem = s.mem)) := by
  refine ⟨ret, s0, 0x42, hret, setup, ?pre, correctness 0x42 ret hret s0 setup ?pre⟩
  case pre =>
    unfold Janus.Program.DataLoaded; decide

end Witness

end Proof
