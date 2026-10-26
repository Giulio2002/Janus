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

end Proof
