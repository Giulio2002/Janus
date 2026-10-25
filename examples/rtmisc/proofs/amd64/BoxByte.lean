import Janus
import Extracted

/-!
# `BoxByte(b uint8) any`: a byte boxed through `runtime.staticuint64s` (amd64)

```go
func BoxByte(b uint8) any { return b }
```

**Guarantee.** For every byte `b` and every Go call state whose memory holds the program's
read-only data (`Program.DataLoaded`: among it the extracted `runtime.staticuint64s` and the
`uint8` type descriptor), the call returns, obeys the ABI, changes no memory, and returns the
interface `(uint8Type, ptr)` in `RAX`, `RBX` with `ptr = &staticuint64s[b]`, a readable word
holding `b`: the conversion does not allocate. Nothing is assumed beyond `DataLoaded`
(`staticAddr_holds` checks the extracted bytes against `Misc.staticuint64sBytes`).
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts.Misc

/-- The type word: the RIP-relative `LEAQ` at `BoxByte+0xe` (`type:uint8`). -/
def uint8Type : Nat := ripTarget Extracted.program (Extracted.entry + 0xe)

/-- `runtime.staticuint64s`, the extracted read-only object. -/
def staticAddr : Nat := dataAddr Extracted.program.data "runtime.staticuint64s"

/-- The table the code indexes (`LEAQ` at `BoxByte+0x3`) is `runtime.staticuint64s`. -/
theorem staticAddr_code : ripTarget Extracted.program (Extracted.entry + 3) = staticAddr := by decide

/-- With the program's data loaded, `staticAddr` holds the table `0, 1, …, 255`. -/
theorem staticAddr_holds {m : Janus.Arm64.Memory} (h : Extracted.program.DataLoaded m) :
    StaticUint64s m staticAddr :=
  StaticUint64s.of_loaded (ds := Extracted.program.data) h (d := Extracted.data1) rfl (by decide +kernel)

theorem correctness (b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [b] (fun s => StackWritable s 0 8 ∧ Extracted.program.DataLoaded s.mem)
      (fun s s' => (s'.regs 0).toNat = uint8Type ∧ (s'.regs 3).toNat = staticAddr + 8 * (b.toNat % 256) ∧
        s'.mem.accessible (s'.regs 3).toNat 8 false = true ∧
        s'.mem.readLE (s'.regs 3).toNat 8 = b.toNat % 256 ∧ s'.mem = s.mem) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, hd⟩
  have hst := staticAddr_holds hd
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus_eval_nat hT : uint8Type
  janus_eval_nat hA : staticAddr
  rw [hA] at hst
  janus64_run
  have hlt : b.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have hm : b.toNat % 256 % 4294967296 * 8 = 8 * (b.toNat % 256) := by omega
  rw [hm, hT, hA]
  exact ⟨rfl, rfl, hst.accessible hlt, hst.read hlt⟩

end Proof
