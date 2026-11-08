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

namespace Witness

def ret : Nat := 0x200000
def sp0 : Nat := 0x108000
def g0 : Nat := 0x300000
def tls0 : Nat := 0x400000


def dataByte (a : Nat) : Option (BitVec 8) :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def bytes0 (a : Nat) : BitVec 8 :=
  match dataByte a with
  | some v => v
  | none =>
  if a = sp0 + 2 then 0x20 else if a = tls0 + 2 then 0x30 else
  0

def mem0 : Janus.Arm64.Memory := ⟨bytes0, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x1000, false⟩, ⟨tls0, 0x100, false⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then (0x42 : BitVec 64) else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := mem0, fsBase := BitVec.ofNat 64 (tls0 + 8) }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x42 : BitVec 64)] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0) with rfl <;> decide, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call, and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : Janus.Amd64.State) (b : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [b] s ∧ (StackWritable s 0 8 ∧ Extracted.program.DataLoaded s.mem) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = uint8Type ∧ (s'.regs 3).toNat = staticAddr + 8 * (b.toNat % 256) ∧
        s'.mem.accessible (s'.regs 3).toNat 8 false = true ∧
        s'.mem.readLE (s'.regs 3).toNat 8 = b.toNat % 256 ∧ s'.mem = s.mem)) := by
  refine ⟨ret, s0, 0x42, hret, setup, ?pre, correctness 0x42 ret hret s0 setup ?pre⟩
  case pre =>
    try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Program.DataLoaded]
    repeat' apply And.intro
    all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

end Witness

end Proof
