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

namespace Witness

def ret : Nat := 0x200000
def sp0 : Nat := 0x108000
def g0 : Nat := 0x300000
def tls0 : Nat := 0x400000



def dbyte (a : Nat) : Option Nat :=
  Extracted.program.data.findSome? fun d =>
    if d.base ≤ a ∧ a < d.base + d.bytes.length then d.bytes[a - d.base]? else none

def bytes0 (a : Nat) : BitVec 8 := BitVec.ofNat 8 ((dbyte a).getD (if a = sp0 + 2 then 0x20 else if a = tls0 + 2 then 0x30 else 0))

def mem0 : Janus.Arm64.Memory := ⟨bytes0, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x1000, false⟩, ⟨tls0, 0x100, false⟩] ++ Extracted.program.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

theorem dataLoaded : Extracted.program.DataLoaded mem0 :=
  Program.DataLoaded_of_dataSegByte (by unfold DataSegsDisjoint; decide +kernel) (by decide +kernel) (by decide +kernel) fun a n h => by
    have h' : dbyte a = some n := h
    show (bytes0 a).toNat = n % 256
    simp only [bytes0, h', Option.getD_some, BitVec.toNat_ofNat]

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := mem0, fsBase := BitVec.ofNat 64 (tls0 + 8) }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by intro i h; simp at h, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call, and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : Janus.Amd64.State) , RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧ (StackWritable s 0 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = arrType ∧ (s'.regs 3).toNat = zeroAddr ∧ s'.mem = s.mem ∧
        (ZeroVal s.mem zeroAddr → s'.mem.accessible (s'.regs 3).toNat 32 false = true ∧
          s'.mem.readLE (s'.regs 3).toNat 32 = 0))) := by
  refine ⟨ret, s0, hret, setup, ?pre, correctness  ret hret s0 setup ?pre⟩
  case pre =>
    try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR]
    repeat' apply And.intro
    all_goals first | exact dataLoaded | decide +kernel | (refine ⟨?_, ?_, ?_⟩ <;> decide +kernel)

end Witness

end Proof
