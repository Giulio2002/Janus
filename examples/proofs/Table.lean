import Extracted

/-!
# `Table(i uint64) uint64`: entry `i & 7` of a constant `[8]uint64` (a `.rodata` literal)

**Guarantee.** For every 64-bit `i` and every Go call state `s` of `example.com/basic.Table` whose
memory holds the function's read-only data (`DataLoaded`), that satisfies Go's frame-pointer
invariant (`FPConvention`) and whose `SP` is aligned with `[SP-88, SP)` writable, the call
returns (never faulting or panicking), obeys the ABI, and `X0 = table[i mod 8]` for the table of
the Go source. The code copies the 64-byte literal from `.rodata` into its frame (four
`ADRP`/`ADD`/`LDP` and four `STP`) and loads `t[i&7]` from the frame.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- The Go source's table. -/
def table : List (BitVec 64) :=
  [0x243f6a8885a308d3, 0x13198a2e03707344, 0xa4093822299f31d0, 0x082efa98ec4e6c89,
   0x452821e638d01377, 0xbe5466cf34e90c6c, 0xc0ac29b7c97c50dd, 0x3f84d5b5b5470917]

theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i]
      (fun s => Extracted.program.DataLoaded s.mem ∧ FPConvention s ∧ StackOK s 88 0)
      (fun _ s' => s'.regs 0 = table[i.toNat % 8]!) := by
  intro ret hret s hs ⟨hd, hfp, ⟨hal, hb, ha, hw⟩⟩
  janus_intro hs
  simp only [FPConvention, regFP] at hfp
  janus_data hd [hw]
  janus_run
  generalize hk : i.toNat % 8 = k
  have hlt : k < 8 := hk ▸ Nat.mod_lt _ (by decide)
  janus_cases hlt
  all_goals janus_simp [table]


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def dataByte (a : Nat) : Option Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def wbytes (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (3) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(3 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (i : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [i] s ∧ (Extracted.program.DataLoaded s.mem ∧ FPConvention s ∧ StackOK s 88 0) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.regs 0 = table[i.toNat % 8]!)) := by
  refine ⟨ret, s0, (3), hret, setup, ?pre, correctness (3) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, dataByte, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
