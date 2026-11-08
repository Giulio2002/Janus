import Extracted

/-!
# `HexDigit(i uint64) byte` returns `"0123456789abcdef"[i & 15]` (an indexed `.rodata` load)

**Guarantee.** For every 64-bit `i` and every Go call state `s` of `example.com/basic.HexDigit`
(`i` in `X0`) in which memory holds the program's read-only data (`Program.DataLoaded`, which
includes the string constant), the call returns (never faulting or panicking), obeys the ABI, and `X0` is the ASCII code of
the hexadecimal digit of `i mod 16`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- ASCII code of the hexadecimal digit `d < 16`. -/
def hexDigit (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i]
      (fun s => Extracted.program.DataLoaded s.mem)
      (fun _ s' => (s'.regs 0).toNat = hexDigit (i.toNat % 16)) := by
  intro ret hret s hs hd
  janus_intro hs
  janus_data hd
  janus_run
  -- one case per digit: the load address becomes a literal and is read from the data
  generalize hk : i.toNat % 16 = k
  have hlt : k < 16 := hk ▸ Nat.mod_lt _ (by decide)
  janus_cases hlt
  all_goals janus_simp [hexDigit]


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
  { regs := fun i => if i = 0 then (10) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(10 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (i : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [i] s ∧ (Extracted.program.DataLoaded s.mem) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = hexDigit (i.toNat % 16))) := by
  refine ⟨ret, s0, (10), hret, setup, ?pre, correctness (10) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, dataByte, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
