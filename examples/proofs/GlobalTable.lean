import Extracted

/-!
# `GlobalTable(i uint64) uint64`: indexing a writable package array

**Guarantee.** For every 64-bit `i` and every Go call state `s` of
`example.com/basic.GlobalTable` whose memory makes the 64 bytes of the package variable
`example.com/basic.tbl` (a `[8]uint64` in `.noptrdata`) readable, the call returns (never faulting
or panicking), obeys the ABI, and `X0 = tbl[i & 7]`, the word at `tbl + 8·(i mod 8)` in the
memory at the call. The variable is writable, so its contents are not taken from the binary:
the theorem holds for whatever the program stored there. `tbl` is the address the code computes
(`ADRP` + `ADD`), recomputed from the extracted words.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- Address of `example.com/basic.tbl`: `ADRP` (word 1) plus the `ADD` immediate (word 2, the
same 12-bit field as an unscaled `LDR` offset). -/
def tbl : Nat :=
  adrpLdTarget (Extracted.entry + 4) (segWord Extracted.program "example.com/basic.GlobalTable" 1)
    (segWord Extracted.program "example.com/basic.GlobalTable" 2) 0

theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i] (fun s => s.mem.accessible tbl 64 false = true)
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE (tbl + 8 * (i.toNat % 8)) 8) := by
  intro ret hret s hs ht
  janus_intro hs
  janus_eval_nat h_t : tbl
  rw [h_t] at ht ⊢
  janus_run


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩, ⟨tbl, 64, false⟩]⟩


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
    CallSetup (Extracted.program.withExit ret) Extracted.entry [i] s ∧ (s.mem.accessible tbl 64 false = true) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = s.mem.readLE (tbl + 8 * (i.toNat % 8)) 8)) := by
  refine ⟨ret, s0, (3), hret, setup, ?pre, correctness (3) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp, tbl]
    all_goals decide

end Witness

end Proof
