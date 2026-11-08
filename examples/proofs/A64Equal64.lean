import Extracted

/-!
# `A64Equal64(a, b *[64]byte)`: `bytes.Equal(a[:], b[:])` through `runtime.memequal`'s SIMD loop

**Guarantee.** For all pointers `a`, `b` and every Go call state `s` of
`example.com/basic.A64Equal64` such that
* the stack-growth prologue falls through (`GuardOK s 0`), `SP` is aligned and the 24 bytes
  below `SP` are writable (the 16-byte frame and the saved frame pointer),
* the 64 bytes at `a` and the 64 bytes at `b` are readable, and neither array overlaps that
  stack window (the arrays may overlap each other, or be the same array),

the call returns (never faulting or panicking), obeys the ABI, and returns `1` (`true`) in `X0`
if the 64 bytes at `a` equal the 64 bytes at `b`, and `0` (`false`) otherwise.

**What this covers.** `bytes.Equal` is inlined: with the length known to be 64 it becomes a call
`runtime.memequal(a, b, 64)`. The proof executes both functions instruction by instruction from
the extracted words, including memequal's 64-byte SIMD loop: two `LD1 {v0.2d-v3.2d}` loads,
four `CMEQ .2D` (each 64-bit lane all-ones iff equal), three `AND .16B`, two `UMOV x, v.d[i]`
and the `CBZ` tests, plus the shortcut for `a = b`. The vector registers are part of the state
(`State.vregs`), arbitrary at the call, and the model of each instruction is checked against
qemu and the Arm ASL (Sail) model (`docs/ORACLE.md`, `docs/ORACLE-SAIL.md`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

set_option maxHeartbeats 4000000 in
theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b]
      (fun s => GuardOK s 0 ∧ StackOK s 24 0 ∧ Ptr s.mem a 64 false ∧ Ptr s.mem b 64 false ∧
        Disjoint a.toNat 64 (s.sp.toNat - 24) 24 ∧ Disjoint b.toNat 64 (s.sp.toNat - 24) 24)
      (fun s s' => s'.regs 0 = if s.mem.readLE a.toNat 64 = s.mem.readLE b.toNat 64 then 1 else 0) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hA, hA'⟩, ⟨hB, hB'⟩, hda, hdb⟩
  janus_intro hs
  simp only [Disjoint] at hda hdb
  -- Executes A64Equal64 and memequal; the branches of the SIMD loop's two `CBZ`s come out as
  -- "words 0, 2, 4, 6 are equal" and "words 1, 3, 5, 7 are equal" (`elem_cmeq`, `ite_land_ite`).
  janus_run
  -- 64 bytes are equal iff their eight words are.
  all_goals simp only [readLE_64_eq_iff, Nat.add_assoc, Nat.reduceAdd] at *
  all_goals split <;> simp_all


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (0x300100) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (0x300100 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (a : BitVec 64) (b : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b] s ∧ (GuardOK s 0 ∧ StackOK s 24 0 ∧ Ptr s.mem a 64 false ∧ Ptr s.mem b 64 false ∧
        Disjoint a.toNat 64 (s.sp.toNat - 24) 24 ∧ Disjoint b.toNat 64 (s.sp.toNat - 24) 24) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.regs 0 = if s.mem.readLE a.toNat 64 = s.mem.readLE b.toNat 64 then 1 else 0)) := by
  refine ⟨ret, s0, (0x300000), (0x300100), hret, setup, ?pre, correctness (0x300000) (0x300100) ret hret s0 setup ?pre⟩
  case pre =>
    simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp] <;> decide

end Witness

end Proof
