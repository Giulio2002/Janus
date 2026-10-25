import Extracted

/-!
# `Eq32(a, b *[32]byte) bool`: `*a == *b` through `runtime.memequal`

**Guarantee.** For all pointers `a`, `b` and every Go call state `s` of
`example.com/basic.Eq32` such that
* the stack-growth prologue falls through (`GuardOK s 0`), `SP` is aligned and the 24 bytes
  below `SP` are writable (the 16-byte frame and the saved frame pointer),
* the 32 bytes at `a` and the 32 bytes at `b` are readable, and neither array overlaps that
  stack window (the arrays may overlap each other, or be the same array),

the call returns (never faulting or panicking), obeys the ABI, and the `bool` result (the low
byte of `X0`) is `true` iff the 32 bytes at `a` equal the 32 bytes at `b`.

**What this covers.** Go compiles `==` on `[32]byte` to `runtime.memequal(a, b, 32)`. Nothing is
assumed about it: the proof executes `memequal`'s machine code (`internal/bytealg/equal_arm64.s`)
instruction by instruction: the `a = b` shortcut, the skipped 64-byte SIMD loop (`32 & ~63 = 0`),
two rounds of the 16-byte `LDP.P`/`EOR`/`CBNZ` loop and the empty tail.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.Mem

namespace Proof

/-- The precondition (see the module documentation). -/
def pre (a b : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 24 0 ∧ Ptr s.mem a 32 false ∧ Ptr s.mem b 32 false ∧
    Disjoint a.toNat 32 (s.sp.toNat - 24) 24 ∧ Disjoint b.toNat 32 (s.sp.toNat - 24) 24

set_option maxHeartbeats 4000000 in
theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b] (pre a b)
      (fun s s' => (s'.regs 0).toNat % 256 =
        (s.mem.readLE a.toNat 32 == s.mem.readLE b.toNat 32).toNat) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hA, hA'⟩, ⟨hB, hB'⟩, hda, hdb⟩
  janus_intro hs
  simp only [Disjoint] at hda hdb
  janus_run
  -- the branches of the 16-byte loop come out as "word i of a and b agree"
  all_goals simp only [xor_eq_zero_iff] at *
  all_goals by_cases h : s.mem.readLE a.toNat 32 = s.mem.readLE b.toNat 32 <;>
    simp only [h, beq_self_eq_true, Bool.toNat_true, beq_eq_false_iff_ne.mpr, ne_eq, not_false_eq_true,
      Bool.toNat_false] <;> simp_all [readLE_32_eq_iff]

/-! ## Non-vacuity: the precondition holds for a concrete call, and the result is reached -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- The witness return address. -/
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- Two distinct all-zero 32-byte arrays of the witness memory. -/
def a : BitVec 64 := BitVec.ofNat 64 DST
def b : BitVec 64 := BitVec.ofNat 64 (DST + 32)

/-- The witness call state `Eq32(a, b)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then a else if i = 1 then b
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : pre a b s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by unfold Disjoint; decide, by unfold Disjoint; decide⟩

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (a b : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b] s ∧ pre a b s :=
  ⟨ret, s0, a, b, hret, setup, hpre⟩

/-- So the guarantee is reached: the two zero arrays compare equal. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 1 := by
  refine (correctness a b ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  decide

end Witness

end Proof
