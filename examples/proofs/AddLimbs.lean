import Extracted

/-!
# `AddLimbs(z, x, y *[4]uint64)`: a carry loop over four limbs, with aliasing

**Guarantee.** For all pointers `z`, `x`, `y` and every Go call state of
`example.com/basic.AddLimbs` with the pointers in `X0`–`X2` such that
* the 32 bytes at `z` are writable and those at `x` and `y` readable (each inside one memory
  region of the caller, below `2^48`; a written range overlaps no read-only region), and
* every pair of the three pointers is either **equal** or **disjoint** (so `z.Add256(z, z)`,
  `z = x`, `z = y`, `x = y` are all covered; only partial overlap is excluded),

the compiled code returns (never faulting or panicking), obeys the ABI, the 256-bit little-endian value at `z` afterwards is
`(X + Y) mod 2^256`, where `X` and `Y` are the values at `x` and `y` **before** the call, and no
byte outside `z[0..32)` changes (nor the region list).

The Go source is a `for i := 0; i < 4; i++` loop with `bits.Add64`; the compiled loop keeps the
carry in a register (`adds x8, x4, #-1` re-creates the carry flag, `adc x4, xzr, xzr` saves it)
and nil-checks the three pointers with byte loads in every iteration. Since the trip count is a
constant, symbolic execution runs the loop to completion (the counter is a known value in every
iteration), so no loop invariant is needed.

**What it rules out.** Wrong limbs or carries, reading an input limb after it was overwritten
through an alias, out-of-bounds accesses, writes outside `z`, faults and panics.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
        Aliasing z x ∧ Aliasing z y ∧ Aliasing x y)
      (fun s s' =>
        val256 s'.mem z.toNat = (val256 s.mem x.toNat + val256 s.mem y.toNat) % 2 ^ 256 ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hzx, hzy, hxy⟩
  janus_intro hs
  -- one symbolic run per aliasing pattern
  rcases hzx with rfl | hzx <;> rcases hzy with rfl | hzy <;> rcases hxy with h | hxy
  all_goals try subst h
  all_goals simp only [Disjoint] at *
  all_goals first | (exfalso; omega) | (janus_run; janus_arith)


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (0x300100) else if i = 2 then (0x300200) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (0x300100 : BitVec 64), (0x300200 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ (Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
        Aliasing z x ∧ Aliasing z y ∧ Aliasing x y) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (val256 s'.mem z.toNat = (val256 s.mem x.toNat + val256 s.mem y.toNat) % 2 ^ 256 ∧
        OnlyWrites s.mem s'.mem z.toNat 32)) := by
  refine ⟨ret, s0, (0x300000), (0x300100), (0x300200), hret, setup, ?pre, correctness (0x300000) (0x300100) (0x300200) ret hret s0 setup ?pre⟩
  case pre =>
    simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp] <;> decide

end Witness

end Proof
