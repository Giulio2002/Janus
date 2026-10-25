import Extracted

/-!
# `F64Eq(x, y float64) bool`: Go's `==` on `float64`

**Guarantee.** For all binary64 encodings `x`, `y` (NaNs and both zeros included) and every Go
call state of `example.com/basic.F64Eq` with `x`, `y` in `D0`, `D1` and `FPCR = 0` (what Linux
starts a process with and Go never changes), the call returns, obeys the ABI, and the `bool`
result (the low byte of `X0`) is `feq x y`: `false` if either is a NaN, otherwise whether the two
values are equal, so `+0 == -0` (`zeros`) and `NaN != NaN` (`nan`).

**What this covers.** The compiler inlines the comparison (`FCMPD`, `CSET EQ`); the proof executes
it on the ASL model of `FPCompare` (`Mem.fpCompare_z`). The same `feq` is the result of the
runtime's `f64equal` (`examples/proofs/AlgF64equal.lean`), which maps and interface comparisons use.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Float Janus.Contracts.Mem

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = x.toNat ∧ s.getV 1 64 = y.toNat ∧ s.fpcr = 0)
      (fun _ s' => (s'.regs 0).toNat % 256 = (feq binary64 x.toNat y.toNat).toNat) := by
  intro ret hret s hs ⟨hx, hy, hf⟩
  janus_intro hs
  simp only [State.getV] at hx hy
  janus_run [hx, hy, hf]
  cases feq binary64 x.toNat y.toNat <;> rfl

/-- `+0 == -0` is `true`. -/
theorem zeros : feq binary64 0 0x8000000000000000 = true := by decide

/-- A NaN is not `==` to itself. -/
theorem nan : feq binary64 0x7ff8000000000000 0x7ff8000000000000 = false := by decide

/-! ## Non-vacuity: the precondition holds for a concrete call, and the result is reached -/

namespace Witness

open Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- `+0` and `-0`. -/
def x : BitVec 64 := 0#64
def y : BitVec 64 := 0x8000000000000000#64

/-- The witness call state `F64Eq(+0, -0)`. -/
def s0 : State :=
  { regs := fun i => if i = 30 then BitVec.ofNat 64 ret else 0, sp := BitVec.ofNat 64 wsp,
    pc := BitVec.ofNat 64 Extracted.entry, flags := ⟨false, false, false, false⟩,
    mem := Janus.Contracts.EqHashModel.wmem,
    vregs := fun i => if i = 1 then BitVec.ofNat 128 0x8000000000000000 else 0 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h⟩

theorem hpre : s0.getV 0 64 = x.toNat ∧ s0.getV 1 64 = y.toNat ∧ s0.fpcr = 0 := by
  refine ⟨by decide, by decide, rfl⟩

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧
    (s.getV 0 64 = x.toNat ∧ s.getV 1 64 = y.toNat ∧ s.fpcr = 0) :=
  ⟨ret, s0, x, y, hret, setup, hpre⟩

/-- So the guarantee is reached: `+0 == -0` returns `true`. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 1 := by
  refine (correctness x y ret hret s0 setup hpre).mono ?_
  intro s' h
  exact ⟨h.1, by rw [h.2]; decide⟩

end Witness

end Proof
