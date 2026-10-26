import Extracted

/-!
# `Double(x uint64) uint64`: a run-time flag global, for every value it may hold

**Guarantee.** Extracted with `--global example.com/basic.useFast`. `useFast` is a `bool` set by
package initialisation (like math/big's `hasADX`, set from `internal/cpu` at startup), so its
link-time image (`.noptrbss`, zero) is not its value at a call, and the theorem does not assume
it. For every 64-bit `x`, every byte value `v` of the flag (`GlobalBytesIs … "useFast" 0 1 v`,
the variable in one writable region) and every Go call state, the call returns (never faulting
or panicking), obeys the ABI, and `X0 = 2x mod 2^64`: the fast path (`ADD X0, X0, X0`, taken
when bit 0 of the flag is set: `TBNZ`) and the two-iteration loop agree.

**Non-vacuity.** `Witness.nonvacuous`: the precondition holds for the flag clear (the link-time
image, `GlobalsInit.bytesIs`) and for the flag set (the image with the byte stored as `1`);
`Witness.returns`: both calls `Double(21)` return `42`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (x : BitVec 64) (v : Nat) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GlobalBytesIs Extracted.program.globals s.mem "example.com/basic.useFast" 0 1 v)
      (fun _ s' => s'.regs 0 = x + x) := by
  intro ret hret s hs h
  janus_intro hs
  have hacc := h.accessible rfl false
  simp only [Nat.add_zero] at hacc
  janus_run

namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The link-time image of the global (the flag clear). -/
def mem0 : Memory := globalsImage Extracted.program.globals ⟨fun _ => 0, []⟩

/-- The same memory after initialisation set the flag. -/
def mem1 : Memory := mem0.writeLE (globalAddr Extracted.program.globals "example.com/basic.useFast") 1 1

def s0 (m : Memory) : State :=
  { regs := fun i => if i = 0 then 21#64 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := 0x10000, pc := BitVec.ofNat 64 Extracted.entry, flags := ⟨false, false, false, false⟩,
    mem := m }

theorem setup (m : Memory) : CallSetup (Extracted.program.withExit ret) Extracted.entry [21#64] (s0 m) :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

/-- The flag clear: the link-time image (`GlobalsInit`, hence the byte `0`). -/
theorem pre0 : GlobalBytesIs Extracted.program.globals (s0 mem0).mem "example.com/basic.useFast" 0 1 0 :=
  (globalsInit_image Extracted.program.globals ⟨fun _ => 0, []⟩ ["example.com/basic.useFast"]
    (by decide) (by decide)).bytesIs (n := "example.com/basic.useFast") (by simp) rfl
    (off := 0) (k := 1) (by decide)

/-- The flag set. -/
theorem pre1 : GlobalBytesIs Extracted.program.globals (s0 mem1).mem "example.com/basic.useFast" 0 1 1 :=
  ⟨_, rfl, by decide, by decide, by decide⟩

/-- The hypotheses of `correctness` hold together, for the flag clear and for the flag set. -/
theorem nonvacuous : ∃ (ret : Nat) (s s' : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [21#64] s ∧
    GlobalBytesIs Extracted.program.globals s.mem "example.com/basic.useFast" 0 1 0 ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [21#64] s' ∧
    GlobalBytesIs Extracted.program.globals s'.mem "example.com/basic.useFast" 0 1 1 :=
  ⟨ret, s0 mem0, s0 mem1, hret, setup _, pre0, setup _, pre1⟩

/-- So the guarantee is reached on both paths: `Double(21)` returns `42`. -/
theorem returns :
    Returns (Extracted.program.withExit ret) (s0 mem0) (fun s' => ABIReturn (s0 mem0) s' ∧ s'.regs 0 = 42#64) ∧
    Returns (Extracted.program.withExit ret) (s0 mem1) (fun s' => ABIReturn (s0 mem1) s' ∧ s'.regs 0 = 42#64) := by
  refine ⟨(correctness 21#64 0 ret hret _ (setup _) pre0).mono ?_,
    (correctness 21#64 1 ret hret _ (setup _) pre1).mono ?_⟩
  all_goals intro s' h; exact ⟨h.1, by rw [h.2]; decide⟩

end Witness

end Proof
