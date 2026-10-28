import Extracted

/-!
# `MulAlgo(n int) int`: a writable threshold global, under `GlobalsInit`

**Guarantee.** Extracted with `--global example.com/basic.karatsubaCut --global
example.com/basic.mulBias` (`scripts/example-targets.sh`). For every 64-bit `n` and every Go
call state of `example.com/basic.MulAlgo` in which both package variables hold their
link-time values (`GlobalsInit`: `karatsubaCut = 40` from `.noptrdata`, `mulBias = 0` from
`.noptrbss`, as copied from the ELF image into `Extracted.program.globals`), the call returns
(never faulting or panicking), obeys the ABI, and `X0 = 1` if `n < 40` (signed), else `2`: the
way math/big's `nat.mul` picks schoolbook or Karatsuba multiplication against
`karatsubaThreshold`.

**For every value (`forAllValues`).** The variables are writable, so a program may have changed
them. `forAllValues` holds for all values `cut` and `bias` the variables may hold
(`GlobalIs`): `X0 = bias + 1` if `n < cut` (signed), else `bias + 2`. `correctness` is its
instance at the link-time values (`GlobalsInit.globalIs`).

**Non-vacuity.** `Witness.nonvacuous`: the precondition holds in the link-time image itself
(`globalsImage`, `globalsInit_image`), for a concrete call `MulAlgo(0)`; `Witness.returns`: that
call returns `1`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem forAllValues (n : BitVec 64) (cut bias : Nat) :
    Ensures Extracted.program Extracted.entry [n]
      (fun s => GlobalIs Extracted.program.globals s.mem "example.com/basic.karatsubaCut" cut ∧
        GlobalIs Extracted.program.globals s.mem "example.com/basic.mulBias" bias)
      (fun _ s' => s'.regs 0 = if n.slt (BitVec.ofNat 64 cut) then BitVec.ofNat 64 bias + 1
        else BitVec.ofNat 64 bias + 2) := by
  intro ret hret s hs ⟨hc, hb⟩
  janus_intro hs
  obtain ⟨hca, hcr⟩ := hc.elim rfl
  obtain ⟨hba, hbr⟩ := hb.elim rfl
  simp only at hca hcr hba hbr
  have hca' := Memory.accessible_read_of_write _ hca
  have hba' := Memory.accessible_read_of_write _ hba
  janus_run
  all_goals
    rename_i hbr
    rw [hcr] at hbr
    split <;> rename_i hlt <;> simp only [BitVec.slt_iff_toInt_lt] at hlt
  · omega
  · rfl
  · rfl
  · omega

theorem correctness (n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n]
      (fun s => GlobalsInit Extracted.program.globals s.mem
        ["example.com/basic.karatsubaCut", "example.com/basic.mulBias"])
      (fun _ s' => s'.regs 0 = if n.slt 40#64 then 1#64 else 2#64) :=
  (forAllValues n 40 0).mono
    (fun _ h => ⟨h.globalIs (n := "example.com/basic.karatsubaCut") (by simp) rfl,
      h.globalIs (n := "example.com/basic.mulBias") (by simp) rfl⟩)
    (fun _ _ _ h => by rw [h]; split <;> rfl)

namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The link-time image of the two globals, over an otherwise empty memory. -/
def mem : Memory := globalsImage Extracted.program.globals ⟨fun _ => 0, []⟩

/-- The witness call state `MulAlgo(0)` on the link-time image. -/
def s0 : State :=
  { regs := fun i => if i = 30 then BitVec.ofNat 64 ret else 0, sp := 0x10000,
    pc := BitVec.ofNat 64 Extracted.entry, flags := ⟨false, false, false, false⟩, mem := mem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

theorem hpre : GlobalsInit Extracted.program.globals s0.mem
    ["example.com/basic.karatsubaCut", "example.com/basic.mulBias"] :=
  globalsInit_image _ _ _ (by decide) (by decide)

/-- All hypotheses of `correctness` hold together, in the link-time image. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s ∧
    GlobalsInit Extracted.program.globals s.mem
      ["example.com/basic.karatsubaCut", "example.com/basic.mulBias"] :=
  ⟨ret, s0, hret, setup, hpre⟩

/-- So the guarantee is reached: `MulAlgo(0)` returns `1` (schoolbook, `0 < 40`). -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = 1#64 := by
  refine (correctness 0#64 ret hret s0 setup hpre).mono ?_
  intro s' h
  exact ⟨h.1, by rw [h.2]; decide⟩

end Witness

end Proof
