import Janus
import Extracted

/-!
# `MulAlgo(n int) int` (amd64): a writable threshold global, under `GlobalsInit`

**Guarantee.** Extracted with `--global example.com/basic.karatsubaCut --global
example.com/basic.mulBias` (`scripts/example-targets.sh`). For every 64-bit `n` and every Go call
state of `example.com/basic.MulAlgo` whose return-address slot `[RSP, RSP+8)` is writable and in
which both package variables hold their link-time values (`GlobalsInit`: `karatsubaCut = 40`
from `.noptrdata`, `mulBias = 0` from `.noptrbss`, copied from the ELF image into
`Extracted.program.globals`), the call returns (never faulting or panicking), obeys the ABI, and
`RAX = 1` if `n < 40` (signed), else `2`: the way math/big's `nat.mul` compares against
`karatsubaThreshold`. The code reads both globals RIP-relative (`CMPQ karatsubaCut(SB), AX`,
`MOVQ mulBias(SB), AX`).

**For every value (`forAllValues`).** For all values `cut`, `bias` the writable variables may
hold (`GlobalIs`): `RAX = bias + 1` if `n < cut` (signed), else `bias + 2`. `correctness` is its
instance at the link-time values (`GlobalsInit.globalIs`).

**Non-vacuity.** `Witness.nonvacuous`: the precondition holds in the link-time image
(`globalsImage`, `globalsInit_image`) for the call `MulAlgo(0)`; `Witness.returns`: it returns `1`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec

namespace Proof

theorem forAllValues (n : BitVec 64) (cut bias : Nat) :
    Ensures Extracted.program Extracted.entry [n]
      (fun s => StackWritable s 0 8 ∧
        GlobalIs Extracted.program.globals s.mem "example.com/basic.karatsubaCut" cut ∧
        GlobalIs Extracted.program.globals s.mem "example.com/basic.mulBias" bias)
      (fun _ s' => results 1 s' = [if n.slt (BitVec.ofNat 64 cut) then BitVec.ofNat 64 bias + 1
        else BitVec.ofNat 64 bias + 2]) := by
  intro ret hret s hs ⟨hsw, hc, hb⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hsw
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  obtain ⟨hca, hcr⟩ := hc.elim rfl
  obtain ⟨hba, hbr⟩ := hb.elim rfl
  simp only at hca hcr hba hbr
  have hca' := Janus.Arm64.Memory.accessible_read_of_write _ hca
  have hba' := Janus.Arm64.Memory.accessible_read_of_write _ hba
  janus64_run
  all_goals
    rename_i hbr
    split <;> rename_i hlt <;> simp only [BitVec.slt_iff_toInt_lt] at hlt
  all_goals first
    | omega
    | rfl
    | (congr 1; done)
    | (congr 1; apply BitVec.eq_of_toNat_eq; simp)

theorem correctness (n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n]
      (fun s => StackWritable s 0 8 ∧ GlobalsInit Extracted.program.globals s.mem
        ["example.com/basic.karatsubaCut", "example.com/basic.mulBias"])
      (fun _ s' => results 1 s' = [if n.slt 40#64 then 1#64 else 2#64]) :=
  (forAllValues n 40 0).mono
    (fun _ ⟨hs, h⟩ => ⟨hs, h.globalIs (n := "example.com/basic.karatsubaCut") (by simp) rfl,
      h.globalIs (n := "example.com/basic.mulBias") (by simp) rfl⟩)
    (fun _ _ _ h => by rw [h]; split <;> rfl)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The link-time image of the two globals over `EqHashModel.wmem64` (which holds the return
address `wret` at `[wsp]`). -/
def mem : Memory := globalsImage Extracted.program.globals wmem64

/-- The witness call state `MulAlgo(0)`: `RSP = wsp`, on the link-time image. -/
def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ GlobalsInit Extracted.program.globals s0.mem
    ["example.com/basic.karatsubaCut", "example.com/basic.mulBias"] :=
  ⟨⟨by decide, by decide, by decide⟩, globalsInit_image _ _ _ (by decide) (by decide)⟩

/-- All hypotheses of `correctness` hold together, in the link-time image. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s ∧
    (StackWritable s 0 8 ∧ GlobalsInit Extracted.program.globals s.mem
      ["example.com/basic.karatsubaCut", "example.com/basic.mulBias"]) :=
  ⟨ret, s0, hret, setup, hpre⟩

/-- So the guarantee is reached: `MulAlgo(0)` returns `1` (schoolbook, `0 < 40`). -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ results 1 s' = [1#64] := by
  refine (correctness 0#64 ret hret s0 setup hpre).mono ?_
  intro s' h
  exact ⟨h.1, by rw [h.2]; decide⟩

end Witness

end Proof
