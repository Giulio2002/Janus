import Janus
import Extracted

/-!
# `MulAlgo(n int) int` (amd64): a writable threshold global, under `GlobalsInit`

**Guarantee.** Extracted with `--global example.com/basic.karatsubaCut --global
example.com/basic.mulBias` (`scripts/verify/example-targets.sh`). For every 64-bit `n` and every Go call
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

/-- The named global lies apart from the return slot `[rsp, rsp + 8)` (the precondition no longer sees the return
address, so the global must not be the slot). -/
def GlobalApart (gs : List Janus.GlobalSegment) (n : String) (rsp : Nat) : Prop :=
  ∀ g, globalNamed gs n = some g → rsp + 8 ≤ g.base ∨ g.base + g.size ≤ rsp

theorem GlobalApart.of_eq {gs : List Janus.GlobalSegment} {n : String} {g : Janus.GlobalSegment} {rsp : Nat}
    (hg : globalNamed gs n = some g) (h : rsp + 8 ≤ g.base ∨ g.base + g.size ≤ rsp) : GlobalApart gs n rsp :=
  fun g' hg' => by rw [hg] at hg'; cases hg'; exact h

/-- `GlobalIs` survives writing the return slot, when the global is apart from it. -/
theorem globalIs_setRet {gs : List Janus.GlobalSegment} {n : String} {v : Nat} {s : State} {ret : Nat}
    (hap : GlobalApart gs n (s.regs 4).toNat) (h : GlobalIs gs s.mem n v) :
    GlobalIs gs (s.setRet ret).mem n v := by
  obtain ⟨g, hg, h2, h3⟩ := h
  have := hap g hg
  refine ⟨g, hg, by simpa using h2, ?_⟩
  rw [readLE_setRet_of_disjoint (by omega)]
  exact h3

theorem forAllValues (n : BitVec 64) (cut bias : Nat) :
    Ensures Extracted.program Extracted.entry [n]
      (fun s => StackWritable s 0 8 ∧
        GlobalApart Extracted.program.globals "example.com/basic.karatsubaCut" (s.regs regSP).toNat ∧
        GlobalApart Extracted.program.globals "example.com/basic.mulBias" (s.regs regSP).toNat ∧
        GlobalIs Extracted.program.globals s.mem "example.com/basic.karatsubaCut" cut ∧
        GlobalIs Extracted.program.globals s.mem "example.com/basic.mulBias" bias)
      (fun _ s' => results 1 s' = [if n.slt (BitVec.ofNat 64 cut) then BitVec.ofNat 64 bias + 1
        else BitVec.ofNat 64 bias + 2]) := by
  refine Ensures.of_old (fun s ret _ _ hp => ?_) ?_
  · obtain ⟨hw, hac, hab, hc, hb⟩ := hp
    exact ⟨by simpa [StackWritable] using hw, hac, hab, globalIs_setRet hac hc, globalIs_setRet hab hb⟩
  intro ret hret s hs ⟨hsw, _, _, hc, hb⟩
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
      (fun s => StackWritable s 0 8 ∧
        GlobalApart Extracted.program.globals "example.com/basic.karatsubaCut" (s.regs regSP).toNat ∧
        GlobalApart Extracted.program.globals "example.com/basic.mulBias" (s.regs regSP).toNat ∧
        GlobalsInit Extracted.program.globals s.mem
        ["example.com/basic.karatsubaCut", "example.com/basic.mulBias"])
      (fun _ s' => results 1 s' = [if n.slt 40#64 then 1#64 else 2#64]) :=
  (forAllValues n 40 0).mono_ret
    (fun _ ⟨hs, hac, hab, h⟩ => ⟨hs, hac, hab, h.globalIs (n := "example.com/basic.karatsubaCut") (by simp) rfl,
      h.globalIs (n := "example.com/basic.mulBias") (by simp) rfl⟩)
    (fun _ _ _ _ h => by rw [h]; split <;> rfl)

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

theorem setup : CallSetup0 Extracted.entry [0#64] s0 :=
  ⟨rfl, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem apartCut : GlobalApart Extracted.program.globals "example.com/basic.karatsubaCut" (s0.regs regSP).toNat :=
  GlobalApart.of_eq rfl (by decide)

theorem apartBias : GlobalApart Extracted.program.globals "example.com/basic.mulBias" (s0.regs regSP).toNat :=
  GlobalApart.of_eq rfl (by decide)

theorem hpre : StackWritable s0 0 8 ∧
    GlobalApart Extracted.program.globals "example.com/basic.karatsubaCut" (s0.regs regSP).toNat ∧
    GlobalApart Extracted.program.globals "example.com/basic.mulBias" (s0.regs regSP).toNat ∧
    GlobalsInit Extracted.program.globals s0.mem
    ["example.com/basic.karatsubaCut", "example.com/basic.mulBias"] :=
  ⟨(by first | exact ⟨by decide, by decide, by decide, by decide⟩ | exact ⟨by decide, by decide, by decide⟩), apartCut, apartBias, globalsInit_image _ _ _ (by decide) (by decide)⟩

/-- So the guarantee is reached: `MulAlgo(0)` returns `1` (schoolbook, `0 < 40`). -/
theorem returns : Returns (Extracted.program.withExit ret) (s0.setRet ret) fun s' =>
    ABIReturn (s0.setRet ret) s' ∧ results 1 s' = [1#64] := by
  refine ((correctness 0#64) s0 setup hpre ret hret).mono ?_
  intro s' h
  exact ⟨h.1, by rw [h.2]; decide⟩

/-- All hypotheses of `correctness` hold together, in the link-time image. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CallSetup0 Extracted.entry [0#64] s ∧
    (StackWritable s 0 8 ∧
      GlobalApart Extracted.program.globals "example.com/basic.karatsubaCut" (s.regs regSP).toNat ∧
      GlobalApart Extracted.program.globals "example.com/basic.mulBias" (s.regs regSP).toNat ∧
      GlobalsInit Extracted.program.globals s.mem
      ["example.com/basic.karatsubaCut", "example.com/basic.mulBias"]) ∧
    (Returns (Extracted.program.withExit ret) (s.setRet ret) fun s' =>
    ABIReturn (s.setRet ret) s' ∧ results 1 s' = [1#64]) :=
  ⟨ret, s0, hret, setup, hpre, returns⟩

/-- All hypotheses of `forAllValues` hold together (cut 40, bias 0, in the link-time image), and the call returns. -/
theorem forAllValues : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CallSetup0 Extracted.entry [0#64] s ∧
    (StackWritable s 0 8 ∧
        GlobalApart Extracted.program.globals "example.com/basic.karatsubaCut" (s.regs regSP).toNat ∧
        GlobalApart Extracted.program.globals "example.com/basic.mulBias" (s.regs regSP).toNat ∧
        GlobalIs Extracted.program.globals s.mem "example.com/basic.karatsubaCut" 40 ∧
        GlobalIs Extracted.program.globals s.mem "example.com/basic.mulBias" 0) ∧
    (Returns (Extracted.program.withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ results 1 s' = [if (0#64).slt (BitVec.ofNat 64 40) then BitVec.ofNat 64 0 + 1
        else BitVec.ofNat 64 0 + 2]) :=
  ⟨ret, s0, hret, setup, ⟨hpre.1, hpre.2.1, hpre.2.2.1, hpre.2.2.2.globalIs (n := "example.com/basic.karatsubaCut") (by simp) rfl,
      hpre.2.2.2.globalIs (n := "example.com/basic.mulBias") (by simp) rfl⟩,
    (Proof.forAllValues 0#64 40 0) s0 setup ⟨hpre.1, hpre.2.1, hpre.2.2.1, hpre.2.2.2.globalIs (n := "example.com/basic.karatsubaCut") (by simp) rfl,
      hpre.2.2.2.globalIs (n := "example.com/basic.mulBias") (by simp) rfl⟩ ret hret⟩

end Witness

end Proof
