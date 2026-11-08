import Janus
import Extracted

/-! `example.com/basic.Add128` on amd64 (`ADDQ DI, BX; ADCQ CX, AX; RET`): the 128-bit sum of
`xh:xl` and `yh:yl`, modulo `2^128`, returned as `(hi, lo)` in `RAX`, `RBX`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (xh xl yh yl : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [xh, xl, yh, yl] 2
      (fun s => StackWritable s 0 8)
      (fun r => ∃ hi lo, r = [hi, lo] ∧
        hi.toNat * 2 ^ 64 + lo.toNat =
          (xh.toNat * 2 ^ 64 + xl.toNat + (yh.toNat * 2 ^ 64 + yl.toNat)) % 2 ^ 128) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  refine ⟨_, _, rfl, ?_⟩
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
  have := xl.isLt; have := yl.isLt; have := xh.isLt; have := yh.isLt
  omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def xh : BitVec 64 := 1#64
def xl : BitVec 64 := 0xFFFFFFFFFFFFFFFF#64
def yh : BitVec 64 := 2#64
def yl : BitVec 64 := 3#64

def s0 : State :=
  { regs := fun i => if i = 0 then xh else if i = 3 then xl else if i = 1 then yh else if i = 7 then yl else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [xh, xl, yh, yl] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (xh : BitVec 64) (xl : BitVec 64) (yh : BitVec 64) (yl : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [xh, xl, yh, yl] s ∧ (StackWritable s 0 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ ∃ hi lo, (results 2 s') = [hi, lo] ∧
        hi.toNat * 2 ^ 64 + lo.toNat =
          (xh.toNat * 2 ^ 64 + xl.toNat + (yh.toNat * 2 ^ 64 + yl.toNat)) % 2 ^ 128) :=
  ⟨ret, s0, xh, xl, yh, yl, hret, setup, hpre, correctness xh xl yh yl ret hret s0 setup hpre⟩

end Witness

end Proof
