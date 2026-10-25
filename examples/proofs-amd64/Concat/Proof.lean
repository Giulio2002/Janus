import Janus
import Extracted

/-!
# `Concat(a, b string) string` on amd64: `a + b`

**Guarantee.** As for arm64 (`examples/proofs/Concat.lean`), with `a` in `RAX, RBX`, `b` in
`RCX, RDI`, the stack window `[RSP-4152, RSP+40)` and `runtime.concatstring2` given by
`RtContract64 … (concatstringSpec 2)`: the result `(RAX, RBX)` holds the bytes of `a` followed by
those of `b`.

**What is assumed.** Only the contract hypothesis `hc`; `Witness` shows the hypotheses are
satisfiable together and the witness call returns.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
namespace Proof

def Pre (rt : List (Nat × Nat)) (H : RtReady) (ap an bp bn : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 4152 40 ∧ Outside ((s.regs 4).toNat - 4152) 4192 rt ∧
    (s.regs 4).toNat % 8 = 0 ∧
    StrIn s.mem ap.toNat an.toNat ∧ StrIn s.mem bp.toNat bn.toNat ∧
    Outside ap.toNat an.toNat [((s.regs 4).toNat - 4152, (s.regs 4).toNat + 40)] ∧
    Outside bp.toNat bn.toNat [((s.regs 4).toNat - 4152, (s.regs 4).toNat + 40)] ∧
    H [0, ap.toNat, an.toNat, bp.toNat, bn.toNat] (s.regs 14).toNat ((s.regs 4).toNat - 56) (rtView rt s.mem)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ap an bp bn : BitVec 64)
    (hc : RtContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.concatstring2")
      rt 4096 H (concatstringSpec 2)) :
    Ensures (Extracted.program.link impl) Extracted.entry [ap, an, bp, bn] (Pre rt H ap an bp bn)
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat
        (strBytes s.mem ap.toNat an.toNat ++ strBytes s.mem bp.toNat bn.toNat)) := by
  intro ret hret s hs ⟨hsg, ⟨hb, ha, hw⟩, hout, hal, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hao, hbo, hH⟩
  janus64_intro hs
  have hgl := hsg.load
  have hgb := hsg.below
  have hnw2 := hsg.noWrap
  have hgr := hsg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal hao hbo hH ⊢
  simp only [outside_cons, outside_nil, and_true] at hao hbo
  janus64_run [false_implies, implies_true, List.not_mem_nil, forall_const] calls [hc]
  all_goals assumption

/-! ## Non-vacuity -/

namespace Witness

open Janus.Contracts.SatAmd64
open Janus.Contracts.Sat (wsp wg wret rtW wmem H0)

def cAddr : Nat := Extracted.program.contractAddr "runtime.concatstring2"
def implAt : List Amd64.Segment := [{ name := "model", base := cAddr, bytes := constCode64 0 0 0 }]
def linked : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : RtContract64 (Extracted.program.link implAt) cAddr rtW 4096 H0 (concatstringSpec 2) := by
  rw [linked_eq]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, -, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, H0, arg, List.getD_eq_getElem?_getD] at ha
  janus64_run
  apply rtPost_const <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  simp only [concatstringSpec] at ha ⊢
  simp [ha, strBytes]

def ret : Nat := wret
theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- `wmem` with the return address at `[RSP]`. -/
def mem0 : Janus.Arm64.Memory := ⟨fun a => if a = wsp + 2 then 0x20 else wmem.bytes a, wmem.regions⟩

def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [0, 0, 0, 0] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases i with _ | _ | _ | _ | i <;> simp [s0, argReg, intArgRegs] at h ⊢ <;> omega, rfl⟩

theorem pre : Pre rtW H0 0 0 0 0 s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, ?_⟩,
    by simp only [rtW, outside_cons, outside_nil]; decide, by decide,
    ⟨by decide, by simp⟩, ⟨by decide, by simp⟩, by simp only [outside_cons, outside_nil]; decide,
    by simp only [outside_cons, outside_nil]; decide, ?_⟩
  · have hw : mem0.accessible (wsp - 0x2000) 0x2100 true = true := by decide
    exact Janus.Arm64.Memory.accessible_mono _ hw (by decide) (by decide)
  · intro j; simp [arg, List.getD_eq_getElem?_getD]; rcases j with _ | _ | _ | _ | _ | j <;> simp

theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State),
    RtContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.concatstring2")
      rt 4096 H (concatstringSpec 2) ∧ RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [0, 0, 0, 0] s ∧ Pre rt H 0 0 0 0 s :=
  ⟨implAt, rtW, H0, ret, s0, model, hret, setup, pre⟩

theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat
      (strBytes s0.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat ++ strBytes s0.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat) :=
  correctness implAt rtW H0 0 0 0 0 model ret hret s0 setup pre

end Witness

end Proof
