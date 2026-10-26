import Janus
import Extracted

/-!
# `CopyNodes(dst, src []*Node) int` on amd64: `copy(dst, src)`

**Guarantee.** As for arm64 (`examples/proofs/CopyNodes.lean`), with `dst` in `RAX, RBX, RCX`,
`src` in `RDI, RSI, R8`, the stack window `[RSP-4152, RSP+56)` and `runtime.typedslicecopy` given
by `RtContract64 … typedslicecopySpec`: `RAX = n = min(len dst, len src)`, the first `8n` bytes of
`dst` are the old first `8n` bytes of `src`, and memory changed only in `rt`, the stack window
and those bytes.

**What is assumed.** Only the contract hypothesis `hc`; `Witness` as for Concat
(`CopyNodes(nil, nil)`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
namespace Proof

/-- `*Node`'s type descriptor (the `LEA` before the call): the extraction's only data object. -/
def nodeType : Nat := dataBase Extracted.program 0

def Pre (rt : List (Nat × Nat)) (H : RtReady) (dp dl sp sl : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 4152 56 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4152) 4208 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
    dl.toNat < 2 ^ 63 ∧ sl.toNat < 2 ^ 63 ∧
    dp.toNat + 8 * min dl.toNat sl.toNat ≤ 2 ^ 48 ∧
    (0 < min dl.toNat sl.toNat → s.mem.accessible dp.toNat (8 * min dl.toNat sl.toNat) true = true) ∧
    Readable s.mem sp.toNat (8 * min dl.toNat sl.toNat) ∧
    Spec.Disjoint nodeType 16 ((s.regs 4).toNat - 4152) 4208 ∧
    Spec.Disjoint dp.toNat (8 * min dl.toNat sl.toNat) ((s.regs 4).toNat - 4152) 4208 ∧
    Spec.Disjoint sp.toNat (8 * min dl.toNat sl.toNat) ((s.regs 4).toNat - 4152) 4208 ∧
    H [nodeType, dp.toNat, dl.toNat, sp.toNat, sl.toNat] (s.regs 14).toNat ((s.regs 4).toNat - 56) (rtView rt s.mem)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (dp dl dc sp sl sc : BitVec 64)
    (hc : RtContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typedslicecopy")
      rt 4096 H typedslicecopySpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [dp, dl, dc, sp, sl, sc]
      (Pre rt H dp dl sp sl)
      (fun s s' => (s'.regs 0).toNat = min dl.toNat sl.toNat ∧
        (∀ i, i < 8 * min dl.toNat sl.toNat → s'.mem.bytes (dp.toNat + i) = s.mem.bytes (sp.toNat + i)) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4152, (s.regs 4).toNat + 56),
          (dp.toNat, dp.toNat + 8 * min dl.toNat sl.toNat)])) := by
  intro ret hret s hs ⟨hsg, ⟨hb, ha, hw⟩, hd, hout, hal, hdl, hsl, hdb, hdw, ⟨hs1, hs2⟩, hdt, hdd, hds, hH⟩
  janus64_intro hs
  janus_eval_nat h_ut : nodeType
  have hgl := hsg.load
  have hgb := hsg.below
  have hnw2 := hsg.noWrap
  have hgr := hsg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hb ha hw hout hal hdt hdd hds hH ⊢
  janus64_data hd [hw]
  rw [h_ut] at hH hdt
  have hdw' : 0 < min dl.toNat sl.toNat * 8 → s.mem.accessible dp.toNat (min dl.toNat sl.toNat * 8) true = true :=
    fun h => by rw [Nat.mul_comm]; exact hdw (by omega)
  have hs2' : 0 < min dl.toNat sl.toNat * 8 → s.mem.accessible sp.toNat (min dl.toNat sl.toNat * 8) false = true :=
    fun h => by rw [Nat.mul_comm]; exact hs2 (by omega)
  janus64_run [false_implies, implies_true, List.not_mem_nil, forall_const] calls [hc]
  rename_i r0 r1 r2 jk fl xm yh M1 zh kr hfr hpost
  obtain ⟨h0, hcp⟩ := hpost
  refine ⟨h0, fun i hi => ?_, by janus_frame⟩
  rw [hcp i (by omega)]
  repeat rw [Arm64.Memory.bytes_writeLE_outside _ (by omega)]

/-! ## Non-vacuity

Code at `runtime.typedslicecopy`'s address that meets the contract (`SatAmd64.constCode64 0 0 0`)
for the readiness `HA` (the call `typedslicecopy(*Node, nil, 0, nil, 0)`), `Sat.rtW`, and the call
`CopyNodes(nil, nil)` from `Sat`'s witness memory with the binary's read-only data and the return
address at `[RSP]` (`mem0`). -/

namespace Witness

open Janus.Contracts.SatAmd64
open Janus.Contracts.Sat (wsp wg wret rtW wmem HL)

def NT : Nat := dataBase Extracted.program 0
theorem nodeType_eq : nodeType = NT := rfl

def HA : RtReady := HL [NT, 0, 0, 0, 0] fun _ => True

def cAddr : Nat := Extracted.program.contractAddr "runtime.typedslicecopy"
def implAt : List Amd64.Segment := [{ name := "model", base := cAddr, bytes := constCode64 0 0 0 }]
def linked : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : RtContract64 (Extracted.program.link implAt) cAddr rtW 4096 HA typedslicecopySpec := by
  rw [linked_eq]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, -, -, -, hH⟩
  obtain ⟨ha, -⟩ := ready_of rfl hH
  janus64_run
  apply rtPost_const <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  have ha5 : argWords64 s 5 = [NT, 0, 0, 0, 0] := ha
  rw [ha5]
  simp [Copied]

def ret : Nat := wret
set_option maxRecDepth 100000 in
theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- `Sat.wmem` with the binary's read-only data at its address and the return address at `[RSP]`. -/
def mem0 : Arm64.Memory :=
  ⟨fun a => if NT ≤ a ∧ a < NT + 256 then
      BitVec.ofNat 8 (((Extracted.program.data[0]?.map (·.bytes)).getD []).getD (a - NT) 0)
    else if a = wsp + 2 then 0x20 else wmem.bytes a,
    wmem.regions ++ [⟨NT, 256, false⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [0, 0, 0, 0, 0, 0] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h; rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [s0, argReg, intArgRegs] at h ⊢ <;> omega, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded mem0 := by
  unfold Amd64.Program.DataLoaded
  decide

theorem pre : Pre rtW HA 0 0 0 0 s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, ?_⟩, dataLoaded,
    by simp only [rtW, outside_cons, outside_nil]; decide, by decide,
    by decide, by decide, by decide, fun h => absurd h (by decide), ⟨by decide, fun h => absurd h (by decide)⟩,
    by unfold Spec.Disjoint; decide, by unfold Spec.Disjoint; decide, by unfold Spec.Disjoint; decide, ?_⟩
  · have hw : mem0.accessible (wsp - 0x2000) 0x2100 true = true := by decide
    exact Arm64.Memory.accessible_mono _ hw (by decide) (by decide)
  · exact ⟨rfl, trivial⟩

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State),
    RtContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typedslicecopy")
      rt 4096 H typedslicecopySpec ∧ RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [0, 0, 0, 0, 0, 0] s ∧
    Pre rt H 0 0 0 0 s :=
  ⟨implAt, rtW, HA, ret, s0, model, hret, setup, pre⟩

/-- The witness call returns: nothing is copied. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = 0 :=
  (correctness implAt rtW HA 0 0 0 0 0 0 model ret hret s0 setup pre).mono fun _ h => ⟨h.1, by simpa using h.2.1⟩

end Witness

end Proof
