import Janus
import Extracted

/-!
# `AppendPoint(s []Point, p Point) []Point` on amd64: `append(s, p)`

**Guarantee.** As for arm64 (`examples/proofs/AppendPoint.lean`), with the slice in
`RAX, RBX, RCX`, `p` in `RDI, RSI, R8`, the stack window `[RSP-4200, RSP+56)` and
`runtime.growslice` given by `RtContract64 … growsliceSpec`: with room left element `len` becomes
`p` and nothing else changes; when full, the result is a fresh array of capacity
`growCap 24 true (len+1) cap` inside `rt` holding the old elements, then `p`, then zeros.

**What is assumed.** Only the contract hypothesis `hg`; `Witness` as for arm64.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
namespace Proof

/-- `Point`'s type descriptor (the `LEA` before the call): the extraction's only data object. -/
def ptType : Nat := dataBase Extracted.program 0

def Pre (rt : List (Nat × Nat)) (H : RtReady) (ptr len cap : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 4200 56 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4200) 4256 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
    len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 40 ∧
    ptr.toNat + 24 * cap.toNat ≤ 2 ^ 48 ∧
    Spec.Disjoint ptr.toNat (24 * cap.toNat) ((s.regs 4).toNat - 4200) 4256 ∧
    Spec.Disjoint ptType 16 ((s.regs 4).toNat - 4200) 4256 ∧
    (len.toNat < cap.toNat → s.mem.accessible ptr.toNat (24 * cap.toNat) true = true) ∧
    (0 < len.toNat → s.mem.accessible ptr.toNat (24 * len.toNat) false = true) ∧
    (cap.toNat ≤ len.toNat →
      H [ptr.toNat, len.toNat + 1, cap.toNat, 1, ptType] (s.regs 14).toNat ((s.regs 4).toNat - 104)
        (rtView rt s.mem))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (ptr len cap x y z : BitVec 64)
    (hg : RtContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice")
      rt 4096 H growsliceSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [ptr, len, cap, x, y, z]
      (Pre rt H ptr len cap)
      (fun s s' => (s'.regs 3).toNat = len.toNat + 1 ∧
        (len.toNat < cap.toNat → s'.regs 0 = ptr ∧ s'.regs 1 = cap ∧
          s'.mem.readLE (ptr.toNat + 24 * len.toNat) 8 = x.toNat ∧
          s'.mem.readLE (ptr.toNat + 24 * len.toNat + 8) 8 = y.toNat ∧
          s'.mem.readLE (ptr.toNat + 24 * len.toNat + 16) 8 = z.toNat ∧
          MemFrame s.mem s'.mem [(ptr.toNat + 24 * len.toNat, ptr.toNat + 24 * len.toNat + 24),
            ((s.regs 4).toNat - 4200, (s.regs 4).toNat + 56)]) ∧
        (cap.toNat ≤ len.toNat →
          (s'.regs 1).toNat = growCap 24 true (len.toNat + 1) cap.toNat ∧
          InRanges (s'.regs 0).toNat (growCap 24 true (len.toNat + 1) cap.toNat * 24) rt ∧
          s'.mem.accessible (s'.regs 0).toNat (growCap 24 true (len.toNat + 1) cap.toNat * 24) true = true ∧
          (∀ i, i < 24 * len.toNat → s'.mem.bytes ((s'.regs 0).toNat + i) = s.mem.bytes (ptr.toNat + i)) ∧
          s'.mem.readLE ((s'.regs 0).toNat + 24 * len.toNat) 8 = x.toNat ∧
          s'.mem.readLE ((s'.regs 0).toNat + 24 * len.toNat + 8) 8 = y.toNat ∧
          s'.mem.readLE ((s'.regs 0).toNat + 24 * len.toNat + 16) 8 = z.toNat ∧
          ZeroBytes s'.mem ((s'.regs 0).toNat + 24 * (len.toNat + 1))
            (growCap 24 true (len.toNat + 1) cap.toNat * 24 - 24 * (len.toNat + 1)) ∧
          MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 56)]))) := by
  intro ret hret s hs ⟨hsg, ⟨hb, ha, hw⟩, hd, hout, hal, hlc, hc, hpb, hdj, hdt, hwr, hrd, hHf⟩
  janus64_intro hs
  janus_eval_nat h_ut : ptType
  have hgl := hsg.load
  have hgb := hsg.below
  have hnw2 := hsg.noWrap
  have hgr := hsg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hb ha hw hout hal hdj hdt hHf ⊢
  janus64_data hd [hw]
  rw [h_ut] at hdt
  by_cases hl : len.toNat < cap.toNat
  · have hw' := hwr hl
    janus64_run
    exact ⟨fun _ => by janus_frame, fun h => absurd h (by omega)⟩
  · have hH := hHf (by omega)
    rw [h_ut] at hH
    clear hHf
    have hrd' : 0 < len.toNat * 24 → s.mem.accessible ptr.toNat (len.toNat * 24) false = true :=
      fun h => by rw [Nat.mul_comm]; exact hrd (by omega)
    janus64_run [false_implies, implies_true, List.not_mem_nil, forall_const] until [Extracted.entry + 0x3b] calls [hg]
    rename_i r0 r1 r2 jk fl xm yh M1 hfr hpost
    obtain ⟨hr1, hr2, hin, hlt, hacc, hcp, hz, -⟩ := hpost
    have hle := le_growCap 24 true (len.toNat + 1) cap.toNat (by decide)
    have hdj2 := InRanges.disjoint hin hout
    have hacc2 : M1.accessible (r0.toNat + 24 * len.toNat) 24 true = true :=
      Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
    have hacc0 : s.mem.accessible (r0.toNat + 24 * len.toNat) 24 true = true := by
      have := hfr.accessible (r0.toNat + 24 * len.toNat) 24 true
      simp only [Arm64.Memory.accessible_writeLE] at this
      rw [← this]; exact hacc2
    janus64_run
    refine ⟨hr1, fun h => absurd h hl, fun _ => ⟨hr2, by rw [← hr2]; exact hin, ?_, ?_, ?_, by janus_frame⟩⟩
    · have := hfr.accessible r0.toNat (r2.toNat * 24) true
      simp only [Arm64.Memory.accessible_writeLE] at this
      rw [← hr2, ← this]; exact hacc
    · intro i hi
      rw [Arm64.Memory.bytes_writeLE_outside _ (by omega), Arm64.Memory.bytes_writeLE_outside _ (by omega),
        Arm64.Memory.bytes_writeLE_outside _ (by omega), hcp i (by omega)]
      repeat rw [Arm64.Memory.bytes_writeLE_outside _ (by omega)]
    · intro i hi
      rw [Arm64.Memory.bytes_writeLE_outside _ (by omega), Arm64.Memory.bytes_writeLE_outside _ (by omega),
        Arm64.Memory.bytes_writeLE_outside _ (by omega)]
      have := hz i (by omega)
      rwa [Nat.mul_comm (len.toNat + 1) 24] at this

/-! ## Non-vacuity

As on arm64: code at `runtime.growslice`'s address meeting the contract
(`SatAmd64.constCode64 HEAP 1 1`) for the readiness `HA`, the ranges `rtA` (`Sat.rtW` and the
descriptor), and the call `AppendPoint(nil, p)` from `Sat`'s witness memory with the binary's
read-only data and the return address at `[RSP]`. -/

namespace Witness

open Janus.Contracts.SatAmd64
open Janus.Contracts.Sat (wsp wg wret rtW wmem HL HEAP)

def PT : Nat := dataBase Extracted.program 0
theorem ptType_eq : ptType = PT := rfl

def rtA : List (Nat × Nat) := rtW ++ [(PT, PT + 256)]

def PA (v : Arm64.Memory) : Prop := v.readLE PT 8 = 24 ∧ v.readLE (PT + 8) 8 = 0 ∧ v.accessible HEAP 24 true = true
def HA : RtReady := HL [0, 1, 0, 1, PT] PA

def cAddr : Nat := Extracted.program.contractAddr "runtime.growslice"
def implAt : List Amd64.Segment := [{ name := "model", base := cAddr, bytes := constCode64 HEAP 1 1 }]
def linked : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem pt_in : InRanges PT 16 rtA := ⟨(PT, PT + 256), by simp [rtA], Nat.le_refl _, by decide⟩
theorem heap_in : InRanges HEAP 24 rtA := ⟨(HEAP, HEAP + 0x10000), by simp [rtA, rtW], Nat.le_refl _, by decide⟩

theorem model : RtContract64 (Extracted.program.link implAt) cAddr rtA 4096 HA growsliceSpec := by
  rw [linked_eq]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, -, -, -, hH⟩
  obtain ⟨ha, h1, h2, h3⟩ := ready_of rfl hH
  janus64_run
  apply rtPost_const <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  rw [readLE_rtView (pt_in.sub (Nat.le_refl _) (by decide))] at h1
  rw [readLE_rtView (pt_in.sub (by decide) (by decide))] at h2
  rw [rtView_accessible] at h3
  have ha5 : argWords64 s 5 = [0, 1, 0, 1, PT] := ha
  rw [ha5]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, h1, h2]
  exact ⟨trivial, by decide, heap_in, by decide, h3, fun i h => absurd h (by omega),
    fun i h => absurd h (by omega), fun h => by simp at h⟩

def ret : Nat := wret
set_option maxRecDepth 100000 in
theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- `Sat.wmem` with the binary's read-only data at its address and the return address at `[RSP]`. -/
def mem0 : Arm64.Memory :=
  ⟨fun a => if PT ≤ a ∧ a < PT + 256 then
      BitVec.ofNat 8 (((Extracted.program.data[0]?.map (·.bytes)).getD []).getD (a - PT) 0)
    else if a = wsp + 2 then 0x20 else wmem.bytes a,
    wmem.regions ++ [⟨PT, 256, false⟩]⟩

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

theorem pre : Pre rtA HA 0 0 0 s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, ?_⟩, dataLoaded,
    by simp only [rtA, rtW, List.cons_append, List.nil_append, outside_cons, outside_nil]; decide, by decide,
    by decide, by decide, by decide, by unfold Spec.Disjoint; decide, by unfold Spec.Disjoint; decide,
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ?_⟩
  · have hw : mem0.accessible (wsp - 0x2000) 0x2100 true = true := by decide
    exact Arm64.Memory.accessible_mono _ hw (by decide) (by decide)
  · exact ⟨rfl, by decide, by decide, by decide⟩

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State),
    RtContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice")
      rt 4096 H growsliceSpec ∧ RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [0, 0, 0, 0, 0, 0] s ∧
    Pre rt H 0 0 0 s :=
  ⟨implAt, rtA, HA, ret, s0, model, hret, setup, pre⟩

/-- The witness call returns: the result has length 1. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 3).toNat = 1 :=
  (correctness implAt rtA HA 0 0 0 0 0 0 model ret hret s0 setup pre).mono fun _ h => ⟨h.1, by simpa using h.2.1⟩

end Witness

end Proof
