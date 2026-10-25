import Extracted

/-!
# `CopyNodes(dst, src []*Node) int` is `copy(dst, src)` (arm64)

**Guarantee.** For every pair of slices `dst = (dp, dl, ·)`, `src = (sp, sl, ·)` with
`n = min dl sl` and both lengths below `2^63`, every `rt`, every readiness predicate `H` and
**every** implementation of `runtime.typedslicecopy` satisfying its contract
(`RtContract … typedslicecopySpec`, `Janus/Contracts/Slice.lean`: with the GC's bulk write
barrier when it is marking), and every Go call state of `example.com/basic.CopyNodes` in which the
stack-growth prologue falls through, with the read-only data loaded, the stack window
`[SP-4160, SP+56)` writable, outside `rt` and disjoint from `*Node`'s type descriptor and the
first `8n` bytes of both arrays, those bytes writable in `dst` and readable in `src`, and the
runtime ready for the call `typedslicecopy(*Node, dp, dl, sp, sl)`: the call returns, obeys the
ABI, `X0 = n`, the first `8n` bytes of `dst` are the old first `8n` bytes of `src` (the `n`
pointers; overlap allowed, as `memmove`), and memory changed only in `rt`, the stack window and
those bytes of `dst`.

**What is assumed.** The contract (hypothesis `hc`). `Witness` shows the hypotheses are
satisfiable together (`CopyNodes(nil, nil)`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
namespace Proof

def nodeType : Nat :=
  adrpLdTarget (Extracted.entry + 0x28) (segWord Extracted.program "example.com/basic.CopyNodes" 10)
    (segWord Extracted.program "example.com/basic.CopyNodes" 11) 0

def Pre (rt : List (Nat × Nat)) (H : RtReady) (dp dl sp sl : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 4160 56 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4160) 4216 rt ∧ dl.toNat < 2 ^ 63 ∧ sl.toNat < 2 ^ 63 ∧
    dp.toNat + 8 * min dl.toNat sl.toNat ≤ 2 ^ 48 ∧
    (0 < min dl.toNat sl.toNat → s.mem.accessible dp.toNat (8 * min dl.toNat sl.toNat) true = true) ∧
    Readable s.mem sp.toNat (8 * min dl.toNat sl.toNat) ∧
    Disjoint nodeType 16 (s.sp.toNat - 4160) 4216 ∧
    Disjoint dp.toNat (8 * min dl.toNat sl.toNat) (s.sp.toNat - 4160) 4216 ∧
    Disjoint sp.toNat (8 * min dl.toNat sl.toNat) (s.sp.toNat - 4160) 4216 ∧
    H [nodeType, dp.toNat, dl.toNat, sp.toNat, sl.toNat] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (dp dl dc sp sl sc : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typedslicecopy")
      rt 4096 H typedslicecopySpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [dp, dl, dc, sp, sl, sc]
      (Pre rt H dp dl sp sl)
      (fun s s' => (s'.regs 0).toNat = min dl.toNat sl.toNat ∧
        (∀ i, i < 8 * min dl.toNat sl.toNat → s'.mem.bytes (dp.toNat + i) = s.mem.bytes (sp.toNat + i)) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4160, s.sp.toNat + 56),
          (dp.toNat, dp.toNat + 8 * min dl.toNat sl.toNat)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hdl, hsl, hdb, hdw, ⟨hs1, hs2⟩, hdt, hdd, hds, hH⟩
  janus_intro hs
  janus_eval_nat h_ut : nodeType
  janus_data hd [hw]
  simp only [Disjoint] at hdt hdd hds
  rw [h_ut] at hH
  have hdw' : 0 < min dl.toNat sl.toNat * 8 → s.mem.accessible dp.toNat (min dl.toNat sl.toNat * 8) true = true :=
    fun h => by rw [Nat.mul_comm]; exact hdw (by omega)
  have hs2' : 0 < min dl.toNat sl.toNat * 8 → s.mem.accessible sp.toNat (min dl.toNat sl.toNat * 8) false = true :=
    fun h => by rw [Nat.mul_comm]; exact hs2 (by omega)
  janus_run [false_implies, implies_true, List.not_mem_nil, forall_const] calls [hc]
  rename_i r0 r1 r2 jk fl vr M1 hfr hpost
  obtain ⟨h0, hcp⟩ := hpost
  refine ⟨h0, fun i hi => ?_, by janus_frame⟩
  rw [hcp i (by omega)]
  repeat rw [Memory.bytes_writeLE_outside _ (by omega)]

/-! ## Non-vacuity

Code at `runtime.typedslicecopy`'s address that meets the contract (`Sat.constCode 0 0 0`) for
the readiness `HA` (the call `typedslicecopy(*Node, nil, 0, nil, 0)`), `Sat.rtW`, and the call
`CopyNodes(nil, nil)` from `Sat`'s witness memory with the binary's read-only data (`wmemD`). -/

namespace Witness

open Janus.Contracts.Sat

def NT : Nat := ((Extracted.program.data[0]?).map (·.base)).getD 0
theorem nodeType_eq : nodeType = NT := by decide

def HA : RtReady := HL [NT, 0, 0, 0, 0] fun _ => True

def cAddr : Nat := Extracted.program.contractAddr "runtime.typedslicecopy"
def implAt : List Segment := [{ name := "model", base := cAddr, words := constCode 0 0 0 }]
def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : RtContract (Extracted.program.link implAt) cAddr rtW 4096 HA typedslicecopySpec := by
  rw [linked_eq]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, -, -, -, hH⟩
  obtain ⟨ha, -⟩ := ready_of rfl hH
  janus_run
  apply rtPost_const <;> (try rfl) <;> (try simp [setReg])
  have ha5 : argWords s 5 = [NT, 0, 0, 0, 0] := ha
  rw [ha5]
  simp [Copied]

def ret : Nat := wret
set_option maxRecDepth 100000 in
theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- `Sat.wmem` with the binary's read-only data at its address. -/
def wmemD : Memory :=
  ⟨fun a => if NT ≤ a ∧ a < NT + 256 then
      BitVec.ofNat 8 (((Extracted.data.head?.map (·.bytes)).getD []).getD (a - NT) 0) else wmem.bytes a,
    wmem.regions ++ [⟨NT, 256, false⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmemD }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [0, 0, 0, 0, 0, 0] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded wmemD := by
  intro d hd
  have hd' : d ∈ Extracted.data := hd
  simp only [Extracted.data, List.mem_singleton] at hd'
  subst hd'
  refine ⟨by decide, ?_⟩
  intro i h
  simp only [wmemD, Extracted.data] at h ⊢
  have : i < 256 := h
  revert i; decide

theorem pre : Pre rtW HA 0 0 0 0 s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, ?_⟩, dataLoaded,
    by simp only [rtW, outside_cons, outside_nil]; decide,
    by decide, by decide, by decide, fun h => absurd h (by decide), ⟨by decide, fun h => absurd h (by decide)⟩,
    by rw [nodeType_eq]; unfold Disjoint; decide, by simp [Disjoint], by simp [Disjoint], ?_⟩
  · have hw : wmemD.accessible (wsp - 0x2000) 0x2100 true = true := by decide
    exact Memory.accessible_mono _ hw (by decide) (by decide)
  · rw [nodeType_eq]; exact ⟨rfl, trivial⟩

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State),
    RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typedslicecopy")
      rt 4096 H typedslicecopySpec ∧ RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [0, 0, 0, 0, 0, 0] s ∧
    Pre rt H 0 0 0 0 s :=
  ⟨implAt, rtW, HA, ret, s0, model, hret, setup, pre⟩

/-- The witness call returns: nothing is copied (the full theorem's conclusion holds; this
states its first part). -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = 0 :=
  (correctness implAt rtW HA 0 0 0 0 0 0 model ret hret s0 setup pre).mono fun _ h => ⟨h.1, by simpa using h.2.1⟩

end Witness

end Proof
