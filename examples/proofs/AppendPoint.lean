import Extracted

/-!
# `AppendPoint(s []Point, p Point) []Point` is `append(s, p)` (arm64)

`Point` is a 24-byte struct without pointers (`examples/basic/zstr.go`).

**Guarantee.** For every slice `(ptr, len, cap)` with `len ≤ cap < 2^40`, every `p = (x, y, z)`,
every list `rt` of runtime-owned ranges, every readiness predicate `H` and **every**
implementation of `runtime.growslice` satisfying its contract for any element type
(`RtContract … growsliceSpec`, `Janus/Contracts/Slice.lean`), and every Go call state of
`example.com/basic.AppendPoint` in which the stack-growth prologue falls through, with the read-only
data loaded, the stack window `[SP-4208, SP+56)` writable, outside `rt` and disjoint from the
array and from `Point`'s type descriptor, the array writable when `len < cap` and its `len`
elements readable when `len > 0`, and the runtime ready (`H`) for the call
`growslice(ptr, len+1, cap, 1, Point)` when the slice is full: the call returns, obeys the ABI,
the result has length `len + 1`, and

* **room left** (`len < cap`): the result is `(ptr, len+1, cap)`, element `len` is `p`, and only
  that element (and the stack window) changed;
* **growth** (`len = cap`): the capacity is `growCap 24 true (len+1) cap` (Go's `nextslicecap`
  rounded up to the size class, divided by 24), the new array lies inside `rt`, is writable, its
  first `24·len` bytes are the old elements, element `len` is `p`, the bytes after it are zero,
  and memory outside `rt` and the stack window is unchanged.

**What is assumed.** The contract (hypothesis `hg`). `Witness` shows the hypotheses are
satisfiable together: a model of `growslice` (the heap's first block), and the call
`AppendPoint(nil, p)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
namespace Proof

def ptType : Nat :=
  adrpLdTarget (Extracted.entry + 0x38) (segWord Extracted.program "example.com/basic.AppendPoint" 14)
    (segWord Extracted.program "example.com/basic.AppendPoint" 15) 0

def Pre (rt : List (Nat × Nat)) (H : RtReady) (ptr len cap : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 4208 56 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4208) 4264 rt ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 40 ∧
    ptr.toNat + 24 * cap.toNat ≤ 2 ^ 48 ∧ Disjoint ptr.toNat (24 * cap.toNat) (s.sp.toNat - 4208) 4264 ∧
    Disjoint ptType 16 (s.sp.toNat - 4208) 4264 ∧
    (len.toNat < cap.toNat → s.mem.accessible ptr.toNat (24 * cap.toNat) true = true) ∧
    (0 < len.toNat → s.mem.accessible ptr.toNat (24 * len.toNat) false = true) ∧
    (cap.toNat ≤ len.toNat →
      H [ptr.toNat, len.toNat + 1, cap.toNat, 1, ptType] (s.regs 28).toNat (s.sp.toNat - 112)
        (rtView rt s.mem))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (ptr len cap x y z : BitVec 64)
    (hg : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice")
      rt 4096 H growsliceSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [ptr, len, cap, x, y, z]
      (Pre rt H ptr len cap)
      (fun s s' => (s'.regs 1).toNat = len.toNat + 1 ∧
        (len.toNat < cap.toNat → s'.regs 0 = ptr ∧ s'.regs 2 = cap ∧
          s'.mem.readLE (ptr.toNat + 24 * len.toNat) 8 = x.toNat ∧
          s'.mem.readLE (ptr.toNat + 24 * len.toNat + 8) 8 = y.toNat ∧
          s'.mem.readLE (ptr.toNat + 24 * len.toNat + 16) 8 = z.toNat ∧
          MemFrame s.mem s'.mem [(ptr.toNat + 24 * len.toNat, ptr.toNat + 24 * len.toNat + 24),
            (s.sp.toNat - 4208, s.sp.toNat + 56)]) ∧
        (cap.toNat ≤ len.toNat →
          (s'.regs 2).toNat = growCap 24 true (len.toNat + 1) cap.toNat ∧
          InRanges (s'.regs 0).toNat (growCap 24 true (len.toNat + 1) cap.toNat * 24) rt ∧
          s'.mem.accessible (s'.regs 0).toNat (growCap 24 true (len.toNat + 1) cap.toNat * 24) true = true ∧
          (∀ i, i < 24 * len.toNat → s'.mem.bytes ((s'.regs 0).toNat + i) = s.mem.bytes (ptr.toNat + i)) ∧
          s'.mem.readLE ((s'.regs 0).toNat + 24 * len.toNat) 8 = x.toNat ∧
          s'.mem.readLE ((s'.regs 0).toNat + 24 * len.toNat + 8) 8 = y.toNat ∧
          s'.mem.readLE ((s'.regs 0).toNat + 24 * len.toNat + 16) 8 = z.toNat ∧
          ZeroBytes s'.mem ((s'.regs 0).toNat + 24 * (len.toNat + 1))
            (growCap 24 true (len.toNat + 1) cap.toNat * 24 - 24 * (len.toNat + 1)) ∧
          MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4208, s.sp.toNat + 56)]))) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hlc, hc, hpb, hdj, hdt, hwr, hrd, hHf⟩
  janus_intro hs
  janus_eval_nat h_ut : ptType
  janus_data hd [hw]
  simp only [Disjoint] at hdj hdt
  by_cases hl : len.toNat < cap.toNat
  · have hw' := hwr hl
    janus_run
    exact ⟨fun _ => by janus_frame, fun h => absurd h (by omega)⟩
  · have hH := hHf (by omega)
    rw [h_ut] at hH
    clear hHf
    have hrd' : 0 < len.toNat * 24 → s.mem.accessible ptr.toNat (len.toNat * 24) false = true :=
      fun h => by rw [Nat.mul_comm]; exact hrd (by omega)
    janus_run [false_implies, implies_true, List.not_mem_nil, forall_const] until [Extracted.entry + 0x44] calls [hg]
    rename_i r0 r1 r2 jk fl vr M1 hfr hpost
    obtain ⟨hr1, hr2, hin, hlt, hacc, hcp, hz, -⟩ := hpost
    have hle := le_growCap 24 true (len.toNat + 1) cap.toNat (by decide)
    have hdj2 := InRanges.disjoint hin hout
    have hacc2 : M1.accessible (r0.toNat + 24 * len.toNat) 24 true = true :=
      Memory.accessible_mono _ hacc (by omega) (by omega)
    have hx : (8 * r1.toNat + 2 * (8 * r1.toNat) - 24) = 24 * len.toNat := by omega
    have hb0 : r0.toNat + 24 * len.toNat + 24 ≤ 2 ^ 48 := by omega
    janus_run until [Extracted.entry + 0x5c]
    have hx6 : (BitVec.rotateRight r1 61 &&& 18446744073709551608#64 &&& 18446744073709551615#64) +
        (BitVec.rotateRight r1 61 &&& 18446744073709551608#64 &&& 18446744073709551615#64) <<< 1 - 24#64 =
        BitVec.ofNat 64 (24 * len.toNat) := by
      have e3 : r1.rotateRight 61 &&& 18446744073709551608#64 = r1 <<< 3 :=
        Iface.rotateRight_and_eq_shiftLeft r1 3 (by decide)
      have e4 : ∀ v : BitVec 64, v &&& 18446744073709551615#64 = v := fun v => by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_and, show (18446744073709551615#64).toNat = 2 ^ 64 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]
        omega
      rw [e3, e4]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        BitVec.toNat_ofNat]
      omega
    rw [hx6]
    have hacc0 : s.mem.accessible (r0.toNat + 24 * len.toNat) 24 true = true := by
      have := hfr.accessible (r0.toNat + 24 * len.toNat) 24 true
      simp only [Memory.accessible_writeLE] at this
      rw [← this]; exact hacc2
    janus_run
    refine ⟨hr1, fun h => absurd h hl, fun _ => ⟨hr2, by rw [← hr2]; exact hin, ?_, ?_, ?_, by janus_frame⟩⟩
    · have := hfr.accessible r0.toNat (r2.toNat * 24) true
      simp only [Memory.accessible_writeLE] at this
      rw [← hr2, ← this]; exact hacc
    · intro i hi
      rw [Memory.bytes_writeLE_outside _ (by omega), Memory.bytes_writeLE_outside _ (by omega),
        Memory.bytes_writeLE_outside _ (by omega), hcp i (by omega)]
      repeat rw [Memory.bytes_writeLE_outside _ (by omega)]
    · intro i hi
      rw [Memory.bytes_writeLE_outside _ (by omega), Memory.bytes_writeLE_outside _ (by omega),
        Memory.bytes_writeLE_outside _ (by omega)]
      have := hz i (by omega)
      rwa [Nat.mul_comm (len.toNat + 1) 24] at this

/-! ## Non-vacuity

Code at `runtime.growslice`'s address that meets the contract (`Sat.constCode HEAP 1 1`: the
heap's first block, length and capacity 1) for the readiness `HA` (the call `growslice(nil, 1, 0,
1, Point)` with `Point`'s descriptor and 24 writable heap bytes in the runtime's view), the
runtime-owned ranges `rtA` (`Sat.rtW` and the descriptor), and the call `AppendPoint(nil, p)`
from `Sat`'s witness memory with the binary's read-only data (`wmemD`). -/

namespace Witness

open Janus.Contracts.Sat

def PT : Nat := ((Extracted.program.data[0]?).map (·.base)).getD 0
theorem ptType_eq : ptType = PT := by decide

def rtA : List (Nat × Nat) := rtW ++ [(PT, PT + 256)]

def PA (v : Memory) : Prop := v.readLE PT 8 = 24 ∧ v.readLE (PT + 8) 8 = 0 ∧ v.accessible HEAP 24 true = true
def HA : RtReady := HL [0, 1, 0, 1, PT] PA

def cAddr : Nat := Extracted.program.contractAddr "runtime.growslice"
def implAt : List Segment := [{ name := "model", base := cAddr, words := constCode HEAP 1 1 }]
def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem pt_in : InRanges PT 16 rtA := ⟨(PT, PT + 256), by simp [rtA], Nat.le_refl _, by decide⟩
theorem heap_in : InRanges HEAP 24 rtA := ⟨(HEAP, HEAP + 0x10000), by simp [rtA, rtW], Nat.le_refl _, by decide⟩

theorem model : RtContract (Extracted.program.link implAt) cAddr rtA 4096 HA growsliceSpec := by
  rw [linked_eq]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, -, -, -, hH⟩
  obtain ⟨ha, h1, h2, h3⟩ := ready_of rfl hH
  janus_run
  apply rtPost_const <;> (try rfl) <;> (try simp [setReg])
  rw [readLE_rtView (pt_in.sub (Nat.le_refl _) (by decide))] at h1
  rw [readLE_rtView (pt_in.sub (by decide) (by decide))] at h2
  rw [rtView_accessible] at h3
  have ha5 : argWords s 5 = [0, 1, 0, 1, PT] := ha
  rw [ha5]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, h1, h2]
  exact ⟨trivial, by decide, heap_in, by decide, h3, fun i h => absurd h (by omega),
    fun i h => absurd h (by omega), fun h => by simp at h⟩

def ret : Nat := wret
set_option maxRecDepth 100000 in
theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- `Sat.wmem` with the binary's read-only data at its address. -/
def wmemD : Memory :=
  ⟨fun a => if PT ≤ a ∧ a < PT + 256 then
      BitVec.ofNat 8 (((Extracted.data.head?.map (·.bytes)).getD []).getD (a - PT) 0) else wmem.bytes a,
    wmem.regions ++ [⟨PT, 256, false⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmemD }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [0, 0, 0, 0, 0, 0] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded wmemD := by
  unfold Program.DataLoaded
  decide

theorem pre : Pre rtA HA 0 0 0 s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, ?_⟩, dataLoaded,
    by simp only [rtA, rtW, List.cons_append, List.nil_append, outside_cons, outside_nil]; decide,
    by decide, by decide, by decide, by simp [Disjoint], by rw [ptType_eq]; unfold Disjoint; decide,
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ?_⟩
  · have hw : wmemD.accessible (wsp - 0x2000) 0x2100 true = true := by decide
    exact Memory.accessible_mono _ hw (by decide) (by decide)
  · rw [ptType_eq]; exact ⟨rfl, by decide, by decide, by decide⟩

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State),
    RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice")
      rt 4096 H growsliceSpec ∧ RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [0, 0, 0, 0, 0, 0] s ∧
    Pre rt H 0 0 0 s :=
  ⟨implAt, rtA, HA, ret, s0, model, hret, setup, pre⟩

/-- The witness call returns: the result has length 1 (the full theorem's conclusion holds;
this states its first part). -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 1).toNat = 1 :=
  (correctness implAt rtA HA 0 0 0 0 0 0 model ret hret s0 setup pre).mono fun _ h => ⟨h.1, by simpa using h.2.1⟩

end Witness

end Proof
