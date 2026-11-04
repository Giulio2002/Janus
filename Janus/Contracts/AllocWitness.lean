import Janus.Contracts.AllocAmd64
import Janus.Contracts.AllocSat
import Janus.Contracts.AllocSatAmd64

/-!
# Non-vacuity witnesses for allocation-contract theorems (`janus_alloc_witness`)

A theorem about a function that calls `runtime.newobject` takes the allocation contract as a
hypothesis `hnew : NewobjectContract (P.link impl) addr rt 4096 H` and quantifies over `impl`, `rt`
and the readiness predicate `H`. To show that the hypotheses are not vacuous (round 9 C1, round 10
V1) one builds ONE concrete allocator and proves the contract for it:

* `impl`: two instructions at `runtime.newobject`'s address that return the 64 KiB heap at `0x10000`
  whatever is asked (arm64 `MOVZ X0, #1, LSL #16; RET`, amd64 `MOV EAX, 0x10000; RET`);
* `rt`: the heap and the 16-byte type descriptors the function passes;
* `H`: the argument is a type descriptor inside `rt` of at most 32 KiB, the heap is writable and zero
  (as the runtime sees it, `rtView`);
* `hnew`: the contract for these, proved by `janus_run` / `janus64_run` on the linked program.

`janus_alloc_witness types := [t₁, …]` (arm64) and `janus64_alloc_witness types := [t₁, …]`
(amd64), used in `namespace Witness`, define all of that in a namespace `AllocW` of the
caller: `AllocW.tys` (the numeric addresses of the type descriptors, `janus_eval%` of the given
terms, e.g. `Proof.pairType`), `AllocW.cA`, `impl`, `rt`, `H`, `linked` (the linked program as a closed
constant), `addr` and `hnew`. The caller then only writes the function-specific concrete call state
(`s0`, its `pre`) and ends with `example := correctness AllocW.impl AllocW.rt AllocW.H … AllocW.hnew …`.
The helper lemmas below (`heapZero_of_bytes`, `allocH_intro`) prove the heap part of `H` for a
state whose bytes are zero on the heap. Examples: `examples/proofs/NewPair.lean`,
`examples/proofs-amd64/NewPair/Proof.lean`; the pattern's source is
`audit/round9/controls/NewPair_witness.lean`.
-/

namespace Janus.Contracts.AllocWitness

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- The toy heap. -/
def heap : Nat := 0x10000

/-- The runtime-owned ranges: the heap and 16-byte type descriptors at `tys`. -/
def allocRt (tys : List Nat) : List (Nat × Nat) :=
  (heap, heap + 0x10000) :: tys.map fun a => (a, a + 16)

theorem heap_mem (tys : List Nat) : (heap, heap + 0x10000) ∈ allocRt tys := List.mem_cons_self

theorem ty_mem {tys : List Nat} {a : Nat} (h : a ∈ tys) : (a, a + 16) ∈ allocRt tys :=
  List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, h, rfl⟩)

theorem inRanges_ty {tys : List Nat} {a : Nat} (h : a ∈ tys) : InRanges a 16 (allocRt tys) :=
  ⟨(a, a + 16), ty_mem h, Nat.le_refl _, Nat.le_refl _⟩

/-- arm64 readiness: the argument is a type descriptor in `rt` of at most 32 KiB; the heap is
writable and zero. -/
def allocH (rt : List (Nat × Nat)) : RtReady := fun args _ _ v =>
  ∃ typ, args = [typ] ∧ InRanges typ 16 rt ∧ typSize v typ ≤ 32768 ∧
    v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000

/-- amd64 readiness (the same facts, in the order the amd64 contract proofs use). -/
def allocH64 (rt : List (Nat × Nat)) : RtReady := fun args _ _ v =>
  (v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000) ∧
    ∃ typ, args = [typ] ∧ InRanges typ 16 rt ∧ typSize v typ ≤ 32768

/-- `MOVZ X0, #1, LSL #16; RET`. -/
def heapCode : List Nat := [0xd2a00020, 0xd65f03c0]
/-- `MOV EAX, 0x10000; RET`. -/
def heapCode64 : List Nat := [0xb8, 0x00, 0x00, 0x01, 0x00, 0xc3]

theorem callRegs_eq (r : Nat → W64) :
    callRegs r r [BitVec.ofNat 64 heap] = setReg r 0 (BitVec.ofNat 64 heap) := by
  funext i
  simp only [callRegs, setReg]
  rcases i with _ | i
  · rfl
  · simp only [List.getD_cons_succ, List.getD_nil]
    split <;> rfl

/-- The heap is zero as the runtime sees it when the memory's bytes are zero on the heap. -/
theorem heapZero_of_bytes (rt : List (Nat × Nat)) (m : Memory) (h : ∀ i, i < 0x10000 → m.bytes (heap + i) = 0) :
    ZeroBytes (rtView rt m) heap 0x10000 := by
  intro i hi
  show (if _ then m.bytes (heap + i) else 0) = 0
  split
  · exact h i hi
  · rfl

/-- `allocH` for a call whose single argument is the type descriptor `ty`. -/
theorem allocH_intro {rt : List (Nat × Nat)} {ty : Nat} {v : Memory} {g sp : Nat}
    (hin : InRanges ty 16 rt) (hsz : typSize v ty ≤ 32768)
    (hacc : v.accessible heap 0x10000 true = true) (hz : ZeroBytes v heap 0x10000) :
    allocH rt [ty] g sp v := ⟨ty, rfl, hin, hsz, hacc, hz⟩

theorem allocH64_intro {rt : List (Nat × Nat)} {ty : Nat} {v : Memory} {g sp : Nat}
    (hin : InRanges ty 16 rt) (hsz : typSize v ty ≤ 32768)
    (hacc : v.accessible heap 0x10000 true = true) (hz : ZeroBytes v heap 0x10000) :
    allocH64 rt [ty] g sp v := ⟨⟨hacc, hz⟩, ty, rfl, hin, hsz⟩

/-- The heap, as the runtime sees it, is writable and zero. -/
def HeapReady (v : Memory) : Prop := v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000

/-- `makeslice` readiness (arm64 and amd64): the element type is a descriptor in `rt`, the request fits. -/
def makeH (rt : List (Nat × Nat)) : RtReady := fun args _ _ v =>
  HeapReady v ∧ ∃ et l c, args = [et, l, c] ∧ InRanges et 16 rt ∧ typSize v et * c ≤ 32768

/-- `growslice` readiness: exactly `append(p[:0:0], x)` of a `[]uint64`: `newLen = 1`, `oldCap = 0`, `num = 1`. -/
def growH : RtReady := fun args _ _ v => HeapReady v ∧ ∃ p et, args = [p, 1, 0, 1, et]

theorem makeH_intro {rt : List (Nat × Nat)} {et l c : Nat} {v : Memory} {g sp : Nat}
    (hin : InRanges et 16 rt) (hsz : typSize v et * c ≤ 32768) (hr : HeapReady v) :
    makeH rt [et, l, c] g sp v := ⟨hr, et, l, c, rfl, hin, hsz⟩

/-- The heap object is `Fresh` for a request that fits. -/
theorem fresh_heap' {tys : List Nat} {m : Memory} {size round : Nat} (zero hdr : Bool)
    (hr : HeapReady (rtView (allocRt tys) m)) (hsz : size ≤ round) (hround : round ≤ 32768) :
    Fresh (allocRt tys) m heap size round zero hdr := by
  obtain ⟨hacc, hz⟩ := hr
  rw [rtView_accessible] at hacc
  have hz' := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000), heap_mem _, Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨⟨(heap, heap + 0x10000), heap_mem _, Nat.le_refl _, by simp only [heap]; omega⟩,
    by simp only [heap]; omega, Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    fun _ => by decide, fun _ _ => by decide, fun _ => fun i hi => hz' i (by omega), hsz⟩

theorem callRegs_grow' (r : Nat → W64) (b : W64) :
    callRegs r r [BitVec.ofNat 64 heap, r 1, b] = setReg (setReg r 0 (BitVec.ofNat 64 heap)) 2 b :=
  AllocSat.callRegs_grow r b

/-- `MOVZ X0, #1, LSL #16; MOVZ X2, #1; RET`. -/
def growCodeA : List Nat := [0xd2a00020, 0xd2800022, 0xd65f03c0]
/-- `MOV EAX, 0x10000; MOV ECX, 1; RET`. -/
def growCode64 : List Nat := [0xb8, 0x00, 0x00, 0x01, 0x00, 0xb9, 0x01, 0x00, 0x00, 0x00, 0xc3]

end Janus.Contracts.AllocWitness

open Lean in
set_option hygiene false in
/-- arm64: the concrete allocator, `rt`, `H` and `hnew` for the allocation contract of a program
`Extracted.program` (see the module doc). `types := [t₁, …]` are terms for the addresses of the
16-byte type descriptors the function passes to `newobject`. -/
macro "janus_alloc_witness " "types" " := " "[" tys:term,* "]" : command =>
  `(namespace AllocW
    open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
    open Janus.Contracts.AllocWitness (heap allocRt allocH heapCode)

    def tys : List Nat := [$[(janus_eval% $tys)],*]
    def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
    def impl : List Segment := [{ name := "witness.newobject", base := cA, words := heapCode }]
    def rt : List (Nat × Nat) := allocRt tys
    def H : RtReady := allocH rt
    /-- The linked program, as one closed constant (the executor evaluates its facts directly). -/
    def linked : Program := Extracted.program.link impl

    theorem addr : Extracted.program.contractAddr "runtime.newobject" = cA := by decide

    theorem hnew : NewobjectContract (Extracted.program.link impl)
        (Extracted.program.contractAddr "runtime.newobject") rt 4096 H := by
      rw [addr]
      intro s hpc hpre
      obtain ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, typ, hargs, hin, hsz, hacc, hz⟩ := hpre
      simp only [List.cons.injEq, and_true] at hargs
      subst hargs
      change ReachesRet linked _ s _
      janus_run
      refine ⟨BitVec.ofNat 64 heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_,
        ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun hpos => ?_⟩
      · simp only [retStateX]; rw [Janus.Contracts.AllocWitness.callRegs_eq]; rfl
      · unfold typSize at hsz
        rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
        change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
        have hb := blockSize_le_maxSmallSize (typSize s.mem (s.regs 0).toNat)
          (typNoscan s.mem (s.regs 0).toNat) hsz
        have hle : typSize s.mem (s.regs 0).toNat ≤
            blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat) :=
          Janus.Contracts.AllocSat.le_blockSize _ _
        simp only [maxSmallSize] at hb
        have hheap : (BitVec.ofNat 64 heap).toNat = heap := by decide
        rw [hheap]
        refine ⟨⟨(heap, heap + 0x10000), Janus.Contracts.AllocWitness.heap_mem _, Nat.le_refl _,
            by simp only [heap]; omega⟩,
          by simp only [heap]; omega, ?_, fun _ => by decide, fun _ _ => by decide, fun _ => ?_, hle⟩
        · rw [rtView_accessible] at hacc
          exact Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
        · have := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000),
            Janus.Contracts.AllocWitness.heap_mem _, Nat.le_refl _, Nat.le_refl _⟩
          exact fun i hi => this i (by omega)
    end AllocW)

open Lean in
set_option hygiene false in
/-- amd64 twin of `janus_alloc_witness`. -/
macro "janus64_alloc_witness " "types" " := " "[" tys:term,* "]" : command =>
  `(namespace AllocW
    open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Tactic Janus.Spec Janus.Contracts
    open Janus (InRanges Outside outside_cons outside_nil MemFrame)
    open Janus.Contracts.AllocWitness (heap allocRt allocH64 heapCode64)
    open Janus.Contracts.AllocSatAmd64 (ret_of)
    open Janus.Contracts.AllocSat (le_blockSize)

    def tys : List Nat := [$[(janus_eval% $tys)],*]
    def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
    def impl : List Janus.Amd64.Segment := [{ name := "witness.newobject", base := cA, bytes := heapCode64 }]
    def rt : List (Nat × Nat) := allocRt tys
    def H : RtReady := allocH64 rt
    /-- The linked program, as one closed constant. -/
    def linked : Janus.Amd64.Program := Extracted.program.link impl

    theorem addr : Extracted.program.contractAddr "runtime.newobject" = cA := by decide

    theorem hnew : NewobjectContract64 (Extracted.program.link impl)
        (Extracted.program.contractAddr "runtime.newobject") rt 4096 H := by
      rw [addr]
      intro s hpc hpre
      obtain ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, typ, hargs, hin, hsz⟩ := hpre
      simp only [List.cons.injEq, and_true] at hargs
      subst hargs
      change ReachesRet linked _ s _
      janus64_run
      refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, _, _, ret_of s _ [BitVec.ofNat 64 heap]
        (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
        (by simp [setRegF, heap]) (by simp) (by simp) rfl rfl rfl rfl rfl,
        ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
      unfold typSize at hsz
      rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
      change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
      have hb := blockSize_le_maxSmallSize (typSize s.mem (s.regs 0).toNat)
        (typNoscan s.mem (s.regs 0).toNat) hsz
      simp only [maxSmallSize] at hb
      have hle := le_blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat)
      have hheap : (BitVec.ofNat 64 heap).toNat = heap := by decide
      rw [hheap]
      obtain ⟨hacc, hz⟩ := hr
      rw [rtView_accessible] at hacc
      have hz' := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000),
        Janus.Contracts.AllocWitness.heap_mem _, Nat.le_refl _, Nat.le_refl _⟩
      refine ⟨⟨(heap, heap + 0x10000), Janus.Contracts.AllocWitness.heap_mem _, Nat.le_refl _,
          by simp only [heap]; omega⟩,
        by simp only [heap]; omega, Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
        fun _ => by decide, fun _ _ => by decide, fun _ => fun i hi => hz' i (by omega), hle⟩
    end AllocW)

open Lean in
set_option hygiene false in
/-- arm64: the concrete `runtime.makeslice` (returns the heap), `rt`, `H` and `hmk` for a program
`Extracted.program` (see the module doc); in namespace `MakeW`. -/
macro "janus_makeslice_witness " "types" " := " "[" tys:term,* "]" : command =>
  `(namespace MakeW
    open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
    open Janus.Contracts.AllocWitness (heap allocRt heapCode makeH)

    def tys : List Nat := [$[(janus_eval% $tys)],*]
    def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.makeslice")
    def impl : List Segment := [{ name := "witness.makeslice", base := cA, words := heapCode }]
    def rt : List (Nat × Nat) := allocRt tys
    def H : RtReady := makeH rt
    def linked : Program := Extracted.program.link impl

    theorem addr : Extracted.program.contractAddr "runtime.makeslice" = cA := by decide

    theorem hmk : MakesliceContract (Extracted.program.link impl)
        (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H := by
      rw [addr]
      intro s hpc hpre
      obtain ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, hr, et, l, c, hargs, hin, hsz⟩ := hpre
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -, rfl⟩ := hargs
      change ReachesRet linked _ s _
      janus_run
      refine ⟨BitVec.ofNat 64 heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_,
        ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
      · simp only [retStateX]; rw [Janus.Contracts.AllocWitness.callRegs_eq]; rfl
      · unfold typSize at hsz
        rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
        change typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat ≤ 32768 at hsz
        rw [show (BitVec.ofNat 64 heap).toNat = heap from by decide]
        exact Janus.Contracts.AllocWitness.fresh_heap' _ _ hr (Janus.Contracts.AllocSat.le_blockSize _ _)
          (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))
    end MakeW)

open Lean in
set_option hygiene false in
/-- arm64: the concrete `runtime.growslice` (for `append` to an empty `[]uint64`), `rt`, `H` and
`hgrow` for a program `Extracted.program`; in namespace `GrowW`. -/
macro "janus_growslice_witness " : command =>
  `(namespace GrowW
    open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
    open Janus.Contracts.AllocWitness (heap allocRt growCodeA growH)

    def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.growslice")
    def impl : List Segment := [{ name := "witness.growslice", base := cA, words := growCodeA }]
    def rt : List (Nat × Nat) := allocRt []
    def H : RtReady := growH
    def linked : Program := Extracted.program.link impl

    theorem addr : Extracted.program.contractAddr "runtime.growslice" = cA := by decide

    theorem hgrow : GrowsliceContract (Extracted.program.link impl)
        (Extracted.program.contractAddr "runtime.growslice") rt 4096 H := by
      rw [addr]
      intro s hpc hpre
      obtain ⟨⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _, _, _, _, _, _⟩, _⟩, hr, p, et, hargs⟩ := hpre
      simp only [growsliceArgs, List.cons.injEq, and_true] at hargs
      obtain ⟨-, h1, h2, h3, -⟩ := hargs
      change ReachesRet linked _ s _
      janus_run
      refine ⟨BitVec.ofNat 64 heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_,
        ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
      · simp only [retStateX]
        rw [h1, h2, Janus.Contracts.AllocSat.growCap8_1_0, Janus.Contracts.AllocWitness.callRegs_grow']; rfl
      · simp only [growsliceObj, h1, h2, h3, Janus.Contracts.AllocSat.growCap8_1_0,
          show (BitVec.ofNat 64 heap).toNat = heap from by decide]
        exact ⟨Janus.Contracts.AllocWitness.fresh_heap' (tys := []) _ _ hr (Nat.le_refl _) (by decide),
          fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩
    end GrowW)

open Lean in
set_option hygiene false in
/-- amd64 twin of `janus_makeslice_witness`. -/
macro "janus64_makeslice_witness " "types" " := " "[" tys:term,* "]" : command =>
  `(namespace MakeW
    open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Tactic Janus.Spec Janus.Contracts
    open Janus (InRanges Outside outside_cons outside_nil MemFrame)
    open Janus.Contracts.AllocWitness (heap allocRt heapCode64 makeH)
    open Janus.Contracts.AllocSatAmd64 (ret_of)

    def tys : List Nat := [$[(janus_eval% $tys)],*]
    def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.makeslice")
    def impl : List Janus.Amd64.Segment := [{ name := "witness.makeslice", base := cA, bytes := heapCode64 }]
    def rt : List (Nat × Nat) := allocRt tys
    def H : RtReady := makeH rt
    def linked : Janus.Amd64.Program := Extracted.program.link impl

    theorem addr : Extracted.program.contractAddr "runtime.makeslice" = cA := by decide

    theorem hmk : MakesliceContract64 (Extracted.program.link impl)
        (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H := by
      rw [addr]
      intro s hpc hpre
      obtain ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, et, l, c, hargs, hin, hsz⟩ := hpre
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -, rfl⟩ := hargs
      change ReachesRet linked _ s _
      janus64_run
      refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, _, _, ret_of s _ [BitVec.ofNat 64 heap]
        (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
        (by simp [setRegF, heap]) (by simp) (by simp) rfl rfl rfl rfl rfl,
        ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
      unfold typSize at hsz
      rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
      change typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat ≤ 32768 at hsz
      rw [show (BitVec.ofNat 64 heap).toNat = heap from by decide]
      exact Janus.Contracts.AllocWitness.fresh_heap' _ _ hr (Janus.Contracts.AllocSat.le_blockSize _ _)
        (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))
    end MakeW)

open Lean in
set_option hygiene false in
/-- amd64 twin of `janus_growslice_witness`. -/
macro "janus64_growslice_witness " : command =>
  `(namespace GrowW
    open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Tactic Janus.Spec Janus.Contracts
    open Janus (InRanges Outside outside_cons outside_nil MemFrame)
    open Janus.Contracts.AllocWitness (heap allocRt growCode64 growH)
    open Janus.Contracts.AllocSatAmd64 (ret_of)

    def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.growslice")
    def impl : List Janus.Amd64.Segment := [{ name := "witness.growslice", base := cA, bytes := growCode64 }]
    def rt : List (Nat × Nat) := allocRt []
    def H : RtReady := growH
    def linked : Janus.Amd64.Program := Extracted.program.link impl

    theorem addr : Extracted.program.contractAddr "runtime.growslice" = cA := by decide

    theorem hgrow : GrowsliceContract64 (Extracted.program.link impl)
        (Extracted.program.contractAddr "runtime.growslice") rt 4096 H := by
      rw [addr]
      intro s hpc hpre
      obtain ⟨⟨⟨⟨hra, hal, _, _, _⟩, _, _, _, _, _, _, _⟩, _⟩, hr, p, et, hargs⟩ := hpre
      simp only [growsliceArgs64, List.cons.injEq, and_true] at hargs
      obtain ⟨-, h1, h2, h3, -⟩ := hargs
      change ReachesRet linked _ s _
      janus64_run
      refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, _, _, ret_of s _ _
        (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
        (by simp [setRegF, heap]) (by simp [setRegF])
        (by simp [setRegF, h1, h2, Janus.Contracts.AllocSat.growCap8_1_0]) rfl rfl rfl rfl rfl,
        ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
      simp only [growsliceObj64, h1, h2, h3, Janus.Contracts.AllocSat.growCap8_1_0,
        show (BitVec.ofNat 64 heap).toNat = heap from by decide]
      exact ⟨Janus.Contracts.AllocWitness.fresh_heap' (tys := []) (size := 8) (round := 8) _ _ hr
          (Nat.le_refl _) (by decide),
        fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩
    end GrowW)
