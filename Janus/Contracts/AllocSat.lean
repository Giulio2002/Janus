import Janus.Contracts.Alloc

/-!
# The allocation contracts are satisfiable (arm64, round 9 C1)

Before round 9 the allocation contracts were false for every implementation
(`audit/round9/model/Unsat.lean`): their precondition said nothing about the runtime's own state.
With the readiness predicate `H : RtReady` they are not. For every contract of
`Janus.Contracts` (`Alloc.lean`) this file gives machine code placed at `A0` of a program with no
other code, a runtime-owned list `rt`, a readiness predicate `H`, a proof by symbolic execution
that the code meets the contract, and a call state (`wstate`) that satisfies the contract's
whole precondition, `H` included, for a non-zero size. `<contract>_satisfiable` states that they
exist (`audit/round9/run-round9.sh`, row SAT, requires one for every contract).

The code is a toy, not the Go runtime: it returns the 64 KiB heap `heap` whatever is asked, and
`H` says the heap is writable and zero and the request fits.
-/

namespace Janus.Contracts.AllocSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- A program with no code, stubs or data of its own. -/
def toy : Program := { segments := [], stubs := [], exitAddr := 0 }
/-- Where the implementations are placed. -/
def A0 : Nat := 0x100000
/-- An implementation: the words `ws` at `A0`. -/
def at0 (ws : List Nat) : List Segment := [{ name := "model", base := A0, words := ws }]
/-- `toy` with the implementation, as a closed program (the executor runs its own segments). -/
def withCode (ws : List Nat) : Program := { segments := at0 ws, stubs := [], exitAddr := 0 }
theorem link_at0 (ws : List Nat) : toy.link (at0 ws) = withCode ws := rfl

def heap : Nat := 0x10000
def tyA : Nat := 0x30000
def wsp : Nat := 0x200000
def wg : Nat := 0x300000
def wret : Nat := 0x1000
/-- The runtime-owned memory: the heap and the type descriptor. -/
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16)]

/-- A type descriptor of 16 bytes (`Size_ = 16`) without pointers (`PtrBytes = 0`) at `tyA`. -/
def wmem : Memory :=
  ⟨fun a => if a = tyA then 16 else 0,
   [⟨wsp - 4096, 4096 + 64, true⟩, ⟨wg, 0x100, false⟩, ⟨tyA, 16, false⟩, ⟨heap, 0x10000, true⟩]⟩

/-- The witness call state with argument registers `r`. -/
def wstate (r : Nat → W64) : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret else r i,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
    mem := wmem }

/-- The heap, as the runtime sees it, is writable and zero. -/
def HeapReady (v : Memory) : Prop := v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000

theorem heapReady_w : HeapReady (rtView rt wmem) := by
  refine ⟨by decide, fun i hi => ?_⟩
  show (if _ then wmem.bytes (heap + i) else 0) = 0
  split
  · show (if heap + i = tyA then (16 : Byte) else 0) = 0
    rw [if_neg (by simp only [heap, tyA]; omega)]
  · rfl

theorem callOK_w (r : Nat → W64) (n : Nat) (hn : n ≤ 5) : CallOK (wstate r) 4096 n := by
  have hw : wmem.accessible (wsp - 4096) (4096 + 8 + 8 * 5) true = true := by decide
  have h30 : (wstate r).regs 30 = BitVec.ofNat 64 wret := rfl
  have hsp : (wstate r).sp = BitVec.ofNat 64 wsp := rfl
  have hm : (wstate r).mem = wmem := rfl
  simp only [CallOK, h30, hsp, hm]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by simp [wsp]; omega, ?_⟩
  rw [show (BitVec.ofNat 64 wsp).toNat = wsp from rfl]
  exact Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)

theorem typeOK_w : TypeOK wmem tyA := ⟨by decide, by decide⟩
theorem typSize_w : typSize wmem tyA = 16 := by decide
theorem typPtr_w : typPtrBytes wmem tyA = 0 := by decide

/-- The object every implementation returns is `Fresh` for a request of at most 32 KiB. -/
theorem fresh_heap {m : Memory} {size round : Nat} (zero hdr : Bool)
    (hr : HeapReady (rtView rt m)) (hsz : size ≤ round) (hround : round ≤ 32768) :
    Fresh rt m heap size round zero hdr := by
  obtain ⟨hacc, hz⟩ := hr
  rw [rtView_accessible] at hacc
  have hz' := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, by simp only [heap]; omega⟩,
    by simp only [heap]; omega, Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    fun _ => by decide, fun _ _ => by decide, fun _ => fun i hi => hz' i (by omega), hsz⟩

theorem le_blockSize (size : Nat) (b : Bool) : size ≤ blockSize size b := by
  unfold blockSize; split
  · exact Nat.le_refl _
  · exact le_roundupsize _ _

theorem callRegs_heap (r : Nat → W64) :
    callRegs r r [BitVec.ofNat 64 heap] = setReg r 0 (BitVec.ofNat 64 heap) := by
  funext i
  rcases i with _ | i
  · rfl
  · simp only [callRegs, setReg, List.getD_cons_succ, List.getD_nil]
    split <;> (try split) <;> first | rfl | (exfalso; omega)

theorem callRegs_grow (r : Nat → W64) (b : W64) :
    callRegs r r [BitVec.ofNat 64 heap, r 1, b] = setReg (setReg r 0 (BitVec.ofNat 64 heap)) 2 b := by
  funext i
  rcases i with _ | _ | _ | i
  · rfl
  · rfl
  · rfl
  · simp only [callRegs, setReg, List.getD_cons_succ, List.getD_nil]
    split <;> (try split) <;> (try split) <;> first | rfl | (exfalso; omega)

/-! ## `newobject` -/

/-- `MOVZ X0, #1, LSL #16` (`X0 = heap`); `RET`. -/
def heapCode : List Nat := [0xd2a00020, 0xd65f03c0]

def Hnew : RtReady := fun args _ _ v =>
  HeapReady v ∧ ∃ typ, args = [typ] ∧ InRanges typ 16 rt ∧ typSize v typ ≤ 32768

theorem newobject_impl : NewobjectContract (toy.link (at0 heapCode)) A0 rt 4096 Hnew := by
  rw [link_at0]
  intro s hpc ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, hr, typ, hargs, hin, hsz⟩
  simp only [List.cons.injEq, and_true] at hargs
  subst hargs
  janus_run
  refine ⟨BitVec.ofNat 64 heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
  · simp only [retStateX]; rw [callRegs_heap]; rfl
  · unfold typSize at hsz
    rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
    change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
    rw [show (BitVec.ofNat 64 heap).toNat = heap from rfl]
    exact fresh_heap _ _ hr (le_blockSize _ _)
      (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))

theorem newobject_satisfiable : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady),
    NewobjectContract (toy.link impl) A0 rt 4096 H ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (NewobjectPre 4096 s ∧ Ready H rt [(s.regs 0).toNat] s) ∧ 0 < typSize s.mem (s.regs 0).toNat :=
  ⟨_, _, _, newobject_impl, wstate (fun i => if i = 0 then BitVec.ofNat 64 tyA else 0), rfl,
    ⟨⟨callOK_w _ 1 (by omega), typeOK_w, by rw [show ((wstate _).regs 0).toNat = tyA from rfl]; decide⟩,
     heapReady_w, tyA, rfl, ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩, by decide⟩,
    by rw [show ((wstate _).regs 0).toNat = tyA from rfl]; decide⟩

/-! ## `mallocgc` -/

def Hmalloc : RtReady := fun args _ _ v =>
  HeapReady v ∧ ∃ sz typ nz, args = [sz, typ, nz] ∧ sz ≤ 32768

theorem mallocgc_impl : MallocgcContract (toy.link (at0 heapCode)) A0 rt 4096 Hmalloc := by
  rw [link_at0]
  intro s hpc ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, hr, sz, typ, nz, hargs, hsz⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, -, -⟩ := hargs
  janus_run
  refine ⟨BitVec.ofNat 64 heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
  · simp only [retStateX]; rw [callRegs_heap]; rfl
  · rw [show (BitVec.ofNat 64 heap).toNat = heap from rfl]
    exact fresh_heap _ _ hr (le_blockSize _ _)
      (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))

theorem mallocgc_satisfiable : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady),
    MallocgcContract (toy.link impl) A0 rt 4096 H ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (MallocgcPre 4096 s ∧ Ready H rt [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s) ∧
      0 < (s.regs 0).toNat :=
  ⟨_, _, _, mallocgc_impl, wstate (fun i => if i = 0 then 64 else if i = 2 then 1 else 0), rfl,
    ⟨⟨callOK_w _ 3 (by omega), by decide, Or.inl rfl⟩, heapReady_w, 64, 0, 1, rfl, by decide⟩,
    by decide⟩

/-! ## `makeslice` -/

def Hmake : RtReady := fun args _ _ v =>
  HeapReady v ∧ ∃ et l c, args = [et, l, c] ∧ InRanges et 16 rt ∧ typSize v et * c ≤ 32768

theorem makeslice_impl : MakesliceContract (toy.link (at0 heapCode)) A0 rt 4096 Hmake := by
  rw [link_at0]
  intro s hpc ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, hr, et, l, c, hargs, hin, hsz⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, -, rfl⟩ := hargs
  janus_run
  refine ⟨BitVec.ofNat 64 heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
  · simp only [retStateX]; rw [callRegs_heap]; rfl
  · unfold typSize at hsz
    rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
    change typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat ≤ 32768 at hsz
    rw [show (BitVec.ofNat 64 heap).toNat = heap from rfl]
    exact fresh_heap _ _ hr (le_blockSize _ _)
      (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))

theorem makeslice_satisfiable : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady),
    MakesliceContract (toy.link impl) A0 rt 4096 H ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (MakeslicePre 4096 s ∧ Ready H rt [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s) ∧
      0 < typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat :=
  ⟨_, _, _, makeslice_impl,
    wstate (fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 1 then 2 else if i = 2 then 4 else 0), rfl,
    ⟨⟨callOK_w _ 3 (by omega), typeOK_w, by decide, by decide,
        by rw [show ((wstate _).regs 0).toNat = tyA from rfl]; decide⟩,
     heapReady_w, tyA, 2, 4, rfl, ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩,
     by decide⟩,
    by rw [show ((wstate _).regs 0).toNat = tyA from rfl]; decide⟩

/-! ## `growslice` -/

/-- A type descriptor of 8 bytes without pointers (`uint64`) at `tyA`, for `growslice`. -/
def wmem8 : Memory := { wmem with bytes := fun a => if a = tyA then 8 else 0 }

def wstate8 (r : Nat → W64) : State := { wstate r with mem := wmem8 }

/-- `MOVZ X0, #1, LSL #16` (`X0 = heap`); `MOVZ X2, #1` (the new capacity `growCap8 1 0`); `RET`. -/
def growCode : List Nat := [0xd2a00020, 0xd2800022, 0xd65f03c0]

/-- Ready for exactly `append(nil, x)` of a `[]uint64`: `newLen = 1`, `oldCap = 0`, `num = 1`. -/
def Hgrow : RtReady := fun args _ _ v =>
  HeapReady v ∧ ∃ p et, args = [p, 1, 0, 1, et]

theorem growCap8_1_0 : growCap8 1 0 = 1 := by decide

theorem growslice_impl : GrowsliceContract (toy.link (at0 growCode)) A0 rt 4096 Hgrow := by
  rw [link_at0]
  intro s hpc ⟨⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _, _, _, _, _, _⟩, _⟩, hr, p, et, hargs⟩
  simp only [growsliceArgs, List.cons.injEq, and_true] at hargs
  obtain ⟨-, h1, h2, h3, -⟩ := hargs
  janus_run
  refine ⟨BitVec.ofNat 64 heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
  · simp only [retStateX]; rw [h1, h2, growCap8_1_0, callRegs_grow]; rfl
  · simp only [growsliceObj, h1, h2, h3, growCap8_1_0, show (BitVec.ofNat 64 heap).toNat = heap from rfl]
    exact ⟨fresh_heap _ _ hr (Nat.le_refl _) (by decide), fun i hi => absurd hi (by omega),
      fun i hi => absurd hi (by omega)⟩

/-- The arguments of `append(nil, x)`: `newLen = 1`, `oldCap = 0`, `num = 1`, `et` at `tyA`. -/
def r8 : Nat → W64 := fun i => if i = 1 then 1 else if i = 3 then 1 else if i = 4 then BitVec.ofNat 64 tyA else 0

theorem growslice_satisfiable : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady),
    GrowsliceContract (toy.link impl) A0 rt 4096 H ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ GrowslicePre 4096 s ∧ Ready H rt (growsliceArgs s) s :=
  ⟨_, _, _, growslice_impl,
    wstate8 r8, rfl,
    ⟨⟨callOK_w r8 5 (by omega), ⟨by decide, by decide⟩, by decide, by decide, by decide, by decide,
        by decide, by decide⟩, fun h => absurd h (by decide)⟩,
    ⟨by refine ⟨by decide, fun i hi => ?_⟩
        show (if _ then wmem8.bytes (heap + i) else 0) = 0
        split
        · show (if heap + i = tyA then (8 : Byte) else 0) = 0
          rw [if_neg (by simp only [heap, tyA]; omega)]
        · rfl,
     0, tyA, rfl⟩⟩

end Janus.Contracts.AllocSat
