import Janus.Contracts.Pool
import Janus.Contracts.LiveSat

/-!
# The `sync.Pool` live contracts are satisfiable (arm64)

For `PoolGetLive` and `PoolPutLive` of `Janus.Contracts.Pool`: machine code placed at the address
`A0` of a program with no other code, a proof by symbolic execution that it satisfies the contract
for the toy bump-allocator runtime `toyR` of `Janus.Contracts.LiveToy`, and a call state that
satisfies the whole precondition. `Get` always returns nil (a pool may be empty: the contract's
first disjunct) and `Put` drops its argument (the pool may drop what it is given), so neither
needs a shape: any `T` and `Sh` do.

The file also holds the toys the `sync.Pool` examples' witnesses need beyond `LiveSat`: a
`newobject` that serves a 24- or 32-byte descriptor (`newobject32_impl`) and a `growslice` that
serves `growslice(p, 1, 0, 1, et)` (`growslice8_impl`), on the same runtime, and the fact that
dropping ranges from the live set keeps the toy's invariant (`toyInv.drop`).
-/

namespace Janus.Contracts.PoolSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.Toy Janus.Contracts.LiveSat
open Janus.Contracts.AllocSat (toy A0 at0 link_at0 withCode)

/-! ## Dropping live ranges -/

/-- The toy's invariant holds for a sub-list of the live set (what `Put` does). -/
theorem toyInv_drop {tys : Tys} (hty : TysOK tys) {b : Nat} {L L' : List (Nat × Nat)} {g : Nat} {m : Memory}
    (hsub : ∀ r ∈ L', r ∈ L) (h : toyInv tys b L g (view (toyRt tys) L m)) :
    toyInv tys b L' g (view (toyRt tys) L' m) := by
  obtain ⟨p, hp, h1, h2, h3, hL, hz, hac, hacB, hacW, hT⟩ := h
  have hL' : ∀ r ∈ L', HEAP ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ p := fun r hr => hL r (hsub r hr)
  have eq : ∀ a n, InRanges a n (toyRt tys) → (a + n ≤ HEAP ∨ p ≤ a) →
      (view (toyRt tys) L' m).readLE a n = (view (toyRt tys) L m).readLE a n := by
    intro a n hin hout
    have o1 : Outside a n L := outside_of_forall fun r hr => by have := hL r hr; omega
    have o2 : Outside a n L' := outside_of_forall fun r hr => by have := hL' r hr; omega
    rw [readLE_view hin o1, readLE_view hin o2]
  have hb : BUMP + 8 ≤ HEAP := by simp [BUMP, HEAP]
  refine ⟨p, ?_, h1, h2, h3, hL', fun i hi hi' => ?_, by rw [view_accessible]; exact hac,
    by rw [view_accessible]; exact hacB, by rw [view_accessible]; exact hacW, fun t ht => ?_⟩
  · rw [eq _ _ (inRanges_bump tys) (Or.inl hb)]; exact hp
  · rw [eq _ _ (inRanges_heap (n := 1) (by omega) (by omega)) (Or.inr hi)]; exact hz i hi hi'
  · have hr := hT t ht
    have ht' : t.1 + 16 ≤ BUMP := (hty t ht).1
    rw [eq _ _ (inRanges_ty ht (n := 8) (by omega)) (Or.inl (by omega)),
      eq _ _ (InRanges.sub (inRanges_ty ht (n := 16) (by omega)) (by omega) (by omega)) (Or.inl (by omega))]
    exact hr


/-! ## `newobject` of a 24- or 32-byte descriptor, `growslice(p, 1, 0, 1, et)` -/

set_option maxRecDepth 20000 in
/-- The toy `newobject` for descriptors whose block is `K` bytes, `16 < K ≤ 32` (it advances the bump
pointer by 32). -/
theorem newobject32_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) (K : Nat)
    (hK1 : 16 < K) (hK2 : K ≤ 32)
    (hok' : ∀ args, ok A0 args → ∃ t ∈ tys, args = [t.1] ∧ blockSize t.2.1 (t.2.2 == 0) = K) :
    NewobjectLiveContract (toy.link (at0 (bumpCode 32))) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩ := pre.1
  janus_run
  exact finish_newobject hty (K := K) (by omega) (by omega) (by omega) hok' pre

/-- `X9 = BUMP; X0 = [X9]; X10 = X0 + 16; [X9] = X10; X2 = 1; RET`: the next 16 bytes of the heap
and `(ptr, newLen, 1)`. -/
def growCode8 : List Nat := [0xd2a00809, 0xf9400120, 0x9100000a + 16 * 1024, 0xf900012a, 0xd2800022, 0xd65f03c0]

/-- The state `growCode8` returns in. -/
def growFinal8 (s : State) : State :=
  { s with
    regs := setReg (setReg (setReg (setReg s.regs 0 (BitVec.ofNat 64 (s.mem.readLE BUMP 8))) 2 1) 9
      (BitVec.ofNat 64 BUMP)) 10 (BitVec.ofNat 64 (s.mem.readLE BUMP 8) + BitVec.ofNat 64 16),
    pc := s.regs 30, mem := s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + 16) }

theorem growFinal8_ret (s : State) (p : Nat) (hp : s.mem.readLE BUMP 8 = p) :
    growFinal8 s = retStateX s (growFinal8 s).regs [BitVec.ofNat 64 p, s.regs 1, 1] s.flags s.vregs
      (s.mem.writeLE BUMP 8 (p + 16)) s.excl s.exclPass := by
  subst hp
  simp only [growFinal8, retStateX]
  congr 1
  funext i
  simp only [callRegs, setReg]
  by_cases h : i = 18 ∨ i = 28 ∨ i = 29
  · rw [if_pos h]; rcases h with rfl | rfl | rfl <;> simp
  · rw [if_neg h]
    rcases i with _ | _ | _ | i <;> simp [List.getD]

theorem finish_growslice8 {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr b : Nat}
    {L : List (Nat × Nat)} {s : State}
    (hok' : ∀ args, ok addr args → ∃ p et, args = [p, 1, 0, 1, et])
    (pre : GrowslicePre 4096 s ∧ StackRoom s 4096 5 ∧
      LiveAt (toyR tys ok) addr (growsliceArgs s) L b (growsliceRound s) (s.regs 28).toNat s.mem
        (calleeStack s 4096 5)) :
    LiveAllocRet (toyR tys ok) 4096 5
      (fun ptr => [ptr, s.regs 1, BitVec.ofNat 64 (growCap8 (s.regs 1).toNat (s.regs 2).toNat)])
      L b (growsliceRound s) (growsliceRound s) s (growFinal8 s) fun m ptr =>
        growsliceObj (toyR tys ok).rt s m ptr ∧ ApartAll ptr (growsliceRound s) L := by
  obtain ⟨-, -, hok, hinv, hcost, hLs, hWs⟩ := pre
  obtain ⟨p0, et, hargs⟩ := hok' _ hok
  simp only [growsliceArgs, List.cons.injEq, and_true] at hargs
  obtain ⟨-, h1, h2, h3, -⟩ := hargs
  have hg : growCap8 1 0 = 1 := by decide
  have hR : growsliceRound s = 8 := by simp only [growsliceRound, h1, h2, hg]
  rw [hR] at hcost ⊢
  refine bump_ret hty (A := 16) (by omega) (by omega) (by omega) rfl rfl hcost hinv hWs _ _ (fun p hp => ?_) (fun p h1' h2' hend hz hacc hap => ⟨?_, hap⟩)
  · have := growFinal8_ret s p hp
    simp only [h1, h2, hg] at this ⊢
    exact this
  · simp only [growsliceObj, h1, h2, h3, hg]
    refine ⟨toy_fresh h1' h2' hend hz hacc _ (by omega) _ _, fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩

set_option maxRecDepth 20000 in
theorem growslice8_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ p et, args = [p, 1, 0, 1, et]) :
    GrowsliceLiveContract (toy.link (at0 growCode8)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _, _, _, _, _, _⟩, _⟩ := pre.1
  janus_run
  exact finish_growslice8 hty hok' pre

/-! ## `Get` and `Put` -/

/-- `Get` returning nil: `mov x0, #0; mov x1, #0; ret`. -/
def getCode : List Nat := [0xd2800000, 0xd2800001, 0xd65f03c0]
/-- `Put` dropping its argument: `ret`. -/
def putCode : List Nat := [0xd65f03c0]

/-- The state `getCode` returns in. -/
def getFinal (s : State) : State :=
  { s with regs := Map.keepABI s.regs (setReg (setReg s.regs 0 0) 1 0), pc := s.regs 30 }

/-- The state `putCode` returns in. -/
def putFinal (s : State) : State := { s with pc := s.regs 30 }

theorem keepABI_self (r : Nat → W64) : Map.keepABI r r = r := by
  funext i; simp only [Map.keepABI]; split <;> rfl

theorem getFinal_eq (s : State) :
    ({ s with regs := setReg (setReg s.regs 0 0#64) 1 0#64, pc := s.regs 30 } : State) = getFinal s := by
  simp only [getFinal]
  congr 1
  funext i
  simp only [Map.keepABI, setReg]
  by_cases h : i = 18 ∨ i = 28 ∨ i = 29
  · rw [if_pos h]; rcases h with rfl | rfl | rfl <;> simp
  · rw [if_neg h]; rfl

set_option maxRecDepth 10000 in
theorem getCode_run : ∀ s : State, s.pc = BitVec.ofNat 64 A0 → (s.regs 30).toNat < 2 ^ 48 →
    (s.regs 30).toNat % 4 = 0 → ReachesRet (withCode getCode) (s.regs regLR) s (fun s' => s' = getFinal s) := by
  intro s hpc h30 h30'
  janus_run
  exact getFinal_eq s

set_option maxRecDepth 10000 in
theorem putCode_run : ∀ s : State, s.pc = BitVec.ofNat 64 A0 → (s.regs 30).toNat < 2 ^ 48 →
    (s.regs 30).toNat % 4 = 0 → ReachesRet (withCode putCode) (s.regs regLR) s (fun s' => s' = putFinal s) := by
  intro s hpc h30 h30'
  janus_run
  rfl

set_option maxRecDepth 10000 in
/-- Every code that runs to the return in the state `getFinal s` meets `PoolGetLive`. -/
theorem poolGetLive_of_run (tys : Tys) (ok : Nat → List Nat → Prop) (p : Program) (addr : Nat)
    (T : Nat) (Sh : PoolShape)
    (hrun : ∀ s : State, s.pc = BitVec.ofNat 64 addr → (s.regs 30).toNat < 2 ^ 48 →
      (s.regs 30).toNat % 4 = 0 → ReachesRet p (s.regs regLR) s (fun s' => s' = getFinal s)) :
    PoolGetLive p addr 4096 (toyR tys ok) T Sh := by
  intro L b s hpc ⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _, _, hinv, _, _, _⟩
  obtain ⟨k, s', hst, hpc', rfl⟩ := hrun s hpc h30b h30a
  refine ⟨k, getFinal s, hst, hpc', ?_⟩
  unfold LiveRet
  refine ⟨setReg (setReg s.regs 0 0) 1 0, s.vregs, s.flags, s.mem, s.excl, s.exclPass, rfl, MemFrame.refl _ _,
    LiveFrame.refl _ _ _, rfl, Or.inl ⟨?_, ?_, hinv⟩⟩
  · simp [setReg]
  · simp [setReg]

set_option maxRecDepth 10000 in
/-- Every code that runs to the return in the state `putFinal s` meets `PoolPutLive`. -/
theorem poolPutLive_of_run (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) (p : Program)
    (addr : Nat) (T : Nat) (Sh : PoolShape)
    (hrun : ∀ s : State, s.pc = BitVec.ofNat 64 addr → (s.regs 30).toNat < 2 ^ 48 →
      (s.regs 30).toNat % 4 = 0 → ReachesRet p (s.regs regLR) s (fun s' => s' = putFinal s)) :
    PoolPutLive p addr 4096 (toyR tys ok) T Sh := by
  intro L b rs s hpc ⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _, _, hsub, _, hinv, _, _, _⟩
  obtain ⟨k, s', hst, hpc', rfl⟩ := hrun s hpc h30b h30a
  refine ⟨k, putFinal s, hst, hpc', ?_⟩
  unfold LiveRet
  refine ⟨s.regs, s.vregs, s.flags, s.mem, s.excl, s.exclPass, ?_, MemFrame.refl _ _, LiveFrame.refl _ _ _, rfl,
    toyInv_drop hty (g := (s.regs 28).toNat) (fun r h => mem_dropAll h) hinv⟩
  simp only [putFinal, keepABI_self]

theorem poolGetLive_impl (ok : Nat → List Nat → Prop) (T : Nat) (Sh : PoolShape) :
    PoolGetLive (toy.link (at0 getCode)) A0 4096 (toyR tys0 ok) T Sh := by
  rw [link_at0]; exact poolGetLive_of_run tys0 ok _ _ T Sh getCode_run

theorem poolPutLive_impl (ok : Nat → List Nat → Prop) (T : Nat) (Sh : PoolShape) :
    PoolPutLive (toy.link (at0 putCode)) A0 4096 (toyR tys0 ok) T Sh := by
  rw [link_at0]; exact poolPutLive_of_run tys0 tysOK0 ok _ _ T Sh putCode_run

/-- The pool struct of the witnesses (its 40 bytes read as zero). -/
def POOL : Nat := 0x30100

def okPool : Nat → List Nat → Prop := fun _ args => args = [POOL]

/-- The witness call state of `Get`/`Put`: the pool in `X0`, `T` in `X1`. -/
def pstate : State := wstate fun i => if i = 0 then BitVec.ofNat 64 POOL else if i = 1 then 0x77 else 0

set_option maxRecDepth 10000 in
theorem pstate_pre (n : Nat) (hn : n = 1 ∨ n = 3) :
    CallOK pstate 4096 n ∧ StackRoom pstate 4096 n ∧
      LiveAt (toyR tys0 okPool) A0 [(pstate.regs 0).toNat] [] 0x400 0 (pstate.regs 28).toNat pstate.mem
        (calleeStack pstate 4096 n) := by
  rcases hn with rfl | rfl
  · refine ⟨wcallOK _ 1 (by omega), wguard _ 1 (by omega), ?_, wmem_inv (pstate.regs 28).toNat, by omega, by simp, wwin _ 1 (by omega)⟩
    simp [pstate, wstate]
    show [POOL % 18446744073709551616] = [POOL]
    simp [POOL]
  · refine ⟨wcallOK _ 3 (by omega), wguard _ 3 (by omega), ?_, wmem_inv (pstate.regs 28).toNat, by omega, by simp, wwin _ 3 (by omega)⟩
    simp [pstate, wstate]
    show [POOL % 18446744073709551616] = [POOL]
    simp [POOL]

theorem pstate_new : pstate.mem.readLE ((pstate.regs 0).toNat + newOffset) 8 = 0 := by
  unfold newOffset; decide

theorem poolGetLive_satisfiable : ∃ (R : RtInv) (T : Nat) (Sh : PoolShape) (impl : List Segment),
    PoolGetLive (toy.link impl) A0 4096 R T Sh ∧
    ∃ (s : State) (L : List (Nat × Nat)) (b : Nat), s.pc = BitVec.ofNat 64 A0 ∧
      CallOK s 4096 1 ∧ StackRoom s 4096 1 ∧ s.mem.readLE ((s.regs 0).toNat + newOffset) 8 = 0 ∧
      LiveAt R A0 [(s.regs 0).toNat] L b 0 (s.regs 28).toNat s.mem (calleeStack s 4096 1) :=
  ⟨toyR tys0 okPool, 0x77, SliceObj 8, at0 getCode, poolGetLive_impl okPool 0x77 (SliceObj 8), pstate, [], 0x400,
    rfl, (pstate_pre 1 (Or.inl rfl)).1, (pstate_pre 1 (Or.inl rfl)).2.1, pstate_new,
    (pstate_pre 1 (Or.inl rfl)).2.2⟩

theorem poolPutLive_satisfiable : ∃ (R : RtInv) (T : Nat) (Sh : PoolShape) (impl : List Segment),
    PoolPutLive (toy.link impl) A0 4096 R T Sh ∧
    ∃ (s : State) (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)), s.pc = BitVec.ofNat 64 A0 ∧
      CallOK s 4096 3 ∧ StackRoom s 4096 3 ∧ (s.regs 1).toNat = T ∧ Sh s.mem (s.regs 2).toNat rs ∧
      (∀ r ∈ rs, r ∈ L) ∧
      LiveAt R A0 [(s.regs 0).toNat] L b 0 (s.regs 28).toNat s.mem (calleeStack s 4096 3) :=
  ⟨toyR tys0 okPool, 0x77, fun _ _ rs => rs = [], at0 putCode, poolPutLive_impl okPool 0x77 _, pstate, [], 0x400, [],
    rfl, (pstate_pre 3 (Or.inr rfl)).1, (pstate_pre 3 (Or.inr rfl)).2.1, by decide, rfl, fun _ h => h,
    (pstate_pre 3 (Or.inr rfl)).2.2⟩

end Janus.Contracts.PoolSat
