import Janus.Contracts.WriteBarrier
import Janus.Contracts.MallocSC
import Janus.Contracts.Mem

/-!
# Live allocation contracts: allocations and write barriers that compose over many calls (arm64)

The allocation contracts of `Janus.Contracts.Alloc` take a readiness predicate `H` that the
theorem assumes **for the one call** it makes, and let the allocator change any byte of the
runtime-owned ranges `rt`: a theorem cannot make a second call (its readiness is not handed back),
and the second object may overlap the first or overwrite what the caller stored into it. The
*live* contracts of this file are stated so that a theorem can make any number of calls, a
data-dependent number included, and keep every object it allocated.

**The interface (stable; agent/pool codes against it).** ONE hypothesis `R : RtInv` is threaded
through every runtime call of a function, whatever it calls:

```
structure RtInv where
  inv : Nat → List (Nat × Nat) → Nat → Memory → Prop   -- budget, live set L, g, view
  ok  : Nat → List Nat → Prop                          -- requests served, by (address, args)
  rt  : List (Nat × Nat)                               -- the runtime's private ranges
  ext : (inv depends only on bytes and accessibility)
```

Every contract is `∀ L b, Summary p addr pre post` over this `R` (no separate `rt`, no `MemModel`),
its precondition has `LiveAt`/`LiveMemAt` (`R.ok`, `R.inv b L g (view R.rt L m)`, the live set and
the callee's window apart, the window outside `R.rt`), and its postcondition keeps the memory
frame (`MemFrame` in `R.rt` ∪ window ∪ destination, `LiveFrame` for `L`) and re-establishes
`R.inv` (for `L ++ new objects` and the budget less the cost). The contracts: `MallocgcLiveContract`,
`NewobjectLiveContract`, `MakesliceLiveContract`, `GrowsliceLiveContract`, the SC variants,
`WbLiveContract` (`gcWriteBarrierN`), `RtLiveContract` (the string and slice specs, `rawstring`
and the bulk barriers via `LiveSpec`), and the copies and clears `MemmoveLive`,
`MemclrNoHeapPointersLive`, `TypedMemmoveLive`, `TypedMemclrLive`, `MemclrHasPointersLive`.
A new runtime function (e.g. `sync.Pool` `Get`/`Put`) is a contract of the same shape: take `R`,
state `LiveAt`-style preconditions, `MemFrame (R.rt ++ window ++ writes)`, `LiveFrame s.mem m L
writes`, new objects `ApartAll _ _ L`, and `R.inv b' (L ++ adds) g (view R.rt (L ++ adds) m)`.
The `Mem.MemModel` family is kept as legacy contracts; `MemModel.ofRt R` states one over a live runtime's model. Every Go ABIInternal contract returns in `retStateX` (`retStateX_intro` proves a state is one); the barrier returns in `wbRetX`.

**The live set.** A ghost list `L` of byte ranges `[lo, hi)`: the heap objects the program holds
(every object a live allocation returned is added to it). It is not stored anywhere; a theorem
threads it through its calls. `view rt L m` is the memory **as the runtime sees it**: the bytes
inside `rt` that are outside `L`, every other byte 0, and the regions. The program's own stores go
either outside `rt` or into its live objects, so they never change the view
(`view_writeLE_out`, `view_writeLE_live`).

**The runtime invariant.** A theorem quantifies over `R : RtInv`, which has

* `R.inv b L g v`: the runtime is in a state from which it serves the program's next calls: `b`
  is the **budget** (bytes the runtime can still allocate), `L` the live set, `g` the current
  goroutine (arm64 `R28`, amd64 `R14`) and `v` the view;
* `R.ok addr args`: the requests the runtime at `addr` serves with these argument words (for the
  real runtime, every request the precondition admits; the toy witnesses use it to restrict the
  arguments to the ones they implement).

Every live contract is a `∀ L b, Summary …`: from a call state with `R.ok addr args`,
`R.inv b L g (view rt L s.mem)`, `cost ≤ b` (the request fits the budget) and the live set
outside the callee's stack window (`LiveSep`), the function returns with

* the object (`[ptr, ptr + round)`) inside `rt`, **outside `L`** and outside the callee's stack
  window (so disjoint from every object the program holds, and from its frame, which a caller
  keeps outside `rt`);
* memory changed only inside `rt` and the callee's stack window (`MemFrame`), and **not in the
  live objects** (`LiveFrame s.mem m L ws`: every read inside an object of `L` is the same,
  except in the ranges `ws` the function writes on purpose, e.g. a copy's destination);
* `R.inv (b - cost) (L ++ [obj]) g (view rt (L ++ [obj]) m)`: the invariant again, for the live
  set with the new object and the budget less the call's cost. So the postcondition establishes
  the next call's precondition, for as many calls as the budget allows.

The budget is what keeps the contracts satisfiable (round 10 V2: a contract that hands back all
its precondition needs can be chained without bound, and no code with finite memory can hand
out unboundedly many disjoint objects): each allocating call costs its block size (`blockSize`,
at least 1 byte for a non-empty object), so a theorem that allocates `n` objects assumes a
budget of their total size at its entry. A call that allocates nothing (a write barrier, a copy)
costs nothing.

**`growslice` and the old array.** The live `growslice` keeps the old array in `L`: the runtime
does not free it (only the collector does, once it is unreachable, and the caller may still hold
the old slice), so a caller that had it in `L` keeps knowing its contents, and the new array is
disjoint from it. Dropping it from `L` would let a later allocation reuse it, which the real
runtime does only after the collector found it unreachable, and would require the invariant to
be monotone in `L`, which the contract cannot state for an arbitrary runtime.

**Write barriers.** `WbLiveContract` (`gcWriteBarrierN`): the `8·N` buffer slots it returns are
runtime memory outside `L` that the caller then fills, so its postcondition gives the invariant
for **every** content of those slots (`InvSlots`). The bulk barriers (`wbZero`, `wbMove`,
`bulkBarrierPreWrite`) are `RtLiveContract`s of their `RtSpec`s. None of these contracts mentions
the flag `runtime.writeBarrier.enabled`: they hold in both flag states. The caller reads the flag
inline; it is runtime memory (inside `rt`), so after any call that may write `rt` (an allocation
may start a GC cycle) its value is unknown and a theorem covers both branches.

**What is trusted** (docs/SOUNDNESS.md, "Live allocation"): that the Go 1.26 runtime meets these
contracts for some `R` that holds at the theorem's entry; in particular that the collector frees
no object of `L` while the program holds it (it frees only unreachable objects, and the program
keeps every object of `L` reachable from its roots), and that the runtime's behaviour does not
depend on the bytes of the live objects or of the filled barrier slots beyond what a
type-correct Go program stores there (valid pointers or nil in pointer slots).

**Migration.** The single-call contracts stay (`Janus.Contracts.Alloc`), and each follows from
its live form for a derived readiness predicate (`MallocgcLiveContract.ready`, …), so a proof
against them is a proof against the live contracts too.
-/

namespace Janus.Contracts

open Janus Janus.Arm64 Janus.Tactic Janus.Spec

/-! ## The runtime's view with the live set masked -/

/-- `a` lies in one of the ranges `[lo, hi)` of `rs`. -/
def inRs (rs : List (Nat × Nat)) (a : Nat) : Bool := rs.any fun r => decide (r.1 ≤ a) && decide (a < r.2)

/-- `m` as the runtime sees it, with the live set `L` masked: the bytes inside `rt` and outside
`L`, every other byte `0`, and the regions. -/
def view (rt L : List (Nat × Nat)) (m : Memory) : Memory :=
  { bytes := fun a => if inRs rt a && !inRs L a then m.bytes a else 0, regions := m.regions }

theorem inRs_of_inRanges {a n : Nat} {rs : List (Nat × Nat)} (h : InRanges a n rs) {x : Nat}
    (h1 : a ≤ x) (h2 : x < a + n) : inRs rs x = true := by
  obtain ⟨r, hr, h3, h4⟩ := h
  exact List.any_eq_true.2 ⟨r, hr, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩

theorem inRs_of_outside {a n : Nat} {rs : List (Nat × Nat)} (h : Outside a n rs) {x : Nat}
    (h1 : a ≤ x) (h2 : x < a + n) : inRs rs x = false := by
  unfold inRs
  rw [List.any_eq_false]
  intro r hr
  have := MemFrame.outside_mem h hr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

@[simp] theorem view_regions (rt L : List (Nat × Nat)) (m : Memory) : (view rt L m).regions = m.regions := rfl

@[simp] theorem view_accessible (rt L : List (Nat × Nat)) (m : Memory) (a n : Nat) (w : Bool) :
    (view rt L m).accessible a n w = m.accessible a n w := rfl

/-- With an empty live set the view is round 9's `rtView`. -/
theorem view_nil (rt : List (Nat × Nat)) (m : Memory) : view rt [] m = rtView rt m := by
  simp only [view, rtView, inRs, List.any_nil, Bool.not_false, Bool.and_true]

/-- The view does not depend on the bytes outside `rt`. -/
theorem view_rtView (rt L : List (Nat × Nat)) (m : Memory) : view rt L (rtView rt m) = view rt L m := by
  simp only [view, rtView, Memory.mk.injEq, and_true]
  funext a
  unfold inRs
  by_cases h : rt.any (fun r => decide (r.1 ≤ a) && decide (a < r.2)) = true <;> simp [h]

/-- A store outside the runtime-owned ranges does not change the view. -/
theorem view_writeLE_out {rt L : List (Nat × Nat)} {m : Memory} {a n v : Nat} (h : Outside a n rt) :
    view rt L (m.writeLE a n v) = view rt L m := by
  simp only [view, Memory.mk.injEq, Memory.regions_writeLE, and_true]
  funext x
  by_cases hx : a ≤ x ∧ x < a + n
  · rw [inRs_of_outside h hx.1 hx.2]; simp
  · rw [Memory.bytes_writeLE_outside _ (by omega)]

/-- A store into a live object does not change the view. -/
theorem view_writeLE_live {rt L : List (Nat × Nat)} {m : Memory} {a n v : Nat} (h : InRanges a n L) :
    view rt L (m.writeLE a n v) = view rt L m := by
  simp only [view, Memory.mk.injEq, Memory.regions_writeLE, and_true]
  funext x
  by_cases hx : a ≤ x ∧ x < a + n
  · rw [inRs_of_inRanges h hx.1 hx.2]; simp
  · rw [Memory.bytes_writeLE_outside _ (by omega)]

/-- A store inside `rt` and outside the live set (e.g. into a write barrier's buffer slots) is a
store into the view. -/
theorem view_writeLE_vis {rt L : List (Nat × Nat)} {m : Memory} {a n v : Nat} (h1 : InRanges a n rt)
    (h2 : Outside a n L) : view rt L (m.writeLE a n v) = (view rt L m).writeLE a n v := by
  simp only [view, Memory.writeLE, Memory.mk.injEq, and_true]
  funext x
  by_cases hx : a ≤ x ∧ x < a + n
  · rw [inRs_of_inRanges h1 hx.1 hx.2, inRs_of_outside h2 hx.1 hx.2]; simp [hx]
  · simp [hx]

theorem view_bytes {rt L : List (Nat × Nat)} {m : Memory} {a : Nat} (h1 : InRanges a 1 rt)
    (h2 : Outside a 1 L) : (view rt L m).bytes a = m.bytes a := by
  simp only [view, inRs_of_inRanges h1 (Nat.le_refl a) (by omega),
    inRs_of_outside h2 (Nat.le_refl a) (by omega), Bool.not_false, Bool.and_self, ite_true]

/-- Reads inside `rt` and outside the live set are the same in the view. -/
theorem readLE_view {rt L : List (Nat × Nat)} {m : Memory} {a n : Nat} (h1 : InRanges a n rt)
    (h2 : Outside a n L) : (view rt L m).readLE a n = m.readLE a n :=
  Memory.readLE_congr fun i hi => view_bytes (h1.sub (by omega) (by omega)) (Outside.of_sub h2 (by omega) (by omega))

/-- Zero bytes of the view (inside `rt`, outside `L`) are zero in memory. -/
theorem ZeroBytes.of_view {rt L : List (Nat × Nat)} {m : Memory} {a n : Nat} (hz : ZeroBytes (view rt L m) a n)
    (h1 : InRanges a n rt) (h2 : Outside a n L) : ZeroBytes m a n := by
  intro i hi
  rw [← view_bytes (rt := rt) (L := L) (h1.sub (by omega) (by omega)) (Outside.of_sub h2 (by omega) (by omega))]
  exact hz i hi

/-! ## The live runtime -/

/-- **The live runtime** a theorem quantifies over (see the module documentation): `inv b L g v`,
the runtime's invariant for the budget `b`, the live set `L`, the goroutine `g` and the view `v`;
`ok addr args`, the requests the runtime function at `addr` serves. -/
structure RtInv where
  inv : Nat → List (Nat × Nat) → Nat → Memory → Prop
  ok : Nat → List Nat → Prop
  /-- The runtime-owned ranges (heap arenas, `mcache`, `mspan`s, `m`, `p`, GC buffers, barrier
  buffers, the runtime's own memory, the write-barrier flag): the only memory a runtime call may
  change besides the callee's stack window and the caller-designated destination. -/
  rt : List (Nat × Nat)
  /-- The invariant depends only on what the memory holds: bytes and accessible ranges (so it
  can be moved between two memories that agree on both, e.g. the views of `Agrees` memories). -/
  ext : ∀ b L g (v v' : Memory), (∀ a, v'.bytes a = v.bytes a) →
    (∀ a n w, v'.accessible a n w = v.accessible a n w) → inv b L g v → inv b L g v'

/-- Every object of the live set lies outside the ranges `win` (a callee's stack window). -/
def LiveSep (L win : List (Nat × Nat)) : Prop := ∀ r ∈ L, Outside r.1 (r.2 - r.1) win

@[simp, janus_exec, janus_post, janus64_exec, janus64_post] theorem liveSep_nil
    (win : List (Nat × Nat)) : LiveSep [] win = True := by simp [LiveSep]
@[simp, janus_exec, janus_post, janus64_exec, janus64_post] theorem liveSep_cons (lo hi : Nat)
    (L win : List (Nat × Nat)) : LiveSep ((lo, hi) :: L) win = (Outside lo (hi - lo) win ∧ LiveSep L win) := by
  simp [LiveSep]
@[simp, janus_exec, janus_post, janus64_exec, janus64_post] theorem liveSep_append
    (L L' win : List (Nat × Nat)) : LiveSep (L ++ L') win = (LiveSep L win ∧ LiveSep L' win) := by
  simp only [LiveSep, List.mem_append]
  exact propext ⟨fun h => ⟨fun r hr => h r (Or.inl hr), fun r hr => h r (Or.inr hr)⟩,
    fun h r hr => hr.elim (h.1 r) (h.2 r)⟩

/-- `[a, a+n)` is `Apart` from every range of `rs`: `Outside`, in the form that the executors keep
as one `Apart` fact per range (the dischargers use them one at a time, `janus_apart`), instead
of disjunctions that `omega` would case-split on. The postconditions of the live contracts state
their disjointness facts this way. -/
def ApartAll (a n : Nat) (rs : List (Nat × Nat)) : Prop := ∀ r ∈ rs, Apart a n r.1 (r.2 - r.1)

@[simp, janus_exec, janus_post, janus64_exec, janus64_post] theorem apartAll_nil (a n : Nat) :
    ApartAll a n [] = True := by simp [ApartAll]
@[simp, janus_exec, janus_post, janus64_exec, janus64_post] theorem apartAll_cons (a n lo hi : Nat)
    (rs : List (Nat × Nat)) : ApartAll a n ((lo, hi) :: rs) = (Apart a n lo (hi - lo) ∧ ApartAll a n rs) := by
  simp [ApartAll]
@[simp, janus_exec, janus_post, janus64_exec, janus64_post] theorem apartAll_append (a n : Nat)
    (rs rs' : List (Nat × Nat)) : ApartAll a n (rs ++ rs') = (ApartAll a n rs ∧ ApartAll a n rs') := by
  simp only [ApartAll, List.mem_append]
  exact propext ⟨fun h => ⟨fun r hr => h r (Or.inl hr), fun r hr => h r (Or.inr hr)⟩,
    fun h r hr => hr.elim (h.1 r) (h.2 r)⟩

theorem ApartAll.outside {a n : Nat} {rs : List (Nat × Nat)} (h : ApartAll a n rs) : Outside a n rs := by
  induction rs with
  | nil => trivial
  | cons r rs ih =>
    obtain ⟨lo, hi⟩ := r
    have h1 := h (lo, hi) (List.mem_cons_self ..)
    simp only [Apart] at h1
    exact ⟨by omega, ih fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

attribute [janus_post, janus64_post] Nat.add_sub_cancel_left

/-- Every range of `L` is `Apart` from `win` (as `LiveSep`, in the `ApartAll` form). -/
def LiveApart (L win : List (Nat × Nat)) : Prop := ∀ r ∈ L, ApartAll r.1 (r.2 - r.1) win

@[simp, janus_exec, janus_post, janus64_exec, janus64_post] theorem liveApart_nil
    (win : List (Nat × Nat)) : LiveApart [] win = True := by simp [LiveApart]
@[simp, janus_exec, janus_post, janus64_exec, janus64_post] theorem liveApart_cons (lo hi : Nat)
    (L win : List (Nat × Nat)) : LiveApart ((lo, hi) :: L) win = (ApartAll lo (hi - lo) win ∧ LiveApart L win) := by
  simp [LiveApart]
@[simp, janus_exec, janus_post, janus64_exec, janus64_post] theorem liveApart_append
    (L L' win : List (Nat × Nat)) : LiveApart (L ++ L') win = (LiveApart L win ∧ LiveApart L' win) := by
  simp only [LiveApart, List.mem_append]
  exact propext ⟨fun h => ⟨fun r hr => h r (Or.inl hr), fun r hr => h r (Or.inr hr)⟩,
    fun h r hr => hr.elim (h.1 r) (h.2 r)⟩

theorem LiveApart.liveSep {L win : List (Nat × Nat)} (h : LiveApart L win) : LiveSep L win :=
  fun r hr => (h r hr).outside

/-- Every range of `fs` (new objects) lies outside the live set `L`. -/
def FreshFrom (fs L : List (Nat × Nat)) : Prop := ∀ r ∈ fs, ApartAll r.1 (r.2 - r.1) L

@[simp, janus_exec, janus_post, janus64_exec, janus64_post] theorem freshFrom_nil
    (L : List (Nat × Nat)) : FreshFrom [] L = True := by simp [FreshFrom]
@[simp, janus_exec, janus_post, janus64_exec, janus64_post] theorem freshFrom_cons (lo hi : Nat)
    (fs L : List (Nat × Nat)) : FreshFrom ((lo, hi) :: fs) L = (ApartAll lo (hi - lo) L ∧ FreshFrom fs L) := by
  simp [FreshFrom]

/-- The invariant up to the write barrier's buffer slots `[buf, buf + 8·n)`: it holds for the
view `view rt L m` with **any** contents of the slots (the caller fills them after the call). -/
def InvSlots (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g : Nat) (rt : List (Nat × Nat))
    (m : Memory) (buf n : Nat) : Prop :=
  ∀ v, MemFrame (view rt L m) v [(buf, buf + 8 * n)] → R.inv b L g v

theorem InvSlots.inv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g : Nat} {rt : List (Nat × Nat)}
    {m : Memory} {buf n : Nat} (h : InvSlots R b L g rt m buf n) : R.inv b L g (view rt L m) :=
  h _ (MemFrame.refl _ _)

/-- `janus_live`'s last step: the invariant at equal arguments. -/
theorem RtInv.inv_congr {R : RtInv} {b b' : Nat} {L : List (Nat × Nat)} {g g' : Nat} {v v' : Memory}
    (h : R.inv b' L g' v') (hb : b = b') (hg : g = g') (hv : v = v') : R.inv b L g v := by
  subst hb hg hv; exact h

theorem RtInv.ok_congr {R : RtInv} {a a' : Nat} {l l' : List Nat} (h : R.ok a' l') (ha : a = a')
    (hl : l = l') : R.ok a l := by
  subst ha hl; exact h

/-! ## The `janus_live` closer

The executors' precondition closers (`janus_run`, `janus64_run`) call `janus_live` on every part
of a callee's precondition they cannot close otherwise. For `R.inv b L g v` it takes the latest
hypothesis about `R.inv` (the entry's, or the last call's postcondition), determines the live set
and the budget of a live contract's call from it (they are metavariables there), and proves the
view at the call equal to the hypothesis's: the program's stores outside `rt` and into live
objects vanish from the view, stores into the barrier's slots become stores into the view
(`InvSlots`). For `R.ok a args` it uses a hypothesis with equal arguments. -/

open Lean Meta Elab Tactic in
/-- The side conditions of the view lemmas: `Outside a n rs` and `InRanges a n rs`. -/
elab "janus_live_disch" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  if t.isAppOfArity ``Janus.Outside 3 then
    if ← Common.dischargeOutside g then replaceMainGoal []; return
  if t.isAppOfArity ``Janus.InRanges 3 then
    if ← Common.dischargeInRanges g then replaceMainGoal []; return
  throwError "janus_live_disch: cannot prove{indentExpr t}"

open Lean Meta Elab Tactic in
/-- Prove `e₁ = e₂` (natural numbers): by defeq, else `omega`. -/
def liveEq (e1 e2 : Expr) : TacticM (Option Expr) := do
  if ← withReducible (isDefEq e1 e2) then return some (← mkEqRefl e1)
  let m ← mkFreshExprSyntheticOpaqueMVar (← mkEq e1 e2)
  let saved ← saveState
  try
    let gs ← Tactic.run m.mvarId! <| withoutRecover (evalTactic (← `(tactic|
      first | omega | (simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod] at *; omega))))
    if gs.isEmpty then return some m
    saved.restore; return none
  catch _ => saved.restore; return none

/-- An equation between argument words (numbers or lists of numbers), for `janus_live`. -/
macro "janus_live_eq" : tactic => `(tactic| first
  | rfl
  | omega
  | (simp only [List.cons.injEq, and_true, and_self]; done)
  | (simp only [List.cons.injEq, and_true]
     (repeat' apply And.intro) <;>
       first
       | rfl
       | omega
       | (simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
           Nat.reduceMod] at *; omega)))

open Lean Meta in
/-- `R.inv b L g v` (as the projection function or the primitive projection `R.1`): `R`, then
the arguments. -/
def invParts? (e : Expr) : Option (Expr × Array Expr) :=
  if e.isAppOfArity ``RtInv.inv 5 then some (e.getArg! 0, e.getAppArgs.extract 1 5)
  else match e.getAppFn with
    | .proj ``RtInv 0 r => if e.getAppNumArgs == 4 then some (r, e.getAppArgs) else none
    | _ => none

open Lean Meta in
/-- `R.ok a args`, likewise. -/
def okParts? (e : Expr) : Option (Expr × Array Expr) :=
  if e.isAppOfArity ``RtInv.ok 3 then some (e.getArg! 0, e.getAppArgs.extract 1 3)
  else match e.getAppFn with
    | .proj ``RtInv 1 r => if e.getAppNumArgs == 2 then some (r, e.getAppArgs) else none
    | _ => none

open Lean Meta Elab Tactic in
elab_rules : tactic | `(tactic| janus_live) => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  if let some (R, as) := invParts? t then
    let g ← g.replaceTargetDefEq (mkAppN (mkConst ``RtInv.inv) (#[R] ++ as))
    let bG := as[0]!
    let LG := as[1]!
    let gG := as[2]!
    let vG := as[3]!
    -- the latest hypothesis first
    for d in (← getLCtx).decls.toArray.reverse do
      let some d := d | continue
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      -- `R.inv b L g v` or `InvSlots R b L g rt m buf n`
      let (R1, b1, L1, g1, slots) ← do
        if let some (R1, a1) := invParts? ty then
          pure (R1, a1[0]!, a1[1]!, a1[2]!, false)
        else if ty.isAppOfArity ``InvSlots 8 then
          pure (ty.getArg! 0, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, true)
        else continue
      let saved ← saveState
      unless ← isDefEq R1 R do saved.restore; continue
      unless ← isDefEq LG L1 do saved.restore; continue
      let some hb ← liveEq bG b1 | saved.restore; continue
      let some hg ← liveEq gG g1 | saved.restore; continue
      let L1 ← instantiateMVars L1
      let vG ← instantiateMVars vG
      -- the invariant at the hypothesis's budget and goroutine, for the view at the call
      let g2 ← mkFreshExprSyntheticOpaqueMVar (mkAppN (mkConst ``RtInv.inv) #[R, b1, L1, g1, vG])
      let hstx ← Term.exprToSyntax d.toExpr
      let ok ← try
          let gs ← Tactic.run g2.mvarId! <| withoutRecover do
            evalTactic (← `(tactic| simp -failIfUnchanged (disch := janus_live_disch) only
              [Janus.Contracts.view_writeLE_out, Janus.Contracts.view_writeLE_live,
               Janus.Contracts.view_writeLE_vis]))
            if slots then
              evalTactic (← `(tactic| (apply $hstx; janus_frame)))
            else
              evalTactic (← `(tactic| with_reducible exact $hstx))
          pure gs.isEmpty
        catch _ => pure false
      unless ok do saved.restore; continue
      g.assign (← mkAppM ``RtInv.inv_congr #[g2, hb, hg, ← mkEqRefl vG])
      replaceMainGoal []
      return
    throwError "janus_live: no hypothesis gives the runtime invariant{indentExpr t}"
  if let some (R, as) := okParts? t then
    let g ← g.replaceTargetDefEq (mkAppN (mkConst ``RtInv.ok) (#[R] ++ as))
    for d in (← getLCtx).decls.toArray.reverse do
      let some d := d | continue
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (R1, _) := okParts? ty | continue
      let saved ← saveState
      unless ← isDefEq R1 R do saved.restore; continue
      let hstx ← Term.exprToSyntax d.toExpr
      let ok ← try
          let gs ← Tactic.run g <| withoutRecover (evalTactic (← `(tactic| first
            | with_reducible exact $hstx
            | (refine Janus.Contracts.RtInv.ok_congr $hstx ?_ ?_ <;> janus_live_eq))))
          pure gs.isEmpty
        catch _ => pure false
      if ok then replaceMainGoal []; return
      saved.restore
    throwError "janus_live: no hypothesis gives{indentExpr t}"
  throwError "janus_live: not a live goal"

/-! ## arm64 -/

/-- The runtime's stack checks fall through (arm64): `g.stackguard0 + stack < SP`, its word
outside the callee's window. -/
@[reducible] def StackRoom (s : State) (stack nargs : Nat) : Prop :=
  GuardOK s stack ∧ Outside ((s.regs 28).toNat + 16) 8 (calleeStack s stack nargs)

/-- The live part of a contract's precondition: the request is served (`R.ok`), the invariant
holds for the live set `L` and the budget `b` (`R.inv`, about the view), the request's `cost`
fits the budget, the live set is outside the callee's window `win` and the window outside the
runtime-owned ranges (the caller keeps its frame outside `rt`, as in every example). -/
@[reducible] def LiveAt (R : RtInv) (addr : Nat) (args : List Nat)
    (L : List (Nat × Nat)) (b cost g : Nat) (m : Memory) (win : List (Nat × Nat)) : Prop :=
  R.ok addr args ∧ R.inv b L g (view R.rt L m) ∧ cost ≤ b ∧ LiveSep L win ∧ LiveSep win R.rt

/-- The shape of a live allocation contract's postcondition (arm64): the callee returned to `X30`
(`retStateX`, results `res ptr`), memory changed only in `R.rt` and the callee's window and not in
the live objects, `Q m ptr` (the object, with its freshness for `L`), the object
`[ptr, ptr + round)` outside the callee's window, and the invariant for the live set with the
object and the budget less `cost`. -/
@[reducible] def LiveAllocRet (R : RtInv) (stack nargs : Nat)
    (res : W64 → List W64) (L : List (Nat × Nat)) (b cost round : Nat) (s s' : State)
    (Q : Memory → Nat → Prop) : Prop :=
  ∃ (ptr : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
    (ex : Option (Nat × Nat)) (ep : Nat → Bool),
    s' = retStateX s junk (res ptr) f v m ex ep ∧
      MemFrame s.mem m (R.rt ++ calleeStack s stack nargs) ∧ LiveFrame s.mem m L [] ∧
      Q m ptr.toNat ∧ ApartAll ptr.toNat round (calleeStack s stack nargs) ∧
      R.inv (b - cost) (L ++ [(ptr.toNat, ptr.toNat + round)]) (s.regs 28).toNat
        (view R.rt (L ++ [(ptr.toNat, ptr.toNat + round)]) m)

/-! ### `mallocgc` -/

/-- The block `mallocgc` hands out for the call state `s` (its cost). -/
@[reducible] def mallocgcRound (s : State) : Nat :=
  blockSize (s.regs 0).toNat ((s.regs 1).toNat == 0 || typNoscan s.mem (s.regs 1).toNat)

/-- **`runtime.mallocgc(size, typ, needzero)`, live** (arm64): `MallocgcContract`'s object
(fresh, aligned, zeroed as asked), also outside the live set, for as many calls as the budget
allows (see the module documentation). -/
def MallocgcLiveContract (p : Program) (addr : Nat) (stack : Nat)
    (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => MallocgcPre stack s ∧ StackRoom s stack 3 ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
        (s.regs 28).toNat s.mem (calleeStack s stack 3))
    (fun s s' => LiveAllocRet R stack 3 (fun ptr => [ptr]) L b (mallocgcRound s) (mallocgcRound s)
      s s' fun m ptr => 0 < (s.regs 0).toNat → mallocgcObj R.rt s m ptr ∧ ApartAll ptr (mallocgcRound s) L)

/-! ### `newobject` -/

@[reducible] def newobjectRound (s : State) : Nat :=
  blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat)

/-- **`runtime.newobject(typ)`, live** (arm64). -/
def NewobjectLiveContract (p : Program) (addr : Nat) (stack : Nat)
    (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => NewobjectPre stack s ∧ StackRoom s stack 1 ∧
      LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem
        (calleeStack s stack 1))
    (fun s s' => LiveAllocRet R stack 1 (fun ptr => [ptr]) L b (newobjectRound s) (newobjectRound s)
      s s' fun m ptr => 0 < typSize s.mem (s.regs 0).toNat →
        newobjectObj R.rt s m ptr ∧ ApartAll ptr (newobjectRound s) L)

/-! ### `makeslice` -/

@[reducible] def makesliceRound (s : State) : Nat :=
  blockSize (typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat) (typNoscan s.mem (s.regs 0).toNat)

/-- **`runtime.makeslice(et, len, cap)`, live** (arm64). -/
def MakesliceLiveContract (p : Program) (addr : Nat) (stack : Nat)
    (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => MakeslicePre stack s ∧ StackRoom s stack 3 ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (makesliceRound s)
        (s.regs 28).toNat s.mem (calleeStack s stack 3))
    (fun s s' => LiveAllocRet R stack 3 (fun ptr => [ptr]) L b (makesliceRound s) (makesliceRound s)
      s s' fun m ptr => 0 < typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat →
        makesliceObj R.rt s m ptr ∧ ApartAll ptr (makesliceRound s) L)

/-! ### `growslice` (8-byte pointer-free elements) -/

@[reducible] def growsliceRound (s : State) : Nat := 8 * growCap8 (s.regs 1).toNat (s.regs 2).toNat

/-- **`runtime.growslice`, live** (arm64; 8-byte pointer-free elements, as `GrowsliceContract`):
the new array holds the old elements and is outside the live set; the old array (in `L` if the
caller holds it) keeps its contents, and stays in `L`. -/
def GrowsliceLiveContract (p : Program) (addr : Nat) (stack : Nat)
    (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => GrowslicePre stack s ∧ StackRoom s stack 5 ∧
      LiveAt R addr (growsliceArgs s) L b (growsliceRound s) (s.regs 28).toNat s.mem
        (calleeStack s stack 5))
    (fun s s' => LiveAllocRet R stack 5
      (fun ptr => [ptr, s.regs 1, BitVec.ofNat 64 (growCap8 (s.regs 1).toNat (s.regs 2).toNat)])
      L b (growsliceRound s) (growsliceRound s) s s' fun m ptr =>
        growsliceObj R.rt s m ptr ∧ ApartAll ptr (growsliceRound s) L)

/-! ### Non-zero sizes -/

theorem MallocgcLiveContract.pos {p : Program} {addr : Nat} {stack : Nat}
    {R : RtInv} (h : MallocgcLiveContract p addr stack R) (L : List (Nat × Nat)) (b : Nat) :
    Summary p addr
      (fun s => (MallocgcPre stack s ∧ StackRoom s stack 3 ∧
        LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
          (s.regs 28).toNat s.mem (calleeStack s stack 3)) ∧ 0 < (s.regs 0).toNat)
      (fun s s' => LiveAllocRet R stack 3 (fun ptr => [ptr]) L b (mallocgcRound s) (mallocgcRound s)
        s s' fun m ptr => mallocgcObj R.rt s m ptr ∧ ApartAll ptr (mallocgcRound s) L) :=
  Summary.mono (h L b) (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, v, m, ex, ep, h1, h2, h3, h4, h5, h6⟩ =>
    ⟨ptr, j, f, v, m, ex, ep, h1, h2, h3, h4 hp.2, h5, h6⟩

theorem NewobjectLiveContract.pos {p : Program} {addr : Nat} {stack : Nat}
    {R : RtInv} (h : NewobjectLiveContract p addr stack R) (L : List (Nat × Nat)) (b : Nat) :
    Summary p addr
      (fun s => (NewobjectPre stack s ∧ StackRoom s stack 1 ∧
        LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem
          (calleeStack s stack 1)) ∧ 0 < typSize s.mem (s.regs 0).toNat)
      (fun s s' => LiveAllocRet R stack 1 (fun ptr => [ptr]) L b (newobjectRound s) (newobjectRound s)
        s s' fun m ptr => newobjectObj R.rt s m ptr ∧ ApartAll ptr (newobjectRound s) L) :=
  Summary.mono (h L b) (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, v, m, ex, ep, h1, h2, h3, h4, h5, h6⟩ =>
    ⟨ptr, j, f, v, m, ex, ep, h1, h2, h3, h4 hp.2, h5, h6⟩

theorem MakesliceLiveContract.pos {p : Program} {addr : Nat} {stack : Nat}
    {R : RtInv} (h : MakesliceLiveContract p addr stack R) (L : List (Nat × Nat)) (b : Nat) :
    Summary p addr
      (fun s => (MakeslicePre stack s ∧ StackRoom s stack 3 ∧
        LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (makesliceRound s)
          (s.regs 28).toNat s.mem (calleeStack s stack 3)) ∧
        0 < typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat)
      (fun s s' => LiveAllocRet R stack 3 (fun ptr => [ptr]) L b (makesliceRound s) (makesliceRound s)
        s s' fun m ptr => makesliceObj R.rt s m ptr ∧ ApartAll ptr (makesliceRound s) L) :=
  Summary.mono (h L b) (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, v, m, ex, ep, h1, h2, h3, h4, h5, h6⟩ =>
    ⟨ptr, j, f, v, m, ex, ep, h1, h2, h3, h4 hp.2, h5, h6⟩

/-! ### The size-specialised entry points (`GOEXPERIMENT=sizespecializedmalloc`) -/

/-- **`runtime.mallocgcSmallNoScanSC<n>`, live** (arm64): `MallocgcLiveContract` at the calls of
the entry point (`NoScanArgs n`). -/
def MallocgcSmallNoScanSCLiveContract (n : Nat) (p : Program) (addr : Nat)
    (stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => (MallocgcPre stack s ∧ StackRoom s stack 3 ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
        (s.regs 28).toNat s.mem (calleeStack s stack 3)) ∧
      NoScanArgs n s.mem (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => LiveAllocRet R stack 3 (fun ptr => [ptr]) L b (mallocgcRound s) (mallocgcRound s)
      s s' fun m ptr => mallocgcObj R.rt s m ptr ∧ ApartAll ptr (mallocgcRound s) L)

/-- **`runtime.mallocgcSmallScanNoHeaderSC<n>`, live** (arm64). -/
def MallocgcSmallScanNoHeaderSCLiveContract (n : Nat) (p : Program) (addr : Nat)
    (stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => (MallocgcPre stack s ∧ StackRoom s stack 3 ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
        (s.regs 28).toNat s.mem (calleeStack s stack 3)) ∧
      ScanArgs n s.mem (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => LiveAllocRet R stack 3 (fun ptr => [ptr]) L b (mallocgcRound s) (mallocgcRound s)
      s s' fun m ptr => mallocgcObj R.rt s m ptr ∧ ApartAll ptr (mallocgcRound s) L)

/-- **`runtime.mallocgcTinySize<n>`, live** (arm64). -/
def MallocgcTinySizeLiveContract (n : Nat) (p : Program) (addr : Nat)
    (stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => (MallocgcPre stack s ∧ StackRoom s stack 3 ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
        (s.regs 28).toNat s.mem (calleeStack s stack 3)) ∧
      TinyArgs n s.mem (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => LiveAllocRet R stack 3 (fun ptr => [ptr]) L b (mallocgcRound s) (mallocgcRound s)
      s s' fun m ptr => mallocgcObj R.rt s m ptr ∧ ApartAll ptr (mallocgcRound s) L)

theorem MallocgcLiveContract.smallNoScanSC {n : Nat} {p : Program} {addr : Nat} {rt : List (Nat × Nat)}
    {stack : Nat} {R : RtInv} (h : MallocgcLiveContract p addr stack R) :
    MallocgcSmallNoScanSCLiveContract n p addr stack R := fun L b =>
  Summary.mono (h.pos L b) (fun _ h => ⟨h.1, by have := h.2.1; omega⟩) fun _ _ _ h => h

theorem MallocgcLiveContract.smallScanNoHeaderSC {n : Nat} {p : Program} {addr : Nat}
    {stack : Nat} {R : RtInv} (h : MallocgcLiveContract p addr stack R) :
    MallocgcSmallScanNoHeaderSCLiveContract n p addr stack R := fun L b =>
  Summary.mono (h.pos L b) (fun _ h => ⟨h.1, h.2.1⟩) fun _ _ _ h => h

theorem MallocgcLiveContract.tinySize {n : Nat} {p : Program} {addr : Nat} {rt : List (Nat × Nat)}
    {stack : Nat} {R : RtInv} (h : MallocgcLiveContract p addr stack R) :
    MallocgcTinySizeLiveContract n p addr stack R := fun L b =>
  Summary.mono (h.pos L b) (fun _ h => ⟨h.1, by obtain ⟨h0, -, hs, -⟩ := h.2; omega⟩) fun _ _ _ h => h

/-! ### The write barrier (`gcWriteBarrierN`) -/

/-- The state `gcWriteBarrierN` returns in (arm64): registers by `wbRegs` (`R25 = buf`), the flags,
the SIMD&FP registers, the memory, the exclusive monitor and its outcomes as given. -/
def wbRetX (s : State) (junk : Nat → W64) (buf : W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
    (ex : Option (Nat × Nat)) (ep : Nat → Bool) : State :=
  { s with regs := wbRegs s.regs junk buf, pc := s.regs 30, flags := f, vregs := v, mem := m,
           excl := ex, exclPass := ep }

attribute [janus_exec, janus_post] wbRetX

/-- **`runtime.gcWriteBarrierN`, live** (arm64, `N = n`): as `WbContract`, from a call at which
the invariant holds (with the barrier on or off: the contract does not mention the flag); the
`8·n` slots it returns are inside `R.rt`, outside the live set and the stack window, the live
objects are unchanged, and the invariant holds again whatever the caller stores into the slots
(`InvSlots`). The barrier allocates nothing: the budget is unchanged. -/
def WbLiveContract (p : Program) (addr : Nat) (stack : Nat) (R : RtInv)
    (n : Nat) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => CallOK s stack 0 ∧ R.ok addr [n] ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
      LiveSep L [(s.sp.toNat - stack, s.sp.toNat - 8)] ∧
      LiveSep [(s.sp.toNat - stack, s.sp.toNat - 8)] R.rt)
    (fun s s' => ∃ (buf : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
        (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      s' = wbRetX s junk buf f v m ex ep ∧
      MemFrame s.mem m (R.rt ++ [(s.sp.toNat - stack, s.sp.toNat - 8)]) ∧ LiveFrame s.mem m L [] ∧
      WbSlots R.rt m buf.toNat n ∧ ApartAll buf.toNat (8 * n) L ∧
      ApartAll buf.toNat (8 * n) [(s.sp.toNat - stack, s.sp.toNat - 8)] ∧
      InvSlots R b L (s.regs 28).toNat R.rt m buf.toNat n)

/-! ## Memory copies and clears (`memmove`, `memclrNoHeapPointers`, the typed variants)

The same runtime hypothesis `R` is threaded through them. The destination `[a, a+n)` is either a
live object (`InRanges a n L`) or caller memory outside the runtime (`Outside a n R.rt`), so a
copy never changes the view (`view_writeLE_live`, `view_writeLE_out`): the invariant holds again
for the same `L` and `b`. They allocate nothing (cost 0) and are indifferent to the write-barrier
flag (the typed variants call `bulkBarrierPreWrite`, which touches runtime memory only). -/

/-- The destination of a copy or clear in a call at `s` (`nargs` arguments, stack bound `d`):
`n` writable bytes at `a`, below `2^48`, outside the callee's window, and either inside a live
object or outside the runtime-owned ranges. -/
def LiveDest (R : RtInv) (L : List (Nat × Nat)) (s : State) (d nargs a n : Nat) : Prop :=
  a + n ≤ 2 ^ 48 ∧ s.mem.accessible a n true = true ∧ Outside a n (calleeStack s d nargs) ∧
    (InRanges a n L ∨ Outside a n R.rt)

/-- The return of a live copy or clear (arm64): the canonical Go ABIInternal return state
`retStateX` (no result registers), memory changed only in `R.rt`, the callee's window and the
destination `extra`, the live objects unchanged except in `extra`, and the invariant again for the
same `L` and `b`. -/
def LiveMemRet (R : RtInv) (d nargs : Nat) (extra L : List (Nat × Nat)) (b : Nat) (s s' : State)
    (P : Memory → Prop) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat))
    (ep : Nat → Bool), s' = retStateX s junk [] f v m ex ep ∧
    MemFrame s.mem m (R.rt ++ calleeStack s d nargs ++ extra) ∧ LiveFrame s.mem m L extra ∧
    R.inv b L (s.regs 28).toNat (view R.rt L m) ∧ P m

/-- The live part of a copy's precondition: served, invariant, live set and window apart. -/
@[reducible] def LiveMemAt (R : RtInv) (addr : Nat) (args : List Nat) (L : List (Nat × Nat)) (b : Nat)
    (s : State) (win : List (Nat × Nat)) : Prop :=
  R.ok addr args ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ LiveSep L win ∧ LiveSep win R.rt

/-- **`runtime.memmove(dst, src, n)`, live** (`X0 = dst`, `X1 = src`, `X2 = n`). -/
def MemmoveLive (p : Program) (addr : Nat) (d : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => Mem.EqPre d 3 s ∧
      LiveMemAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s d 3) ∧
      Mem.Input s d 3 (s.regs 1).toNat (s.regs 2).toNat ∧
      LiveDest R L s d 3 (s.regs 0).toNat (s.regs 2).toNat)
    (fun s s' => LiveMemRet R d 3 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 2).toNat)] L b s s'
      fun m => Mem.Copied s.mem m (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat)

/-- **`runtime.memclrNoHeapPointers(ptr, n)`, live** (`X0 = ptr`, `X1 = n`). -/
def MemclrNoHeapPointersLive (p : Program) (addr : Nat) (d : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => Mem.EqPre d 2 s ∧
      LiveMemAt R addr [(s.regs 0).toNat, (s.regs 1).toNat] L b s (calleeStack s d 2) ∧
      LiveDest R L s d 2 (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => LiveMemRet R d 2 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 1).toNat)] L b s s'
      fun m => Mem.Zeroed m (s.regs 0).toNat (s.regs 1).toNat)

/-- **`runtime.typedmemmove(typ, dst, src)`, live** (barrier on or off). -/
def TypedMemmoveLive (p : Program) (addr : Nat) (d : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => Mem.EqPre d 3 s ∧
      LiveMemAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s d 3) ∧
      TypeOK s.mem (s.regs 0).toNat ∧ Outside (s.regs 0).toNat 16 (calleeStack s d 3) ∧
      Mem.Input s d 3 (s.regs 2).toNat (typSize s.mem (s.regs 0).toNat) ∧
      LiveDest R L s d 3 (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat))
    (fun s s' => LiveMemRet R d 3
      [((s.regs 1).toNat, (s.regs 1).toNat + typSize s.mem (s.regs 0).toNat)] L b s s'
      fun m => Mem.Copied s.mem m (s.regs 1).toNat (s.regs 2).toNat (typSize s.mem (s.regs 0).toNat))

/-- **`runtime.typedmemclr(typ, ptr)`, live**. -/
def TypedMemclrLive (p : Program) (addr : Nat) (d : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => Mem.EqPre d 2 s ∧
      LiveMemAt R addr [(s.regs 0).toNat, (s.regs 1).toNat] L b s (calleeStack s d 2) ∧
      TypeOK s.mem (s.regs 0).toNat ∧ Outside (s.regs 0).toNat 16 (calleeStack s d 2) ∧
      LiveDest R L s d 2 (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat))
    (fun s s' => LiveMemRet R d 2
      [((s.regs 1).toNat, (s.regs 1).toNat + typSize s.mem (s.regs 0).toNat)] L b s s'
      fun m => Mem.Zeroed m (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat))

/-- **`runtime.memclrHasPointers(ptr, n)`, live** (both multiples of 8). -/
def MemclrHasPointersLive (p : Program) (addr : Nat) (d : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => Mem.EqPre d 2 s ∧
      LiveMemAt R addr [(s.regs 0).toNat, (s.regs 1).toNat] L b s (calleeStack s d 2) ∧
      (s.regs 0).toNat % 8 = 0 ∧ (s.regs 1).toNat % 8 = 0 ∧
      LiveDest R L s d 2 (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => LiveMemRet R d 2 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 1).toNat)] L b s s'
      fun m => Mem.Zeroed m (s.regs 0).toNat (s.regs 1).toNat)

/-! ## The string, slice and bulk-barrier specs, live -/

/-- What a live `RtSpec` contract adds to the spec: the call's `cost` (bytes it may allocate), the
`fresh` objects it returns (writable by the caller: outside the live set) and the results it
`keep`s (e.g. a string's bytes, possibly shared with an operand); both join the live set. -/
structure LiveSpec where
  cost : List Nat → Memory → Nat := fun _ _ => 0
  fresh : List Nat → Memory → Nat → Nat → Nat → List (Nat × Nat) := fun _ _ _ _ _ => []
  keep : List Nat → Memory → Nat → Nat → Nat → List (Nat × Nat) := fun _ _ _ _ _ => []

/-- The precondition of `RtLiveContract` (arm64). -/
@[reducible] def RtLivePre (stack : Nat) (R : RtInv) (sp : RtSpec) (ls : LiveSpec)
    (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK s stack sp.nargs ∧ sp.pre (argWords s sp.nargs) s.mem ∧
    ReadsOutside (sp.reads (argWords s sp.nargs) s.mem) (calleeStack s stack sp.nargs) ∧
    (match sp.guard with
      | some adj => Janus.Spec.GuardOK s adj ∧
          Outside ((s.regs 28).toNat + 16) 8 (calleeStack s stack sp.nargs)
      | none => True) ∧
    StackRoom s stack sp.nargs ∧
    LiveAt R addr (argWords s sp.nargs) L b (ls.cost (argWords s sp.nargs) s.mem) (s.regs 28).toNat
      s.mem (calleeStack s stack sp.nargs)

/-- The objects a live `RtSpec` call adds to the live set. -/
@[reducible] def liveAdds (ls : LiveSpec) (a : List Nat) (m : Memory) (r0 r1 r2 : Nat) : List (Nat × Nat) :=
  ls.fresh a m r0 r1 r2 ++ ls.keep a m r0 r1 r2

/-- The postcondition of `RtLiveContract` (arm64). -/
@[reducible] def RtLivePost (stack : Nat) (R : RtInv) (sp : RtSpec) (ls : LiveSpec)
    (L : List (Nat × Nat)) (b : Nat) (s s' : State) : Prop :=
  ∃ (r0 r1 r2 : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
    (ex : Option (Nat × Nat)) (ep : Nat → Bool),
    s' = retStateX s junk [r0, r1, r2] f v m ex ep ∧
      MemFrame s.mem m (rtIf sp.rtWrites R.rt ++ calleeStack s stack sp.nargs ++
        sp.writes (argWords s sp.nargs) s.mem) ∧
      sp.post R.rt (argWords s sp.nargs) s.mem r0.toNat r1.toNat r2.toNat m ∧
      LiveFrame s.mem m L (sp.writes (argWords s sp.nargs) s.mem) ∧
      FreshFrom (ls.fresh (argWords s sp.nargs) s.mem r0.toNat r1.toNat r2.toNat) L ∧
      LiveApart (liveAdds ls (argWords s sp.nargs) s.mem r0.toNat r1.toNat r2.toNat) (calleeStack s stack sp.nargs) ∧
      R.inv (b - ls.cost (argWords s sp.nargs) s.mem)
        (L ++ liveAdds ls (argWords s sp.nargs) s.mem r0.toNat r1.toNat r2.toNat) (s.regs 28).toNat
        (view R.rt (L ++ liveAdds ls (argWords s sp.nargs) s.mem r0.toNat r1.toNat r2.toNat) m)

/-- **The live arm64 contract of the spec `sp`** (with the live data `ls`) at `addr`. -/
def RtLiveContract (p : Program) (addr : Nat) (stack : Nat) (R : RtInv)
    (sp : RtSpec) (ls : LiveSpec) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr (RtLivePre stack R sp ls addr L b)
    (RtLivePost stack R sp ls L b)

/-! ### The live data of each spec -/

/-- A non-empty range `[p, p + n)`, as a list (none for `n = 0`). -/
def range0 (p n : Nat) : List (Nat × Nat) := if n = 0 then [] else [(p, p + n)]

/-- The total length of the strings `xs`. -/
def strsLen (xs : List (Nat × Nat)) : Nat := (xs.map (·.2)).sum

/-- A string result: its bytes stay live. -/
def strKeep : List Nat → Memory → Nat → Nat → Nat → List (Nat × Nat) := fun _ _ r0 r1 _ => range0 r0 r1

def concatstringLive (k : Nat) : LiveSpec where
  cost a _ := roundupsize (strsLen (strPairs a 1 k)) true
  keep := strKeep

def concatstringsLive : LiveSpec where
  cost a m := roundupsize (strsLen (strHdrs m (arg a 1) (arg a 2))) true
  keep := strKeep

/-- A `[]byte` result `(r0, len, cap)` of `rawbyteslice` (the caller's buffer `buf` holds it when
one was passed and `len ≤ 32`): the array is fresh. -/
def bytesFresh (buf len r0 r2 : Nat) : List (Nat × Nat) :=
  if (buf = 0 ∨ 32 < len) ∧ 0 < len then range0 r0 r2 else []

def concatbyteLive (k : Nat) : LiveSpec where
  cost a _ := roundupsize (strsLen (strPairs a 1 k)) true
  fresh a _ r0 _ r2 := bytesFresh (arg a 0) (strsLen (strPairs a 1 k)) r0 r2

def concatbytesLive : LiveSpec where
  cost a m := roundupsize (strsLen (strHdrs m (arg a 1) (arg a 2))) true
  fresh a m r0 _ r2 := bytesFresh (arg a 0) (strsLen (strHdrs m (arg a 1) (arg a 2))) r0 r2

def slicebytetostringLive : LiveSpec where
  cost a _ := roundupsize (arg a 2) true
  keep := strKeep

/-- `slicebytetostringtmp` allocates nothing (its result is its operand). -/
def slicebytetostringtmpLive : LiveSpec := {}

def stringtoslicebyteLive : LiveSpec where
  cost a _ := roundupsize (arg a 2) true
  fresh a _ r0 _ r2 := bytesFresh (arg a 0) (arg a 2) r0 r2

/-- The bytes of the runes of the string in words `1, 2`. -/
def runesLen (a : List Nat) (m : Memory) : Nat := (runes (strBytes m (arg a 1) (arg a 2))).length

def stringtosliceruneLive : LiveSpec where
  cost a m := roundupsize (4 * runesLen a m) true
  fresh a m r0 _ _ := if (arg a 0 = 0 ∨ 32 < runesLen a m) ∧ 0 < runesLen a m then
    range0 r0 (roundupsize (4 * runesLen a m) true) else []

def slicerunetostringLive : LiveSpec where
  cost a m := roundupsize (encodeRunes (runeWords m (arg a 1) (arg a 2))).length true
  keep := strKeep

def intstringLive : LiveSpec where
  cost _ _ := 4
  keep := strKeep

/-- `decoderune` and `countrunes` allocate nothing. -/
def decoderuneLive : LiveSpec := {}
def countrunesLive : LiveSpec := {}

noncomputable def gostringLive : LiveSpec where
  cost a m := roundupsize (cstrLen m (arg a 0)) true
  keep := strKeep

def gostringnLive : LiveSpec where
  cost a _ := roundupsize (arg a 1) true
  keep := strKeep

def gobytesLive : LiveSpec where
  cost a _ := blockSize (arg a 1) true
  fresh a _ r0 _ _ := range0 r0 (arg a 1)

/-- `growslice` of any element type: the new array, `newCap · size` bytes. -/
def growsliceLive : LiveSpec where
  cost a m := roundupsize (nextslicecap (arg a 1) (arg a 2) * typSize m (arg a 4)) (typNoscan m (arg a 4))
  fresh a m r0 _ r2 := range0 r0 (r2 * typSize m (arg a 4))

def growsliceNoAliasLive : LiveSpec := growsliceLive

/-- `growsliceBuf`: as `growslice` when the result does not fit the caller's buffer. -/
def growsliceBufLive : LiveSpec where
  cost a m := if arg a 6 < arg a 1 then growsliceLive.cost a m else 0
  fresh a m r0 r1 r2 := if arg a 6 < arg a 1 then growsliceLive.fresh a m r0 r1 r2 else []

def growsliceBufNoAliasLive : LiveSpec := growsliceBufLive

def makeslicecopyLive : LiveSpec where
  cost a m := blockSize (arg a 1 * typSize m (arg a 0)) (typNoscan m (arg a 0))
  fresh a m r0 _ _ := range0 r0 (arg a 1 * typSize m (arg a 0))

def moveSliceLive : LiveSpec where
  cost a m := blockSize (arg a 3 * typSize m (arg a 0)) (typNoscan m (arg a 0))
  fresh a m r0 _ _ := range0 r0 (arg a 3 * typSize m (arg a 0))

def moveSliceNoScanLive : LiveSpec where
  cost a _ := blockSize (arg a 3 * arg a 0) true
  fresh a _ r0 _ _ := range0 r0 (arg a 3 * arg a 0)

def moveSliceNoCapLive : LiveSpec where
  cost a m := roundupsize (arg a 2 * typSize m (arg a 0)) false
  fresh a m r0 _ _ := if arg a 2 = 0 then [] else range0 r0 (roundupsize (arg a 2 * typSize m (arg a 0)) false)

def moveSliceNoCapNoScanLive : LiveSpec where
  cost a _ := roundupsize (arg a 2 * arg a 0) true
  fresh a _ r0 _ _ := if arg a 2 = 0 then [] else range0 r0 (roundupsize (arg a 2 * arg a 0) true)

/-- The copies and the bulk barriers allocate nothing. -/
def slicecopyLive : LiveSpec := {}
def typedslicecopyLive : LiveSpec := {}
def wbZeroLive : LiveSpec := {}
def wbMoveLive : LiveSpec := {}

/-- **`runtime.bulkBarrierPreWrite(dst, src, size, typ)`** (`mbitmap.go`): with the barrier on and
`dst` in the heap, appends the pointer slots of `dst` (and of `src`, when it is not nil) to the
P's write-barrier buffer; otherwise nothing. Runtime memory only; in both flag states. Words:
`dst, src, size, typ`. -/
def bulkBarrierPreWriteSpec : RtSpec where
  nargs := 4
  pre a m := Readable m (arg a 0) (arg a 2) ∧ (arg a 1 ≠ 0 → Readable m (arg a 1) (arg a 2)) ∧
    (arg a 3 ≠ 0 → TypeOK m (arg a 3))
  reads a _ := [(arg a 0, arg a 2), (arg a 1, if arg a 1 = 0 then 0 else arg a 2),
    (arg a 3, if arg a 3 = 0 then 0 else 16)]
  post _ _ _ _ _ _ _ := True

def bulkBarrierPreWriteLive : LiveSpec := {}

attribute [janus_exec, janus_post] mallocgcRound newobjectRound makesliceRound growsliceRound

attribute [janus_exec, janus_post, janus64_exec, janus64_post] range0 strKeep bytesFresh liveAdds
  concatstringLive concatstringsLive concatbyteLive concatbytesLive slicebytetostringLive
  slicebytetostringtmpLive stringtoslicebyteLive stringtosliceruneLive slicerunetostringLive
  intstringLive decoderuneLive countrunesLive gostringLive gostringnLive gobytesLive growsliceLive
  growsliceNoAliasLive growsliceBufLive growsliceBufNoAliasLive makeslicecopyLive moveSliceLive
  moveSliceNoScanLive moveSliceNoCapLive moveSliceNoCapNoScanLive slicecopyLive typedslicecopyLive
  wbZeroLive wbMoveLive bulkBarrierPreWriteSpec bulkBarrierPreWriteLive

/-! ## The single-call contracts follow from the live ones

A theorem proved against a round 9 contract (`NewobjectContract p addr R.rt stack H`, for every
`H`) holds under the live contract too: the live contract implies the single-call one for the
readiness predicate `liveReady R.rt (LiveCall …)`, which holds at a call when, for **every** memory
the runtime sees as it does, the stack check falls through and the live part of the
precondition holds for some live set and budget (`NewobjectLiveContract.ready`, …). So simple
single-allocation proofs keep their short form (`H` at the entry, `janus_run calls [h]`). -/

/-- The readiness a live contract gives a single call: `P args g sp m` for every memory `m` the
runtime sees as `v` (a function of what a readiness predicate sees, by construction). -/
def liveReady (rt : List (Nat × Nat)) (P : List Nat → Nat → Nat → Memory → Prop) : RtReady :=
  fun args g sp v => ∀ m, rtView rt m = v → P args g sp m

/-- The window `[sp - stack, sp - 8) ∪ [sp + 8, sp + 8 + 8·nargs)` of `calleeStack`, from `SP`. -/
@[reducible] def windowAt (sp stack nargs : Nat) : List (Nat × Nat) :=
  [(sp - stack, sp - 8), (sp + 8, sp + 8 + 8 * nargs)]

/-- The runtime's stack check and the live part of a call's precondition (arm64), from its
arguments, `g`, `SP` and memory, for some live set and budget. -/
def LiveCall (R : RtInv) (addr stack nargs : Nat)
    (cost : List Nat → Memory → Nat) (args : List Nat) (g sp : Nat) (m : Memory) : Prop :=
  (g + 24 ≤ 2 ^ 48 ∧ m.accessible (g + 16) 8 false = true ∧ m.readLE (g + 16) 8 + stack < sp ∧
    Outside (g + 16) 8 (windowAt sp stack nargs)) ∧
  ∃ L b, LiveAt R addr args L b (cost args m) g m (windowAt sp stack nargs)

/-- A family of summaries, one per live set and budget, gives every summary whose precondition
picks one and whose postcondition follows from that one's. -/
theorem Summary.of_live {p : Program} {addr : Nat} {pre : State → Prop} {post : State → State → Prop}
    {α β : Type} {lpre : α → β → State → Prop} {lpost : α → β → State → State → Prop}
    (h : ∀ a b, Summary p addr (lpre a b) (lpost a b)) (hpre : ∀ s, pre s → ∃ a b, lpre a b s)
    (hpost : ∀ a b s s', lpre a b s → lpost a b s s' → post s s') : Summary p addr pre post := by
  intro s hpc hp
  obtain ⟨a, b, hl⟩ := hpre s hp
  obtain ⟨k, s', hst, hr, hq⟩ := h a b s hpc hl
  exact ⟨k, s', hst, hr, hpost a b s s' hl hq⟩

/-- As `Summary.of_live`, with the choice of the family member made together with the
postcondition's consequence (for a caller-side choice such as the empty live set). -/
theorem Summary.of_live' {p : Program} {addr : Nat} {pre : State → Prop} {post : State → State → Prop}
    {α β : Type} {lpre : α → β → State → Prop} {lpost : α → β → State → State → Prop}
    (h : ∀ a b, Summary p addr (lpre a b) (lpost a b))
    (hpre : ∀ s, pre s → ∃ a b, lpre a b s ∧ ∀ s', lpost a b s s' → post s s') : Summary p addr pre post := by
  intro s hpc hp
  obtain ⟨a, b, hl, hq⟩ := hpre s hp
  obtain ⟨k, s', hst, hr, hq'⟩ := h a b s hpc hl
  exact ⟨k, s', hst, hr, hq s' hq'⟩

/-- The costs of the allocation contracts, from the argument words and the memory. -/
def mallocgcCost (a : List Nat) (m : Memory) : Nat := blockSize (arg a 0) (arg a 1 == 0 || typNoscan m (arg a 1))
def newobjectCost (a : List Nat) (m : Memory) : Nat := blockSize (typSize m (arg a 0)) (typNoscan m (arg a 0))
def makesliceCost (a : List Nat) (m : Memory) : Nat :=
  blockSize (typSize m (arg a 0) * arg a 2) (typNoscan m (arg a 0))
def growsliceCost (a : List Nat) (_ : Memory) : Nat := 8 * growCap8 (arg a 1) (arg a 2)

theorem MallocgcLiveContract.ready {p : Program} {addr : Nat} {stack : Nat}
    {R : RtInv} (h : MallocgcLiveContract p addr stack R) :
    MallocgcContract p addr R.rt stack (liveReady R.rt (LiveCall R addr stack 3 mallocgcCost)) :=
  Summary.of_live h (fun s ⟨hpre, hH⟩ => by
      obtain ⟨⟨g1, g2, g3, g4⟩, L, b, hl⟩ := hH s.mem rfl
      exact ⟨L, b, hpre, ⟨⟨g1, g2, g3⟩, g4⟩, hl⟩)
    (fun _ _ _ _ _ ⟨ptr, j, f, v, m, ex, ep, h1, h2, _, h4, _⟩ =>
      ⟨ptr, j, f, v, m, ex, ep, h1, h2, fun hp => (h4 hp).1⟩)

theorem NewobjectLiveContract.ready {p : Program} {addr : Nat} {stack : Nat}
    {R : RtInv} (h : NewobjectLiveContract p addr stack R) :
    NewobjectContract p addr R.rt stack (liveReady R.rt (LiveCall R addr stack 1 newobjectCost)) :=
  Summary.of_live h (fun s ⟨hpre, hH⟩ => by
      obtain ⟨⟨g1, g2, g3, g4⟩, L, b, hl⟩ := hH s.mem rfl
      exact ⟨L, b, hpre, ⟨⟨g1, g2, g3⟩, g4⟩, hl⟩)
    (fun _ _ _ _ _ ⟨ptr, j, f, v, m, ex, ep, h1, h2, _, h4, _⟩ =>
      ⟨ptr, j, f, v, m, ex, ep, h1, h2, fun hp => (h4 hp).1⟩)

theorem MakesliceLiveContract.ready {p : Program} {addr : Nat} {stack : Nat}
    {R : RtInv} (h : MakesliceLiveContract p addr stack R) :
    MakesliceContract p addr R.rt stack (liveReady R.rt (LiveCall R addr stack 3 makesliceCost)) :=
  Summary.of_live h (fun s ⟨hpre, hH⟩ => by
      obtain ⟨⟨g1, g2, g3, g4⟩, L, b, hl⟩ := hH s.mem rfl
      exact ⟨L, b, hpre, ⟨⟨g1, g2, g3⟩, g4⟩, hl⟩)
    (fun _ _ _ _ _ ⟨ptr, j, f, v, m, ex, ep, h1, h2, _, h4, _⟩ =>
      ⟨ptr, j, f, v, m, ex, ep, h1, h2, fun hp => (h4 hp).1⟩)

theorem GrowsliceLiveContract.ready {p : Program} {addr : Nat} {stack : Nat}
    {R : RtInv} (h : GrowsliceLiveContract p addr stack R) :
    GrowsliceContract p addr R.rt stack (liveReady R.rt (LiveCall R addr stack 5 growsliceCost)) :=
  Summary.of_live h (fun s ⟨hpre, hH⟩ => by
      obtain ⟨⟨g1, g2, g3, g4⟩, L, b, hl⟩ := hH s.mem rfl
      exact ⟨L, b, hpre, ⟨⟨g1, g2, g3⟩, g4⟩, hl⟩)
    (fun _ _ _ _ _ ⟨ptr, j, f, v, m, ex, ep, h1, h2, _, h4, _⟩ =>
      ⟨ptr, j, f, v, m, ex, ep, h1, h2, h4.1⟩)

/-- The live part of a write barrier's precondition (arm64). -/
def LiveCallWb (R : RtInv) (addr stack : Nat) (args : List Nat) (g sp : Nat)
    (m : Memory) : Prop :=
  ∃ L b, R.ok addr args ∧ R.inv b L g (view R.rt L m) ∧ LiveSep L [(sp - stack, sp - 8)] ∧
    LiveSep [(sp - stack, sp - 8)] R.rt

theorem WbLiveContract.ready {p : Program} {addr : Nat} {stack : Nat}
    {R : RtInv} {n : Nat} (h : WbLiveContract p addr stack R n) :
    WbContract p addr R.rt stack (liveReady R.rt (LiveCallWb R addr stack)) n :=
  Summary.of_live h (fun s ⟨hc, hH⟩ => by
      obtain ⟨L, b, hl⟩ := hH s.mem rfl
      exact ⟨L, b, hc, hl⟩)
    (fun _ _ _ _ _ ⟨buf, j, f, v, m, ex, ep, h1, h2, _, h4, _⟩ => ⟨buf, j, f, v, m, ex, ep, h1, h2, h4⟩)

/-- The live part of an `RtSpec` call's precondition (arm64). -/
def LiveCallRt (R : RtInv) (addr stack : Nat) (sp : RtSpec) (ls : LiveSpec) :
    List Nat → Nat → Nat → Memory → Prop :=
  LiveCall R addr stack sp.nargs ls.cost

theorem RtLiveContract.ready {p : Program} {addr : Nat} {stack : Nat}
    {R : RtInv} {sp : RtSpec} {ls : LiveSpec} (h : RtLiveContract p addr stack R sp ls)
    (hr : sp.ready = true) :
    RtContract p addr R.rt stack (liveReady R.rt (LiveCallRt R addr stack sp ls)) sp :=
  Summary.of_live h (fun s ⟨hc, hpre, hreads, hg, hH⟩ => by
      obtain ⟨⟨g1, g2, g3, g4⟩, L, b, hl⟩ := ready_of hr hH s.mem rfl
      exact ⟨L, b, hc, hpre, hreads, hg, ⟨⟨g1, g2, g3⟩, g4⟩, hl⟩)
    (fun _ _ _ _ _ ⟨r0, r1, r2, j, f, v, m, ex, ep, h1, h2, h3, _⟩ =>
      ⟨r0, r1, r2, j, f, v, m, ex, ep, h1, h2, h3⟩)

/-! ### The `MemModel` contracts as derived lemmas

`MemModel.ofRt R` is the round 10 model of the live runtime `R`: its private memory is `R.rt` and
the environment holds when the invariant holds for the empty live set and some budget. The legacy
contracts over it (`Mem.Memmove`, …) are NOT derived from the live ones: they state `excl` and
`exclPass` unchanged and the barrier off, which a contract that leaves them unspecified (the
arm64 rule) cannot imply. The live family replaces them for new proofs. -/

open Janus.Spec.Map in
/-- The `MemModel` of a live runtime. -/
def MemModel.ofRt (R : RtInv) : Mem.MemModel where
  Env m g := ∃ b, R.inv b [] g.toNat (view R.rt [] m)
  priv := R.rt

open Janus.Spec.Map in
theorem MemModel.ofRt_laws (R : RtInv) : (MemModel.ofRt R).Laws where
  env_frame m m' g := fun ⟨b, hb⟩ hag => ⟨b, R.ext b [] g.toNat _ _ (fun a => by
    simp only [view]
    by_cases h : inRs R.rt a = true
    · have := hag.2 a (by
        simp only [inRs, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨r, hr, h1, h2⟩ := h
        exact ⟨r, hr, h1, by omega⟩)
      simp [h, this]
    · simp [h]) (fun a n w => by simp only [view_accessible]; exact hag.1 a n w) hb⟩

/-- The callee's window is outside `rt` when `[sp - d, sp + 8 + 8·nargs)` is. -/
theorem liveSep_win {rt : List (Nat × Nat)} {s : State} {d nargs : Nat}
    (h : Outside (s.sp.toNat - d) (d + 8 + 8 * nargs) rt) : LiveSep (calleeStack s d nargs) rt := by
  intro r hr
  simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.of_sub (by omega) (by omega)
  · exact h.of_sub (by omega) (by omega)

/-- A state is `retStateX` of the call state when it returns to `X30` with `SP`, `X18`, `X28`,
`X29`, the system registers and `FPSR` kept and the result registers as `res` (the converse of the
definition, for proofs that run a callee's code). -/
theorem retStateX_intro {s s' : State} {res : List W64} (hpc : s'.pc = s.regs 30) (hsp : s'.sp = s.sp)
    (h18 : s'.regs 18 = s.regs 18) (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29)
    (hdz : s'.dczid = s.dczid) (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr)
    (hfs : s'.fpsr = s.fpsr) (hres : ∀ i, i < res.length → s'.regs i = res.getD i 0) :
    ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat))
      (ep : Nat → Bool), s' = retStateX s junk res f v m ex ep := by
  refine ⟨s'.regs, s'.flags, s'.vregs, s'.mem, s'.excl, s'.exclPass, ?_⟩
  have hr : callRegs s.regs s'.regs res = s'.regs := by
    funext i
    simp only [callRegs]
    by_cases h : i = 18 ∨ i = 28 ∨ i = 29
    · rw [if_pos h]; rcases h with rfl | rfl | rfl <;> simp [h18, h28, h29]
    · rw [if_neg h]
      by_cases hi : i < res.length
      · have := hres i hi
        have e1 : res.getD i (s'.regs i) = res.getD i 0 := by
          simp [List.getD, List.getElem?_eq_getElem hi]
        rw [e1]; exact this.symm
      · simp [List.getD, List.getElem?_eq_none (by omega : res.length ≤ i)]
  cases s; cases s'
  simp only [retStateX] at *
  simp_all

/-- A sub-range of a range of `rs` is in `rs` (a sub-slice of a slab of the live set). -/
theorem InRanges.of_sub {a n b k : Nat} {rs : List (Nat × Nat)} (h : InRanges b k rs) (h1 : b ≤ a)
    (h2 : a + n ≤ b + k) : InRanges a n rs := h.sub h1 h2

/-! ## Removing objects from the live set

When the program gives objects back (`sync.Pool.Put`: the runtime may reuse them), they leave the
live set: `removeRanges L rs` drops every range of `rs` from `L`. A contract that gives objects
back states its invariant for the shrunk set and the view of the same memory:
`view R.rt (removeRanges L rs) m` agrees with `view R.rt L m` outside the removed ranges
(`view_removeRanges`), so what the runtime sees changes exactly where the objects were. -/

/-- `L` without the ranges `rs`. -/
def removeRanges (L rs : List (Nat × Nat)) : List (Nat × Nat) := L.filter fun r => r ∉ rs

@[simp] theorem removeRanges_nil (rs : List (Nat × Nat)) : removeRanges [] rs = [] := rfl
@[simp] theorem removeRanges_append (L L' rs : List (Nat × Nat)) :
    removeRanges (L ++ L') rs = removeRanges L rs ++ removeRanges L' rs := List.filter_append ..
theorem removeRanges_self (o : Nat × Nat) : removeRanges [o] [o] = [] := by simp [removeRanges]
theorem removeRanges_singleton_of_ne {o x : Nat × Nat} (h : x ≠ o) :
    removeRanges [x] [o] = [x] := by simp [removeRanges, h]
theorem removeRanges_of_notMem {L rs : List (Nat × Nat)} (h : ∀ r ∈ L, r ∉ rs) : removeRanges L rs = L :=
  List.filter_eq_self.2 fun r hr => by simpa using h r hr

/-- The shrunk live set is a sub-list of the old one. -/
theorem removeRanges_subset (L rs : List (Nat × Nat)) : ∀ r ∈ removeRanges L rs, r ∈ L :=
  fun r hr => (List.mem_filter.1 hr).1

/-- Outside the removed objects the two live sets mask the same bytes. -/
theorem inRs_removeRanges {L rs : List (Nat × Nat)} {a : Nat}
    (h : inRs (L.filter fun r => r ∈ rs) a = false) : inRs (removeRanges L rs) a = inRs L a := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h1
    obtain ⟨r, hr, h2⟩ := List.any_eq_true.1 h1
    exact List.any_eq_true.2 ⟨r, removeRanges_subset L rs r hr, h2⟩
  · intro h1
    obtain ⟨r, hr, h2⟩ := List.any_eq_true.1 h1
    by_cases hm : r ∈ rs
    · exfalso
      have := List.any_eq_false.1 h r (List.mem_filter.2 ⟨hr, by simpa using hm⟩)
      exact this h2
    · exact List.any_eq_true.2 ⟨r, List.mem_filter.2 ⟨hr, by simpa using hm⟩, h2⟩

/-- The view with objects given back agrees with the old view outside the removed ranges. -/
theorem view_removeRanges (rt L rs : List (Nat × Nat)) (m : Memory) (a : Nat)
    (h : inRs (L.filter fun r => r ∈ rs) a = false) :
    (view rt (removeRanges L rs) m).bytes a = (view rt L m).bytes a := by
  simp only [view, inRs_removeRanges h]

end Janus.Contracts
