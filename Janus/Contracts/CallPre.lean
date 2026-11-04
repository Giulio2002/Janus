import Janus.Contracts.InternalCall

/-!
# Closing the precondition of an internal callee's summary (`janus_callpre`, arm64)

`janus_run … calls [S]` with `S := Ensures.toSummaryIn …` has to prove `RetAddr p0 X30 ∧ ArgsFrom ∧ pre`
at the call. Two parts of that are determined by the layout of the extraction and need no user fact beyond the
usual well-formedness of the runtime stand-in:

* **`p.DataLoaded m'` for the memory `m'` after the caller's stores.** The stores are into a writable range
  (`m.accessible a n true`), and read-only data is disjoint from every writable range
  (`disjoint_of_dataLoaded`), so `DataLoaded` survives a store (`DataLoaded.writeLE`); the base is a
  `DataLoaded` hypothesis about the memory at the entry of the function (for the same data: `of_data_eq`).
* **`RetAddr ((P.onlySegments names).link impl) ret`** for the return site `ret` inside the extraction `P`:
  aligned, below `2^48`, not in the callee's own segments, not a stub address (all decidable on the concrete
  extraction), and not in a segment of `impl`, which follows from the hypothesis
  `(P.segments ++ impl).Pairwise Segment.Apart` that `codeIn_restrict` needs anyway (`RetAddr.of_placement`).

`janus_callpre` (declared in `Janus.Tactic.Common`, used by the call-site closer of `janus_run`) proves these
two goal shapes and fails on every other goal. It only builds terms from the lemmas below; the kernel checks
them like any other proof.
-/

namespace Janus

open Lean Meta Elab Tactic Janus.Arm64 Janus.GoABI

theorem Program.DataLoaded.of_data_eq {p q : Program} {m : Arm64.Memory} (h : p.data = q.data)
    (hd : p.DataLoaded m) : q.DataLoaded m := by
  unfold Program.DataLoaded at *
  rw [← h]; exact hd

/-- A store into a writable range keeps the read-only data loaded. -/
theorem Program.DataLoaded.writeLE {p : Program} {m : Arm64.Memory} (h : p.DataLoaded m) {a n v : Nat}
    (hw : m.accessible a n true = true) : p.DataLoaded (m.writeLE a n v) := by
  intro d hd
  obtain ⟨hreg, hb⟩ := h d hd
  refine ⟨?_, ?_⟩
  · simpa only [Arm64.Memory.regions_writeLE] using hreg
  · intro i hi
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    have hdis := Janus.Tactic.disjoint_of_dataLoaded h k hk hw
    have hbo := @Arm64.Memory.bytes_writeLE_outside m a n v (p.data[k].base + i) (by omega)
    rw [hbo]
    exact hb i hi

/-- The return site `ret` of a call from the extraction `P` into the callee `(P.onlySegments names).link impl`
is an admissible return address of the callee's program: `ret` is aligned, below `2^48`, inside a segment of `P`,
not in a kept segment, not a stub, and (by the layout hypothesis) not in any segment of `impl`. -/
theorem RetAddr.of_placement {P : Program} {names : List String} {impl : List Segment} {ret : Nat}
    (hal : ret % 4 = 0) (hu : ret < 2 ^ 48)
    (hcode : ∃ seg ∈ P.segments, seg.base ≤ ret ∧ ret < seg.base + 4 * seg.words.length)
    (hd : (P.segments ++ impl).Pairwise Segment.Apart)
    (hown : ∀ seg ∈ P.segments, names.contains seg.name = true →
      ret < seg.base ∨ seg.base + 4 * seg.words.length ≤ ret)
    (hst : ∀ st ∈ P.stubs, st.addr ≠ ret) : RetAddr ((P.onlySegments names).link impl) ret := by
  refine ⟨hal, hu, ?_, hst⟩
  intro seg hs
  have hs' : seg ∈ P.segments.filter (fun s => names.contains s.name) ++ impl := hs
  rcases List.mem_append.1 hs' with h | h
  · obtain ⟨hm, hn⟩ := List.mem_filter.1 h
    exact hown seg hm hn
  · obtain ⟨s0, hm0, hb, he⟩ := hcode
    have := List.pairwise_append.1 hd
    have ha := this.2.2 s0 hm0 seg h
    unfold Segment.Apart at ha
    omega

/-! ### The tactic -/

private partial def findPairwise (pf ty : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  if ty.isAppOfArity ``List.Pairwise 3 then
    if (ty.getArg! 1).isConstOf ``Segment.Apart then return some pf
    return none
  if ty.isAppOfArity ``And 2 then
    if let some r ← findPairwise (← mkAppM ``And.left #[pf]) (ty.getArg! 0) fuel then return some r
    return ← findPairwise (← mkAppM ``And.right #[pf]) (ty.getArg! 1) fuel
  if fuel > 0 then
    if let some ty' ← unfoldDefinition? ty then return ← findPairwise pf ty' (fuel - 1)
  return none

private def dataBase (g : MVarId) (p m : Expr) : TacticM Bool := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let (``Program.DataLoaded, #[q, m']) := ty.getAppFnArgs | continue
    unless ← isDefEq m' m do continue
    let dq := mkApp (mkConst ``Program.data) q
    let dp := mkApp (mkConst ``Program.data) p
    unless ← isDefEq dq dp do continue
    let heq ← mkExpectedTypeHint (← mkEqRefl dq) (← mkEq dq dp)
    g.assign (mkAppN (mkConst ``Program.DataLoaded.of_data_eq) #[q, p, m, heq, d.toExpr])
    return true
  return false

private partial def proveDataLoaded (g : MVarId) (p m : Expr) (fuel : Nat) : TacticM Unit := g.withContext do
  if ← dataBase g p m then return
  unless fuel > 0 do throwError "janus_callpre: too many stores"
  let m ← whnfR m
  let (``Arm64.Memory.writeLE, #[m', a, n, v]) := m.getAppFnArgs |
    throwError "janus_callpre: no `DataLoaded` hypothesis about the memory{indentExpr m}"
  let hdl ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Program.DataLoaded) p m')
  let acc ← mkAppM ``Arm64.Memory.accessible #[m', a, n, mkConst ``Bool.true]
  let hacc ← mkFreshExprSyntheticOpaqueMVar (← mkEq acc (mkConst ``Bool.true))
  g.assign (mkAppN (mkConst ``Program.DataLoaded.writeLE) #[p, m', hdl, a, n, v, hacc])
  proveDataLoaded hdl.mvarId! p m' (fuel - 1)
  setGoals [hacc.mvarId!]
  evalTactic (← `(tactic| first | with_reducible assumption | janus_disch))

private def proveRetAddr (g : MVarId) (p0 : Expr) : TacticM Unit := g.withContext do
  let p0 ← whnfR p0
  let (``Program.link, #[pn, impl]) := p0.getAppFnArgs |
    throwError "janus_callpre: the callee's program is not `(P.onlySegments names).link impl`"
  let (``Program.onlySegments, #[P, _]) := pn.getAppFnArgs |
    throwError "janus_callpre: the callee's program is not `(P.onlySegments names).link impl`"
  -- the layout hypothesis `(P.segments ++ impl).Pairwise Segment.Apart`
  let segs := mkApp (mkConst ``Program.segments) P
  let want ← mkAppM ``List.Pairwise #[mkConst ``Segment.Apart, ← mkAppM ``HAppend.hAppend #[segs, impl]]
  let mut hd? : Option Expr := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some pf ← findPairwise d.toExpr d.type 4 then
      if ← isDefEq (← inferType pf) want then
        hd? := some pf
        break
  let some hd := hd? |
    throwError "janus_callpre: no hypothesis `(P.segments ++ impl).Pairwise Segment.Apart` in the context"
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``RetAddr.of_placement)
  for g' in gs do
    let t ← instantiateMVars (← g'.getType)
    if t.isAppOfArity ``List.Pairwise 3 then
      g'.assign hd
    else
      setGoals [g']
      evalTactic (← `(tactic| decide))

/-- The maximal closed natural-number subterms of `e` that are applications of a definition other than the
arithmetic operators (`blockSize 32 false`), with their values by evaluation (`whnf`, kernel-checked by `rfl`). -/
partial def groundTerms (e : Expr) (acc : Array (Expr × Nat)) : MetaM (Array (Expr × Nat)) := do
  if e.hasFVar || e.hasMVar then
    match e with
    | .app f a => groundTerms a (← groundTerms f acc)
    | .forallE _ d b _ => groundTerms b (← groundTerms d acc)
    | .lam _ d b _ => groundTerms b (← groundTerms d acc)
    | .mdata _ b => groundTerms b acc
    | _ => return acc
  else
    let arith := [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``HPow.hPow, ``OfNat.ofNat,
      ``Nat.cast, ``Min.min, ``Max.max, ``Nat.succ]
    if e.isApp && !(e.getAppFn.constName?.any arith.contains) && e.getAppFn.isConst then
      let ty ← inferType e
      if ty.isConstOf ``Nat then
        let v ← whnfD e
        if let some n ← (try Meta.evalNat v catch _ => pure none) then
          unless acc.any (·.1 == e) do return acc.push (e, n)
          return acc
    match e with
    | .app f a => groundTerms a (← groundTerms f acc)
    | _ => return acc

/-- An arithmetic conjunct of a callee precondition whose context facts mention closed terms of definitions
(`blockSize 32 false`): `64 ≤ b` from `blockSize 32 false + blockSize 32 true ≤ b`. The closed terms are evaluated
(`whnf`, the equations `e = n` are `rfl` proofs the kernel re-checks) and `omega` runs on the natural-number
comparisons of the context alone (no disjunctions, no state facts). -/
def callPreNatCmp (g : MVarId) (t : Expr) : TacticM Unit := g.withContext do
  let isCmp (ty : Expr) : Bool :=
    (ty.isAppOfArity ``LE.le 4 || ty.isAppOfArity ``LT.lt 4 || ty.isAppOfArity ``Eq 3) && (ty.getArg! 0).isConstOf ``Nat
  unless isCmp t do throwError "janus_callpre: not a natural number comparison"
  let (terms, toClear) ← do
    let mut terms : Array (Expr × Nat) := #[]
    terms ← groundTerms t terms
    let mut toClear : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ← isProp ty do continue
      if isCmp ty then terms ← groundTerms ty terms else toClear := toClear.push d.fvarId
    pure (terms, toClear)
  if terms.isEmpty then throwError "janus_callpre: no closed definition application to evaluate"
  let mut g'' ← Janus.Tactic.Common.fastClear g toClear
  for (e, n) in terms do
    let eq ← mkEq e (mkNatLit n)
    let pf ← mkExpectedTypeHint (← mkEqRefl (mkNatLit n)) eq
    let (_, g3) ← (← g''.assert `hground eq pf).intro1P
    g'' := g3
  setGoals [g'']
  evalTactic (← `(tactic| omega))

elab_rules : tactic | `(tactic| janus_callpre) => withMainContext do
  let g ← getMainGoal
  let rest := (← getGoals).tail
  let t ← whnfR (← instantiateMVars (← g.getType))
  match t.getAppFnArgs with
  | (``Program.DataLoaded, #[p, m]) =>
    proveDataLoaded g p m 64
    setGoals rest
  | (``RetAddr, #[p0, _]) =>
    proveRetAddr g p0
    setGoals rest
  | _ =>
    callPreNatCmp g t
    setGoals rest

end Janus
