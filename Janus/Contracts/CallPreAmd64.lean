import Janus.Contracts.InternalCallAmd64
import Janus.Contracts.CallPre

/-!
# Closing the precondition of an internal callee's summary (`janus64_callpre`, amd64)

The amd64 twin of `Janus.Contracts.CallPre`: `DataLoaded` across the caller's stores (`DataLoaded.writeLE`),
`RetAddr ((P.onlySegments names).link impl) ret` for a return site inside the extraction
(`RetAddr.of_placement64`, from the layout hypothesis `(P.segments ++ impl).Pairwise Segment.Apart`) and the
closed-definition arithmetic (`callPreNatCmp`). Declared as `janus64_callpre` in `Janus.Amd64.Tactic`, used by the
call-site closer of `janus64_run`; every result is a term the kernel checks.
-/

namespace Janus.Amd64

open Lean Meta Elab Tactic Janus.Amd64.GoABI

theorem Program.DataLoaded.of_data_eq {p q : Program} {m : Memory} (h : p.data = q.data)
    (hd : p.DataLoaded m) : q.DataLoaded m := by
  unfold Program.DataLoaded at *
  rw [← h]; exact hd

/-- A store into a writable range keeps the read-only data loaded. -/
theorem Program.DataLoaded.writeLE {p : Program} {m : Memory} (h : p.DataLoaded m) {a n v : Nat}
    (hw : m.accessible a n true = true) : p.DataLoaded (m.writeLE a n v) := by
  intro d hd
  obtain ⟨hreg, hb⟩ := h d hd
  refine ⟨?_, ?_⟩
  · simpa only [Janus.Arm64.Memory.regions_writeLE] using hreg
  · intro i hi
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    have hdis := Janus.Amd64.Tactic.disjoint_of_dataLoaded h k hk hw
    have hbo := @Janus.Arm64.Memory.bytes_writeLE_outside m a n v (p.data[k].base + i) (by omega)
    rw [hbo]
    exact hb i hi

theorem RetAddr.of_placement64 {P : Program} {names : List String} {impl : List Segment} {ret : Nat}
    (hu : ret < 2 ^ 47)
    (hcode : ∃ seg ∈ P.segments, seg.base ≤ ret ∧ ret < seg.base + seg.bytes.length)
    (hd : (P.segments ++ impl).Pairwise Segment.Apart)
    (hown : ∀ seg ∈ P.segments, names.contains seg.name = true →
      ret < seg.base ∨ seg.base + seg.bytes.length ≤ ret)
    (hst : ∀ st ∈ P.stubs, st.addr ≠ ret) : RetAddr ((P.onlySegments names).link impl) ret := by
  refine ⟨hu, ?_, hst⟩
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

private partial def findPairwise64 (pf ty : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  if ty.isAppOfArity ``List.Pairwise 3 then
    if (ty.getArg! 1).isConstOf ``Segment.Apart then return some pf
    return none
  if ty.isAppOfArity ``And 2 then
    if let some r ← findPairwise64 (← mkAppM ``And.left #[pf]) (ty.getArg! 0) fuel then return some r
    return ← findPairwise64 (← mkAppM ``And.right #[pf]) (ty.getArg! 1) fuel
  if fuel > 0 then
    if let some ty' ← unfoldDefinition? ty then return ← findPairwise64 pf ty' (fuel - 1)
  return none

private def dataBase64 (g : MVarId) (p m : Expr) : TacticM Bool := g.withContext do
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

private partial def proveDataLoaded64 (g : MVarId) (p m : Expr) (fuel : Nat) : TacticM Unit := g.withContext do
  if ← dataBase64 g p m then return
  unless fuel > 0 do throwError "janus64_callpre: too many stores"
  let m ← whnfR m
  let (``Janus.Arm64.Memory.writeLE, #[m', a, n, v]) := m.getAppFnArgs |
    throwError "janus64_callpre: no `DataLoaded` hypothesis about the memory{indentExpr m}"
  let hdl ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Program.DataLoaded) p m')
  let acc ← mkAppM ``Janus.Arm64.Memory.accessible #[m', a, n, mkConst ``Bool.true]
  let hacc ← mkFreshExprSyntheticOpaqueMVar (← mkEq acc (mkConst ``Bool.true))
  g.assign (mkAppN (mkConst ``Program.DataLoaded.writeLE) #[p, m', hdl, a, n, v, hacc])
  proveDataLoaded64 hdl.mvarId! p m' (fuel - 1)
  setGoals [hacc.mvarId!]
  evalTactic (← `(tactic| first | with_reducible assumption | janus64_disch))

private def proveRetAddr64 (g : MVarId) (p0 : Expr) : TacticM Unit := g.withContext do
  let p0 ← whnfR p0
  let (``Program.link, #[pn, impl]) := p0.getAppFnArgs |
    throwError "janus64_callpre: the callee's program is not `(P.onlySegments names).link impl`"
  let (``Program.onlySegments, #[P, _]) := pn.getAppFnArgs |
    throwError "janus64_callpre: the callee's program is not `(P.onlySegments names).link impl`"
  let segs := mkApp (mkConst ``Program.segments) P
  let want ← mkAppM ``List.Pairwise #[mkConst ``Segment.Apart, ← mkAppM ``HAppend.hAppend #[segs, impl]]
  let mut hd? : Option Expr := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some pf ← findPairwise64 d.toExpr d.type 4 then
      if ← isDefEq (← inferType pf) want then
        hd? := some pf
        break
  let some hd := hd? |
    throwError "janus64_callpre: no hypothesis `(P.segments ++ impl).Pairwise Segment.Apart` in the context"
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``RetAddr.of_placement64)
  for g' in gs do
    let t ← instantiateMVars (← g'.getType)
    if t.isAppOfArity ``List.Pairwise 3 then
      g'.assign hd
    else
      setGoals [g']
      evalTactic (← `(tactic| decide))

elab_rules : tactic | `(tactic| janus64_callpre) => withMainContext do
  let g ← getMainGoal
  let rest := (← getGoals).tail
  let t ← whnfR (← instantiateMVars (← g.getType))
  match t.getAppFnArgs with
  | (``Program.DataLoaded, #[p, m]) =>
    proveDataLoaded64 g p m 64
    setGoals rest
  | (``RetAddr, #[p0, _]) =>
    proveRetAddr64 g p0
    setGoals rest
  | _ =>
    Janus.callPreNatCmp g t
    setGoals rest

end Janus.Amd64
