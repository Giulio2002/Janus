import Lean
import Janus.Tactic.CarrySound
import Janus.Arm64.MemoryLemmas

/-!
# `janus_carry`: carry chains by reflection

`janus_carry` proves a goal `lhs = rhs` between natural-number terms built from atoms, `+`,
`*`, literals, `/ k`, `% k` (`k` a literal), truncated `-` and `(decide (k ≤ a)).toNat`, as
left by the symbolic execution of multi-limb arithmetic (see `Janus.Tactic.CarryDefs` for the
normal form). It also accepts a conjunction of such equations.

1. Both sides are reflected into `Janus.Carry.Tm` over a list of atoms (every other subterm:
   `x.toNat`, memory reads, variables, …).
2. Each atom gets the best upper bound it can find: `x.toNat < 2^w` for a `BitVec w`,
   `readLE m a n < 256^n`, `b.toNat ≤ 1`, and every hypothesis `atom ≤ c` / `atom < c` with a
   literal `c`.
3. The certificate (the quotient atoms `D_j = L_j / k_j` and the atom intervals) is computed
   by `Janus.Carry.build` at tactic time.
4. The proof is `check_sound env ubs tbl ivs a b hbounds hcheck`, where `hcheck :
   check ubs tbl ivs a b = true` is an auxiliary lemma proved by `Eq.refl true` (checked by
   kernel evaluation, like `decide +kernel`), and the conclusion `a.eval env = b.eval env` is
   the goal up to unfolding `Tm.eval`.

It fails (without changing the goal) if the goal has another shape or the normal forms do not
match; `janus_arith` then falls back to `omega`.
-/

namespace Janus.Carry

open Lean Meta Elab Tactic
open Janus.Ring

/-! ## Literals -/

/-- The value of a closed natural-number literal expression (`OfNat`, `+`, `*`, `^`, `-`, `/`,
`%` of literals). -/
partial def evalLit (e : Expr) : Option Nat :=
  match e.rawNatLit? with
  | some n => some n
  | none =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) => evalLit n
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return (← evalLit a) + (← evalLit b)
    | (``HMul.hMul, #[_, _, _, _, a, b]) => return (← evalLit a) * (← evalLit b)
    | (``HSub.hSub, #[_, _, _, _, a, b]) => return (← evalLit a) - (← evalLit b)
    | (``HDiv.hDiv, #[_, _, _, _, a, b]) => return (← evalLit a) / (← evalLit b)
    | (``HMod.hMod, #[_, _, _, _, a, b]) => return (← evalLit a) % (← evalLit b)
    | (``HPow.hPow, #[_, _, _, _, a, b]) => do
      let b ← evalLit b
      if b > 4096 then none else return (← evalLit a) ^ b
    | (``Nat.succ, #[a]) => return (← evalLit a) + 1
    | _ => none

def isNatTy (e : Expr) : Bool := e.isConstOf ``Nat

/-! ## Reflection -/

structure RState where
  atoms : Array Expr := #[]
  atomIdx : Std.HashMap Expr Nat := {}
  cache : Std.HashMap Expr (Expr × Tm) := {}

abbrev RM := StateT RState MetaM

def atomOf (e : Expr) : RM (Expr × Tm) := do
  let s ← get
  let i ← match s.atomIdx.get? e with
    | some i => pure i
    | none => do
      let i := s.atoms.size
      modify fun s => { s with atoms := s.atoms.push e, atomIdx := s.atomIdx.insert e i }
      pure i
  return (mkApp (mkConst ``Tm.var) (mkRawNatLit i), .var i)

/-- Reflect a natural-number term: the `Tm` expression and its value. -/
partial def reflect (e : Expr) : RM (Expr × Tm) := do
  if let some r := (← get).cache.get? e then return r
  let r ← go e
  modify fun s => { s with cache := s.cache.insert e r }
  return r
where
  go (e : Expr) : RM (Expr × Tm) := do
    if let some n := evalLit e then
      return (mkApp (mkConst ``Tm.lit) (mkRawNatLit n), .lit n)
    match e.getAppFnArgs with
    | (``HAdd.hAdd, #[t, _, _, _, a, b]) =>
      if isNatTy t then
        let (ea, ta) ← reflect a; let (eb, tb) ← reflect b
        return (mkApp2 (mkConst ``Tm.add) ea eb, .add ta tb)
    | (``HMul.hMul, #[t, _, _, _, a, b]) =>
      if isNatTy t then
        let (ea, ta) ← reflect a; let (eb, tb) ← reflect b
        return (mkApp2 (mkConst ``Tm.mul) ea eb, .mul ta tb)
    | (``HSub.hSub, #[t, _, _, _, a, b]) =>
      if isNatTy t then
        let (ea, ta) ← reflect a; let (eb, tb) ← reflect b
        return (mkApp2 (mkConst ``Tm.sub) ea eb, .sub ta tb)
    | (``HDiv.hDiv, #[t, _, _, _, a, k]) =>
      if isNatTy t then
        if let some k := evalLit k then
          if k > 0 then
            let (ea, ta) ← reflect a
            return (mkApp2 (mkConst ``Tm.div) ea (mkRawNatLit k), .div ta k)
    | (``HMod.hMod, #[t, _, _, _, a, k]) =>
      if isNatTy t then
        if let some k := evalLit k then
          if k > 0 then
            let (ea, ta) ← reflect a
            return (mkApp2 (mkConst ``Tm.mod) ea (mkRawNatLit k), .mod ta k)
    | (``Bool.toNat, #[d]) =>
      if let (``Decidable.decide, #[p, _]) := d.getAppFnArgs then
        let ka? := match p.getAppFnArgs with
          | (``LE.le, #[t, _, k, a]) => if isNatTy t then some (k, a) else none
          | (``GE.ge, #[t, _, a, k]) => if isNatTy t then some (k, a) else none
          | _ => none
        if let some (k, a) := ka? then
          if let some k := evalLit k then
            let (ea, ta) ← reflect a
            return (mkApp2 (mkConst ``Tm.geb) ea (mkRawNatLit k), .geb ta k)
    | _ => pure ()
    atomOf e

/-! ## Bounds of atoms -/

theorem le_of_lt_lit {a b : Nat} (u : Nat) (h : a < b) (hb : b = u + 1) : a ≤ u := by omega

/-- `e ≤ u` from `h : e < b` with `b` a literal expression of value `u + 1`. -/
def leOfLt (e b h : Expr) (u : Nat) : Expr :=
  mkApp5 (mkConst ``le_of_lt_lit) e b (mkRawNatLit u) h
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) b)

theorem le_lit {a b : Nat} (u : Nat) (h : a ≤ b) (hb : b = u) : a ≤ u := hb ▸ h

def leLit (e b h : Expr) (u : Nat) : Expr :=
  mkApp5 (mkConst ``le_lit) e b (mkRawNatLit u) h (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) b)

/-- Upper bounds from the hypotheses: `atom ↦ (u, proof of atom ≤ u)`. -/
def hypBounds : MetaM (Std.HashMap Expr (Nat × Expr)) := do
  let mut m : Std.HashMap Expr (Nat × Expr) := {}
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let ty := ty.cleanupAnnotations
    let cand : Option (Expr × Nat × Expr) :=
      match ty.getAppFnArgs with
      | (``LE.le, #[t, _, a, b]) =>
        if isNatTy t then (evalLit b).map fun u => (a, u, leLit a b d.toExpr u) else none
      | (``LT.lt, #[t, _, a, b]) =>
        if isNatTy t then (evalLit b).bind fun u =>
          if u = 0 then none else some (a, u - 1, leOfLt a b d.toExpr (u - 1)) else none
      | _ => none
    if let some (a, u, pf) := cand then
      match m.get? a with
      | some (u', _) => if u < u' then m := m.insert a (u, pf)
      | none => m := m.insert a (u, pf)
  return m

/-- The structural upper bound of an atom, if any. -/
def structBound (e : Expr) : MetaM (Option (Nat × Expr)) := do
  match e.getAppFnArgs with
  | (``BitVec.toNat, #[w, x]) =>
    let some w := evalLit w | return none
    if w > 4096 then return none
    let lt := mkApp2 (mkConst ``BitVec.isLt) (e.getArg! 0) x
    let some (_, _, _, bnd) := (← inferType lt).app4? ``LT.lt | return none
    return some (2 ^ w - 1, leOfLt e bnd lt (2 ^ w - 1))
  | (``Janus.Arm64.Memory.readLE, #[m, a, nE]) =>
    let some n := evalLit nE | return none
    if n > 512 then return none
    let lt := mkApp3 (mkConst ``Janus.Arm64.Memory.readLE_lt) m a nE
    let some (_, _, _, bnd) := (← inferType lt).app4? ``LT.lt | return none
    return some (256 ^ n - 1, leOfLt e bnd lt (256 ^ n - 1))
  | (``Bool.toNat, #[b]) => return some (1, mkApp (mkConst ``Bool.toNat_le) b)
  | _ => return none

/-! ## Expressions of certificate data -/

def intE (i : Int) : Expr :=
  match i with
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

def listE (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc) (mkApp (mkConst ``List.nil [0]) ty)

def prodE (α β : Expr) (a b : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [0, 0]) α β a b

def monoTy : Expr := mkApp (mkConst ``List [0]) (mkConst ``Nat)
def termTy : Expr := mkApp2 (mkConst ``Prod [0, 0]) monoTy (mkConst ``Int)
def polyTy : Expr := mkApp (mkConst ``List [0]) termTy

def polyE (p : Poly) : Expr :=
  listE termTy (p.map fun (m, c) =>
    prodE monoTy (mkConst ``Int) (listE (mkConst ``Nat) (m.map mkRawNatLit)) (intE c))

def optIntE : Option Int → Expr
  | some i => mkApp2 (mkConst ``Option.some [0]) (mkConst ``Int) (intE i)
  | none => mkApp (mkConst ``Option.none [0]) (mkConst ``Int)

def ivE (I : Iv) : Expr := mkApp2 (mkConst ``Iv.mk) (optIntE I.lo) (optIntE I.hi)

def tblE (t : List (Poly × Nat)) : Expr :=
  let ty := mkApp2 (mkConst ``Prod [0, 0]) polyTy (mkConst ``Nat)
  listE ty (t.map fun (L, k) => prodE polyTy (mkConst ``Nat) (polyE L) (mkRawNatLit k))

def ubsE (ubs : List (Option Nat)) : Expr :=
  let ty := mkApp (mkConst ``Option [0]) (mkConst ``Nat)
  listE ty (ubs.map fun
    | some u => mkApp2 (mkConst ``Option.some [0]) (mkConst ``Nat) (mkRawNatLit u)
    | none => mkApp (mkConst ``Option.none [0]) (mkConst ``Nat))

/-! ## The tactic -/

initialize registerTraceClass `janus.carry

register_option janus.carry.disch : Bool := {
  defValue := true
  descr := "use the carry-chain procedure in the dischargers at all" }

register_option janus.carry.dischProve : Bool := {
  defValue := true
  descr := "prove carry-chain side conditions in the dischargers (`janus_disch`, `janus64_disch`) \
    by reflection" }

register_option janus.carry.dischMaxNodes : Nat := {
  defValue := 64
  descr := "the largest side condition (in distinct subterms) the dischargers prove by \
    reflection; larger ones cost more kernel time than the simplification saves" }

/-- The relation of a goal: `=`, `≤` or `<` between natural numbers (`≥`, `>` swapped). -/
def goalRel? (t : Expr) : Option (Nat × Expr × Expr) :=
  match t.getAppFnArgs with
  | (``Eq, #[ty, a, b]) => if isNatTy ty then some (0, a, b) else none
  | (``LE.le, #[ty, _, a, b]) => if isNatTy ty then some (1, a, b) else none
  | (``LT.lt, #[ty, _, a, b]) => if isNatTy ty then some (2, a, b) else none
  | (``GE.ge, #[ty, _, a, b]) => if isNatTy ty then some (1, b, a) else none
  | (``GT.gt, #[ty, _, a, b]) => if isNatTy ty then some (2, b, a) else none
  | _ => none

/-- Prove one goal `lhs = rhs`, `lhs ≤ rhs` or `lhs < rhs` (natural numbers). Returns `false`
(goal untouched) if the procedure does not apply. -/
def proveEq (g : MVarId) (maxNodes : Nat := 0) : MetaM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let t := t.cleanupAnnotations
  let some (rel, lhs, rhs) := goalRel? t | return false
  let t0 ← IO.monoMsNow
  let (((ea, ta), (eb, tb)), st) ← (do
      let a ← reflect lhs
      let b ← reflect rhs
      return (a, b) : RM _).run {}
  if maxNodes != 0 && st.cache.size > maxNodes then return false
  -- `a < b` is `a + 1 ≤ b`
  let (ea, ta) := if rel == 2 then
      (mkApp2 (mkConst ``Tm.add) ea (mkApp (mkConst ``Tm.lit) (mkRawNatLit 1)), Tm.add ta (.lit 1))
    else (ea, ta)
  let hyps ← hypBounds
  let mut bounds : Array (Option (Nat × Expr)) := #[]
  for e in st.atoms do
    let sb ← structBound e
    let hb := hyps.get? e
    let best := match sb, hb with
      | some (u, p), some (u', p') => if u' < u then some (u', p') else some (u, p)
      | some x, none => some x
      | none, some x => some x
      | none, none => none
    bounds := bounds.push best
  let ubs := bounds.toList.map (·.map (·.1))
  let (tbl, ivs) := build ubs [ta, tb]
  let ok := if rel == 0 then check ubs tbl ivs ta tb else checkLe ubs tbl ivs ta tb
  trace[janus.carry] "{st.atoms.size} atoms, {st.cache.size} nodes, {tbl.length} quotient atoms, accepted: {ok}, {(← IO.monoMsNow) - t0} ms"
  unless ok do
    if (← isTracingEnabledFor `janus.carry) then
      let c : Ctx := { n := ubs.length, tbl := tbl, ivs := ivs }
      match chk c ta, chk c tb with
      | some (p, I), some (q, J) =>
        let d := p.sub q
        trace[janus.carry] "lhs interval {repr (I.inter (polyIv (ivNth ivs) p)).lo} {repr (I.inter (polyIv (ivNth ivs) p)).hi}, rhs {repr (J.inter (polyIv (ivNth ivs) q)).lo} {repr (J.inter (polyIv (ivNth ivs) q)).hi}\ndifference ({d.length} terms, gcd {d.gcdCoeffs}): {repr d}\ntable: {repr tbl}"
      | _, _ => trace[janus.carry] "a side has no normal form"
    return false
  let envE := listE (mkConst ``Nat) st.atoms.toList
  let ubsX := ubsE ubs
  let tblX := tblE tbl
  let ivsX := listE (mkConst ``Iv) (ivs.map ivE)
  let (chkC, soundC) := if rel == 0 then (``check, ``check_sound) else (``checkLe, ``checkLe_sound)
  let chkTy ← mkEq (mkAppN (mkConst chkC) #[ubsX, tblX, ivsX, ea, eb]) (mkConst ``Bool.true)
  let val := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let t1 ← IO.monoMsNow
  let some name ← (try some <$> mkAuxLemma [] chkTy val catch e => do
      trace[janus.carry] "kernel check failed: {e.toMessageData}"; pure none) | return false
  trace[janus.carry] "kernel check: {(← IO.monoMsNow) - t1} ms"
  let pfB ← mkBoundsPf st.atoms.toList bounds.toList
  let pf := mkAppN (mkConst soundC) #[envE, ubsX, tblX, ivsX, ea, eb, pfB, mkConst name]
  -- stated with the goal as its type, so that `simp` accepts it as a discharger result at
  -- reducible transparency (the kernel checks that the two types agree)
  g.assign (← mkExpectedTypeHint pf (← g.getType))
  return true
where
  /-- `BoundsOK env ubs` proof with explicit `And.intro` types. -/
  mkBoundsPf : List Expr → List (Option (Nat × Expr)) → MetaM Expr
    | e :: es, some (u, pf) :: bs => do
      let rest ← mkBoundsPf es bs
      let restTy := mkApp2 (mkConst ``BoundsOK) (listE (mkConst ``Nat) es) (ubsE (bs.map (·.map (·.1))))
      let hd := mkApp4 (mkConst ``LE.le [0]) (mkConst ``Nat) (mkConst ``instLENat) e (mkRawNatLit u)
      return mkApp4 (mkConst ``And.intro) hd restTy pf rest
    | _ :: es, none :: bs => mkBoundsPf es bs
    | _, _ => return mkConst ``True.intro

/-- Does `e` contain a division or remainder by a literal, or a product of non-literals? (The
side conditions worth trying `janus_carry` on before `omega`.) -/
def hasCarryOps (e : Expr) : Bool :=
  (e.find? fun e =>
    match e.getAppFnArgs with
    | (``HDiv.hDiv, #[t, _, _, _, _, k]) => isNatTy t && (evalLit k).isSome
    | (``HMod.hMod, #[t, _, _, _, _, k]) => isNatTy t && (evalLit k).isSome
    | (``HMul.hMul, #[t, _, _, _, a, b]) => isNatTy t && (evalLit a).isNone && (evalLit b).isNone
    | _ => false).isSome

/-- The atoms `omega` would see in a natural-number term: the maximal subterms that are not
`+`, `-`, a product with a literal, `/`/`%` by a literal, or a literal. -/
partial def omegaAtoms (e : Expr) (acc : Array Expr) : Array Expr :=
  if (evalLit e).isSome then acc else
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) | (``HSub.hSub, #[_, _, _, _, a, b]) =>
    omegaAtoms b (omegaAtoms a acc)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    if (evalLit a).isSome then omegaAtoms b acc
    else if (evalLit b).isSome then omegaAtoms a acc
    else acc.push e
  | (``HDiv.hDiv, #[_, _, _, _, a, k]) | (``HMod.hMod, #[_, _, _, _, a, k]) =>
    if (evalLit k).isSome then omegaAtoms a acc else acc.push e
  | _ => acc.push e

/-- No hypothesis mentions an `omega` atom of `a` or `b` (`omegaAtoms`) other than a plain
variable's `toNat`: then `omega` knows nothing about them beyond their ranges, which
`janus_carry` used too, so a goal that `janus_carry` rejected is not worth an `omega` call. -/
def atomsUnconstrained (g : MVarId) (a b : Expr) : MetaM Bool := g.withContext do
  let atoms := omegaAtoms b (omegaAtoms a #[])
  -- products and memory reads only
  for e in atoms do
    unless e.isAppOf ``Janus.Arm64.Memory.readLE || e.isAppOf ``HMul.hMul do return false
  let set : Std.HashSet Expr := atoms.foldl (·.insert ·) {}
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    if (ty.find? set.contains).isSome then return false
  return true

/-- For dischargers: a `=`/`≤`/`<` goal about carry terms. `some true`: proved by
`janus_carry`; `some false`: rejected, and `omega` would not know more (`atomsUnconstrained`);
`none`: not such a goal, or `omega` may still succeed. -/
def dischCarry (g : MVarId) : MetaM (Option Bool) := do
  let t ← instantiateMVars (← g.getType)
  let some (_, a, b) := goalRel? t.cleanupAnnotations | return none
  unless janus.carry.disch.get (← getOptions) do return none
  unless hasCarryOps a || hasCarryOps b do return none
  let saved ← saveState
  try
    if janus.carry.dischProve.get (← getOptions) then
      if ← proveEq g (janus.carry.dischMaxNodes.get (← getOptions)) then return some true
    saved.restore
    if ← atomsUnconstrained g a b then return some false
    return none
  catch _ => saved.restore; return none

/-- Split conjunctions and prove every conjunct with `proveEq`; all or nothing. -/
partial def proveAll (g : MVarId) : MetaM Bool := g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  if let some (a, b) := t.and? then
    let ga ← mkFreshExprSyntheticOpaqueMVar a
    let gb ← mkFreshExprSyntheticOpaqueMVar b
    unless ← proveAll ga.mvarId! do return false
    unless ← proveAll gb.mvarId! do return false
    g.assign (mkApp4 (mkConst ``And.intro) a b ga gb)
    return true
  proveEq g

/-- Prove an equation or inequality (or a conjunction of them) of carry-chain arithmetic by
reflection. Fails, leaving the goal unchanged, if it does not apply. -/
elab "janus_carry" : tactic => do
  let g ← getMainGoal
  let saved ← saveState
  if ← proveAll g then replaceMainGoal []
  else
    saved.restore
    throwError "janus_carry: not a carry-chain equation it can prove"

/-- `janus_carry` on the main goal if it applies (`true`), otherwise nothing (`false`). -/
def tryCarry : TacticM Bool := do
  let some g := (← getUnsolvedGoals).head? | return false
  let saved ← saveState
  let ok ← try proveAll g catch _ => pure false
  if ok then
    replaceMainGoal []
    return true
  saved.restore
  return false

end Janus.Carry
