import Lean
import Janus.Tactic.AddrSolve

/-!
# The search side of `Janus.AddrSolve` (untrusted)

`solveGoal g` reflects the arithmetic facts of the local context of `g` (natural-number `≤ < = ≠`,
conjunctions, disjunctions, negations; `+`, multiplication by a literal, `-`, `min`, `max` through
auxiliary atoms with case facts) into `Janus.AddrSolve` data, searches for a refutation tree of the
negated goal (lazy case splitting with unit propagation; Fourier-Motzkin at the leaves), checks the
tree with the same computable `check` the kernel will evaluate, and closes `g` with
`Janus.AddrSolve.refute`. Any failure (unsupported shape, no refutation, budget) returns `false`
and leaves `g` untouched: callers fall back to `omega`.
-/

open Lean Meta Elab Tactic

namespace Janus.AddrSolve

deriving instance ToExpr for NE
deriving instance ToExpr for Tree

initialize registerTraceClass `janus.lin

namespace Tac

/-! ## Lemmas for the proof terms -/

theorem Sat.nil (env : List Nat) : Sat env [] := True.intro

theorem Sat.one (env : List Nat) (c : Con) (h : c.1.eval env ≤ c.2.eval env) : Sat env [c] :=
  ⟨h, True.intro⟩

theorem ASat.ofSat {env : List Nat} {a : List Con} (h : Sat env a) : ASat env [a] := Or.inl h

theorem ASat.left {env : List Nat} {a : Alts} (b : Alts) (h : ASat env a) : ASat env (a ++ b) := by
  induction a with
  | nil => exact h.elim
  | cons x a ih => rcases h with h | h; exact Or.inl h; exact Or.inr (ih h)

theorem ASat.right {env : List Nat} (a : Alts) {b : Alts} (h : ASat env b) : ASat env (a ++ b) := by
  induction a with
  | nil => exact h
  | cons x a ih => exact Or.inr ih

theorem not_or_elim (a b : Prop) (h : ¬(a ∨ b)) : ¬a ∧ ¬b := not_or.mp h
theorem not_and_elim (a b : Prop) (h : ¬(a ∧ b)) : ¬a ∨ ¬b := Classical.not_and_iff_not_or_not.mp h
theorem not_not_elim (a : Prop) (h : ¬¬a) : a := Classical.not_not.mp h

theorem min_cases (a b : Nat) :
    (a ≤ b ∧ min a b = a) ∨ (b < a ∧ min a b = b) := by
  by_cases h : a ≤ b
  · exact Or.inl ⟨h, Nat.min_eq_left h⟩
  · exact Or.inr ⟨Nat.lt_of_not_le h, Nat.min_eq_right (Nat.le_of_not_le h)⟩

theorem max_cases (a b : Nat) :
    (a ≤ b ∧ max a b = b) ∨ (b < a ∧ max a b = a) := by
  by_cases h : a ≤ b
  · exact Or.inl ⟨h, Nat.max_eq_right h⟩
  · exact Or.inr ⟨Nat.lt_of_not_le h, Nat.max_eq_left (Nat.le_of_not_le h)⟩

theorem sub_cases (a b : Nat) :
    (b ≤ a ∧ a - b + b = a) ∨ (a < b ∧ a - b = 0) := by
  by_cases h : b ≤ a
  · exact Or.inl ⟨h, Nat.sub_add_cancel h⟩
  · exact Or.inr ⟨Nat.lt_of_not_le h, Nat.sub_eq_zero_of_le (Nat.le_of_not_le h)⟩

/-! ## Reflection -/

/-- A reflected fact: a conjunction of constraints with a proof of `Sat env cons`, or a
disjunction of conjunctions with a proof of `ASat env alts`. Proofs mention the placeholder
environment `envPH`. -/
inductive Form where
  | conj (cons : List Con) (pf : Expr)
  | disj (alts : Alts) (pf : Expr)
deriving Inhabited

structure St where
  atoms : Array Expr := #[]
  /-- facts about auxiliary atoms: `(prop, proof)` still to be reflected -/
  pending : Array (Expr × Expr) := #[]

abbrev M := StateT St MetaM

def natTy : Expr := mkConst ``Nat

def envId : FVarId := ⟨`__envPH⟩
def envPH : Expr := mkFVar envId

def atomIdx (e : Expr) : M Nat := do
  let e ← instantiateMVars e
  let st ← get
  match st.atoms.findIdx? (· == e) with
  | some i => return i
  | none =>
    set { st with atoms := st.atoms.push e }
    return st.atoms.size

def numeral? (e : Expr) : Option Nat :=
  if let some n := e.nat? then some n
  else if let some n := e.rawNatLit? then some n
  else match e.getAppFnArgs with
    | (``HPow.hPow, #[_, _, _, _, a, b]) =>
      match a.nat?, b.nat? with
      | some x, some y => if y ≤ 128 then some (x ^ y) else none
      | _, _ => none
    | _ => none

def addPending (pf : Expr) : M Unit := do
  let ty ← inferType pf
  unless (← get).pending.any (·.1 == ty) do
    modify fun st => { st with pending := st.pending.push (ty, pf) }

partial def reify (e : Expr) : M NE := do
  let e := (← instantiateMVars e).consumeMData
  if let some n := numeral? e then return .lit n
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return .add (← reify a) (← reify b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    if let some k := numeral? a then return .mul k (← reify b)
    if let some k := numeral? b then return .mul k (← reify a)
    return .atom (← atomIdx e)
  | (``HSub.hSub, #[ty, _, _, _, a, b]) =>
    unless ty.isConstOf ``Nat do return .atom (← atomIdx e)
    let i ← atomIdx e
    addPending (mkAppN (mkConst ``sub_cases) #[a, b])
    discard <| reify a; discard <| reify b
    return .atom i
  | (``Min.min, #[ty, _, a, b]) =>
    unless ty.isConstOf ``Nat do return .atom (← atomIdx e)
    let i ← atomIdx e
    addPending (mkAppN (mkConst ``min_cases) #[a, b])
    discard <| reify a; discard <| reify b
    return .atom i
  | (``Max.max, #[ty, _, a, b]) =>
    unless ty.isConstOf ``Nat do return .atom (← atomIdx e)
    let i ← atomIdx e
    addPending (mkAppN (mkConst ``max_cases) #[a, b])
    discard <| reify a; discard <| reify b
    return .atom i
  | (``BitVec.toNat, #[w, x]) =>
    let i ← atomIdx e
    addPending (mkAppN (mkConst ``BitVec.isLt) #[w, x])
    return .atom i
  | _ => return .atom (← atomIdx e)

def mkLEn (a b : Expr) : Expr := mkApp4 (mkConst ``LE.le [0]) natTy (mkConst ``instLENat) a b

def satTy (cs : List Con) : Expr := mkApp2 (mkConst ``Sat) envPH (toExpr cs)
def asatTy (as : Alts) : Expr := mkApp2 (mkConst ``ASat) envPH (toExpr as)

def one (c : Con) (pf : Expr) : Form :=
  .conj [c] (mkAppN (mkConst ``Sat.one) #[envPH, toExpr c, pf])

def toAlts : Form → Alts × Expr
  | .conj cs pf => ([cs], mkAppN (mkConst ``ASat.ofSat) #[envPH, toExpr cs, pf])
  | .disj as pf => (as, pf)

/-- Reflect a proof `pf : p` of an arithmetic proposition. -/
partial def trans (p pf : Expr) : M (Option Form) := do
  let p := (← instantiateMVars p).consumeMData
  let isNat (i : Nat) := (p.getArg! i).isConstOf ``Nat
  if p.isAppOfArity ``LE.le 4 && isNat 0 then
    let a ← reify (p.getArg! 2); let b ← reify (p.getArg! 3)
    return some (one (a, b) pf)
  if p.isAppOfArity ``GE.ge 4 && isNat 0 then
    let a ← reify (p.getArg! 3); let b ← reify (p.getArg! 2)
    return some (one (a, b) pf)
  if p.isAppOfArity ``LT.lt 4 && isNat 0 then
    let a ← reify (p.getArg! 2); let b ← reify (p.getArg! 3)
    return some (one (.add a (.lit 1), b) pf)
  if p.isAppOfArity ``GT.gt 4 && isNat 0 then
    let a ← reify (p.getArg! 3); let b ← reify (p.getArg! 2)
    return some (one (.add a (.lit 1), b) pf)
  if p.isAppOfArity ``Eq 3 && isNat 0 then
    let x := p.getArg! 1; let y := p.getArg! 2
    let a ← reify x; let b ← reify y
    let p1 := mkApp3 (mkConst ``Nat.le_of_eq) x y pf
    let p2 := mkApp3 (mkConst ``Nat.le_of_eq) y x (mkApp4 (mkConst ``Eq.symm [1]) natTy x y pf)
    let s1 := mkAppN (mkConst ``Sat.one) #[envPH, toExpr (a, b), p1]
    let s2 := mkAppN (mkConst ``Sat.one) #[envPH, toExpr (b, a), p2]
    let s := mkAppN (mkConst ``Sat.append) #[envPH, toExpr [(a, b)], toExpr [(b, a)], s1, s2]
    return some (.conj [(a, b), (b, a)] s)
  if p.isAppOfArity ``Ne 3 && isNat 0 then
    let pr := mkApp3 (mkConst ``Nat.lt_or_gt_of_ne) (p.getArg! 1) (p.getArg! 2) pf
    return ← trans (← inferType pr) pr
  if p.isAppOfArity ``And 2 then
    let a := p.getArg! 0; let b := p.getArg! 1
    let some fa ← trans a (mkApp3 (mkConst ``And.left) a b pf) | return none
    let some fb ← trans b (mkApp3 (mkConst ``And.right) a b pf) | return none
    match fa, fb with
    | .conj ca sa, .conj cb sb =>
      return some (.conj (ca ++ cb)
        (mkAppN (mkConst ``Sat.append) #[envPH, toExpr ca, toExpr cb, sa, sb]))
    | _, _ => return none   -- a disjunction inside a conjunction: not reflected
  if p.isAppOfArity ``Or 2 then
    let a := p.getArg! 0; let b := p.getArg! 1
    -- the alternatives of each side (independent of the proof variable)
    let some (alts1, _) ← (withLocalDeclD `hp a fun hp => do
        let some f ← trans a hp | return none
        return some (toAlts f)) | return none
    let some (alts2, _) ← (withLocalDeclD `hq b fun hq => do
        let some f ← trans b hq | return none
        return some (toAlts f)) | return none
    let target := asatTy (alts1 ++ alts2)
    let l1 ← withLocalDeclD `hp a fun hp => do
      let some f ← trans a hp | throwError "unreachable"
      let (_, ap) := toAlts f
      mkLambdaFVars #[hp] (mkAppN (mkConst ``ASat.left) #[envPH, toExpr alts1, toExpr alts2, ap])
    let l2 ← withLocalDeclD `hq b fun hq => do
      let some f ← trans b hq | throwError "unreachable"
      let (_, ap) := toAlts f
      mkLambdaFVars #[hq] (mkAppN (mkConst ``ASat.right) #[envPH, toExpr alts1, toExpr alts2, ap])
    return some (.disj (alts1 ++ alts2)
      (mkAppN (mkConst ``Or.elim) #[a, b, target, pf, l1, l2]))
  if p.isAppOfArity ``Not 1 then
    let q := p.getArg! 0
    let q := q.consumeMData
    let isNatQ (i : Nat) := (q.getArg! i).isConstOf ``Nat
    if q.isAppOfArity ``LE.le 4 && isNatQ 0 then
      let pr := mkApp3 (mkConst ``Nat.lt_of_not_le) (q.getArg! 2) (q.getArg! 3) pf
      return ← trans (← inferType pr) pr
    if q.isAppOfArity ``LT.lt 4 && isNatQ 0 then
      let pr := mkApp3 (mkConst ``Nat.le_of_not_lt) (q.getArg! 2) (q.getArg! 3) pf
      return ← trans (← inferType pr) pr
    if q.isAppOfArity ``GE.ge 4 && isNatQ 0 then
      let pr := mkApp3 (mkConst ``Nat.lt_of_not_le) (q.getArg! 3) (q.getArg! 2) pf
      return ← trans (← inferType pr) pr
    if q.isAppOfArity ``GT.gt 4 && isNatQ 0 then
      let pr := mkApp3 (mkConst ``Nat.le_of_not_lt) (q.getArg! 3) (q.getArg! 2) pf
      return ← trans (← inferType pr) pr
    if q.isAppOfArity ``Eq 3 && isNatQ 0 then
      return ← trans (mkApp3 (mkConst ``Ne [1]) natTy (q.getArg! 1) (q.getArg! 2)) pf
    if q.isAppOfArity ``Or 2 then
      let pr := mkApp3 (mkConst ``not_or_elim) (q.getArg! 0) (q.getArg! 1) pf
      return ← trans (← inferType pr) pr
    if q.isAppOfArity ``And 2 then
      let pr := mkApp3 (mkConst ``not_and_elim) (q.getArg! 0) (q.getArg! 1) pf
      return ← trans (← inferType pr) pr
    if q.isAppOfArity ``Not 1 then
      let pr := mkApp2 (mkConst ``not_not_elim) (q.getArg! 0) pf
      return ← trans (← inferType pr) pr
  return none


/-! ## Search -/

structure Row where
  coef : Array Int
  k : Int
  mult : Array Nat

partial def linOf (nv : Nat) : NE → Array Int × Int
  | .atom i => ((Array.replicate nv (0 : Int)).set! i 1, 0)
  | .lit n => (Array.replicate nv (0 : Int), n)
  | .add a b =>
    let (ca, ka) := linOf nv a
    let (cb, kb) := linOf nv b
    (Array.zipWith (· + ·) ca cb, ka + kb)
  | .mul m a =>
    let (ca, ka) := linOf nv a
    (ca.map (m * ·), m * ka)

def Row.isContra (r : Row) : Bool := r.k < 0 && r.coef.all (· ≤ 0)

def Row.normalize (r : Row) : Row := Id.run do
  let mut g : Nat := r.k.natAbs
  for c in r.coef do g := Nat.gcd g c.natAbs
  for m in r.mult do g := Nat.gcd g m
  if g ≤ 1 then return r
  return { coef := r.coef.map (· / (g : Int)), k := r.k / (g : Int), mult := r.mult.map (· / g) }

/-- Fourier-Motzkin elimination with multiplier tracking. The result multipliers (one per pool
constraint) combine the constraints into a row whose variable part is pointwise `≤ 0` and whose
constant is negative (`farkas` accepts it: the atoms are naturals). -/
def fm (nv : Nat) (pool : Array Con) (limit : Nat := 300) : Option (Array Nat) := Id.run do
  let n := pool.size
  let mut rows : Array Row := #[]
  for i in [0:n] do
    let (cl, kl) := linOf nv pool[i]!.1
    let (cr, kr) := linOf nv pool[i]!.2
    rows := rows.push { coef := Array.zipWith (· - ·) cr cl, k := kr - kl,
                        mult := (Array.replicate n 0).set! i 1 }
  let mut fuel := nv + 2
  while fuel > 0 do
    fuel := fuel - 1
    for r in rows do
      if r.isContra then return some r.mult
    -- the variable with the cheapest elimination
    let mut best : Option (Nat × Nat) := none
    for j in [0:nv] do
      let mut np := 0; let mut nn := 0
      for r in rows do
        if r.coef[j]! > 0 then np := np + 1
        else if r.coef[j]! < 0 then nn := nn + 1
      if np + nn == 0 then continue
      let cost := np * nn + nn
      match best with
      | some (_, c) => if cost < c then best := some (j, cost)
      | none => best := some (j, cost)
    let some (j, _) := best | return none
    let mut out : Array Row := #[]
    let mut ps : Array Row := #[]
    let mut ns : Array Row := #[]
    for r in rows do
      if r.coef[j]! > 0 then ps := ps.push r
      else if r.coef[j]! < 0 then ns := ns.push r
      else out := out.push r
    -- `x_j ≥ 0` against a row with a negative coefficient: drop the term
    for r in ns do out := out.push { r with coef := r.coef.set! j 0 }
    for p in ps do
      for q in ns do
        let a : Int := p.coef[j]!
        let b : Int := -q.coef[j]!
        out := out.push (Row.normalize
          { coef := Array.zipWith (fun x y => b * x + a * y) p.coef q.coef,
            k := b * p.k + a * q.k,
            mult := Array.zipWith (fun x y => b.toNat * x + a.toNat * y) p.mult q.mult })
    -- dedupe: same variable part, keep the strongest constant
    let mut tbl : Std.HashMap (Array Int) Row := {}
    for r in out do
      match tbl[r.coef]? with
      | some r0 => if r.k < r0.k then tbl := tbl.insert r.coef r
      | none => tbl := tbl.insert r.coef r
    rows := tbl.fold (fun acc _ r => acc.push r) #[]
    if rows.size > limit then return none
  for r in rows do
    if r.isContra then return some r.mult
  return none

def tryFm (nv : Nat) (pool : Array Con) (budget : IO.Ref Nat) : IO (Option (Array Nat)) := do
  let b ← budget.get
  if b == 0 then return none
  budget.set (b - 1)
  return fm nv pool

partial def search (nv : Nat) (pool : Array Con) (ds : Array Alts) (used : Array Bool)
    (budget : IO.Ref Nat) : IO (Option Tree) := do
  if let some ms ← tryFm nv pool budget then return some (.leaf ms.toList)
  -- unit propagation
  for k in [0:ds.size] do
    if used[k]! then continue
    let alts := ds[k]!
    let mut results : Array (Option (Array Nat)) := #[]
    for a in alts do results := results.push (← tryFm nv (pool ++ a.toArray) budget)
    let survivors := (List.range alts.length).filter fun i => (results[i]!).isNone
    match survivors with
    | [] =>
      return some (.split k (results.toList.map fun r => .leaf (r.getD #[]).toList))
    | [idx] =>
      if alts.length > 1 then
        let some sub ← search nv (pool ++ alts[idx]!.toArray) ds (used.set! k true) budget
          | return none
        return some (.split k ((List.range alts.length).map fun i =>
          if i == idx then sub else .leaf ((results[i]!).getD #[]).toList))
    | _ => pure ()
  -- case split on the smallest unused disjunction(s)
  let mut cands0 : Array (Nat × Nat) := #[]
  for k in [0:ds.size] do
    if !used[k]! then cands0 := cands0.push (ds[k]!.length, k)
  let cands := cands0.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
  let mut tried := 0
  for (_, k) in cands do
    if tried ≥ 3 then break
    tried := tried + 1
    let alts := ds[k]!
    let mut ts : List Tree := []
    let mut ok := true
    for a in alts do
      match ← search nv (pool ++ a.toArray) ds (used.set! k true) budget with
      | some t => ts := ts ++ [t]
      | none => ok := false; break
    if ok then return some (.split k ts)
    if (← budget.get) == 0 then return none
  return none

/-! ## The tactic -/

def conAtoms : List Con → Array Nat := fun cs => Id.run do
  let mut out : Array Nat := #[]
  let rec go (e : NE) (acc : Array Nat) : Array Nat :=
    match e with
    | .atom i => if acc.contains i then acc else acc.push i
    | .lit _ => acc
    | .add a b => go b (go a acc)
    | .mul _ a => go a acc
  for (l, r) in cs do out := go r (go l out)
  return out

def formAtoms : Form → Array Nat
  | .conj cs _ => conAtoms cs
  | .disj as _ => Id.run do
    let mut out : Array Nat := #[]
    for a in as do
      for i in conAtoms a do
        unless out.contains i do out := out.push i
    return out

/-- Pass 1: find the atoms of all facts, including the case facts of auxiliary atoms. Returns all
leaf facts `(type, proof)`: the given ones followed by the generated ones. -/
def discover (leaves0 : Array (Expr × Expr)) : M (Array (Expr × Expr)) := do
  let mut leaves := leaves0
  let mut i := 0
  let mut pendDone := 0
  while true do
    while i < leaves.size do
      let (ty, pf) := leaves[i]!
      i := i + 1
      discard <| (try trans ty pf catch _ => pure none)
    let st ← get
    if pendDone < st.pending.size then
      for j in [pendDone:st.pending.size] do leaves := leaves.push st.pending[j]!
      pendDone := st.pending.size
    else break
  return leaves

/-- Pass 2: reflect the abstracted facts, search, and build the proof of `False` from the
facts `hvs` (`Expr`s of the local context) about the atom variables `xs`. Returns the proof and
the indices of the facts it uses. -/
def build (xs : Array Expr) (leafTys leafHs : Array Expr) (firstIsGoal : Bool) (maxFm : Nat) :
    M (Option (Expr × Array Nat)) := do
  modify fun st => { st with atoms := xs, pending := #[] }
  let mut forms : Array Form := #[]
  let mut idx : Array Nat := #[]
  for i in [0:leafTys.size] do
    if let some f ← (try trans leafTys[i]! leafHs[i]! catch _ => pure none) then
      forms := forms.push f; idx := idx.push i
  let nv := xs.size
  if nv == 0 || forms.isEmpty then return none
  -- relevance: facts connected to the negated goal (the first fact) or all of them
  let mut seen : Array Nat := #[]
  let mut keep : Array Bool := Array.replicate forms.size false
  if firstIsGoal && idx[0]! == 0 then
    keep := keep.set! 0 true
    seen := formAtoms forms[0]!
  else
    for i in [0:forms.size] do
      keep := keep.set! i true
      for a in formAtoms forms[i]! do unless seen.contains a do seen := seen.push a
  let mut changed := true
  while changed do
    changed := false
    for i in [0:forms.size] do
      if keep[i]! then continue
      let fa := formAtoms forms[i]!
      if fa.any seen.contains then
        keep := keep.set! i true
        changed := true
        for a in fa do unless seen.contains a do seen := seen.push a
  let mut poolData : List Con := []
  let mut poolPf : Option (Expr × Expr) := none
  let mut dsData : Array Alts := #[]
  let mut dsPfs : Array Expr := #[]
  let mut used : Array Nat := #[]
  for i in [0:forms.size] do
    unless keep[i]! do continue
    used := used.push idx[i]!
    match forms[i]! with
    | .conj cs pf =>
      let csE := toExpr cs
      match poolPf with
      | none => poolPf := some (csE, pf)
      | some (accE, accPf) =>
        let newE ← mkAppM ``HAppend.hAppend #[accE, csE]
        poolPf := some (newE, mkAppN (mkConst ``Sat.append) #[envPH, toExpr poolData, toExpr cs, accPf, pf])
      poolData := poolData ++ cs
    | .disj as pf =>
      dsData := dsData.push as
      dsPfs := dsPfs.push pf
  let some (poolE, poolSat) := poolPf | return none
  if poolData.length > 150 then return none
  let budget ← IO.mkRef maxFm
  let some tree ← search nv poolData.toArray dsData (Array.replicate dsData.size false) budget
    | return none
  if !(Janus.AddrSolve.check poolData dsData.toList tree) then return none
  if (← isTracingEnabledFor `janus.lin) then
    trace[janus.lin] "pool {repr poolData}\nds {repr dsData}\ntree {repr tree}"
  let mut dsE : Expr := toExpr (α := List Alts) []
  let mut dsPf : Expr := mkConst ``True.intro
  for i in (List.range dsData.size).reverse do
    let a := dsData[i]!
    dsPf := mkAppN (mkConst ``And.intro)
      #[asatTy a, mkApp2 (mkConst ``DS) envPH dsE, dsPfs[i]!, dsPf]
    dsE ← mkAppM ``List.cons #[toExpr a, dsE]
  let chk := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
    (mkAppN (mkConst ``Janus.AddrSolve.check) #[poolE, dsE, toExpr tree]) (mkConst ``Bool.true)
  let chkPf ← mkExpectedTypeHint
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)) chk
  let falsePf := mkAppN (mkConst ``refute) #[envPH, poolE, dsE, toExpr tree, chkPf, poolSat, dsPf]
  return some (falsePf, used)

/-- Close `g` (an arithmetic goal or `False`) by the reflective solver. `false`: not solved,
`g` untouched. -/
def solveGoal (g : MVarId) (maxFm : Nat := 200) : MetaM Bool := g.withContext do
  let goalT ← instantiateMVars (← g.getType)
  let lctx0 ← getLCtx
  let isFalse := goalT.isConstOf ``False
  -- the facts: the negated goal first, then the propositions of the context
  let hn ← mkFreshFVarId
  let lctxN := lctx0.mkLocalDecl hn `hn (mkNot goalT)
  let mut leaves0 : Array (Expr × Expr) := #[]
  if !isFalse then leaves0 := leaves0.push (mkNot goalT, mkFVar hn)
  for d in lctx0 do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    leaves0 := leaves0.push (ty, d.toExpr)
  withLCtx lctxN (← getLocalInstances) do
    -- pass 1: the atoms
    let (leaves, st1) ← (discover leaves0).run {}
    if st1.atoms.isEmpty then return false
    let atoms := st1.atoms
    -- abstract the atoms: fresh variables for them and for the facts
    let mut lctx := (← getLCtx).mkLocalDecl envId `env (mkApp (mkConst ``List [0]) natTy)
    let mut xs : Array Expr := #[]
    for i in [0:atoms.size] do
      let id ← mkFreshFVarId
      lctx := lctx.mkLocalDecl id (Name.mkSimple s!"x{i}") natTy
      xs := xs.push (mkFVar id)
    let abstr (e : Expr) : Expr := e.replace fun t =>
      match atoms.findIdx? (· == t) with
      | some i => some xs[i]!
      | none => none
    let mut tys : Array Expr := #[]
    let mut hs : Array Expr := #[]
    let mut hids : Array FVarId := #[]
    for (ty, _) in leaves do
      let ty' := abstr (← instantiateMVars ty)
      let id ← mkFreshFVarId
      lctx := lctx.mkLocalDecl id `h ty'
      tys := tys.push ty'
      hs := hs.push (mkFVar id)
      hids := hids.push id
    withLCtx lctx (← getLocalInstances) do
      let (r, _) ← (build xs tys hs (!isFalse) maxFm).run {}
      let some (falsePf, used) := r | return false
      let envList ← mkListLit natTy xs.toList
      let falsePf := falsePf.replaceFVar envPH envList
      let P ← mkLambdaFVars (xs ++ used.map (hs[·]!)) falsePf
      let proof0 := mkAppN P (atoms ++ used.map (fun i => leaves[i]!.2))
      let proof ← if isFalse then pure proof0
        else do pure (mkApp2 (mkConst ``Classical.byContradiction) goalT (← mkLambdaFVars #[mkFVar hn] proof0))
      let ty ← inferType proof
      unless ← isDefEq ty goalT do return false
      Lean.Meta.check proof
      g.assign proof
      return true

end Tac
end Janus.AddrSolve

/-- `janus_lin`: the reflective linear-address solver (`Janus.AddrSolve`); fails if it finds no
certificate. -/
elab "janus_lin" : tactic => do
  let g ← getMainGoal
  unless ← Janus.AddrSolve.Tac.solveGoal g do throwError "janus_lin: no certificate"
  replaceMainGoal []
