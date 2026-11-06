import Lean
import Janus.Tactic.Carry

/-!
# `janus_carry_nf`: relations between carry chains in normal form

After `janus_run` on multi-limb arithmetic, a hypothesis or goal such as
`M ≤ Σ 2^(64 i) · limbᵢ` has limbs that are nested `(… + c) % 2^64` of carries `(… ) / 2^64`: forty
nested quotients for a four-limb routine, which `omega` handles by introducing a variable for each and
searching (minutes, or never). `janus_carry` already computes, for each side, the *carry normal form*
(`Janus.Carry`): a polynomial in the atoms (memory reads, …) and a few merged, flattened *quotient atoms*
`D = L / k`: a whole add/sub-with-carry chain becomes `X + Y - 2^256 · D`.

`janus_carry_nf` (opt-in; `janus_run` never calls it) rewrites a relation `a = b`, `a ≤ b`, `a < b` between
`Nat` terms (anywhere in a hypothesis or goal: under `¬`, `∧`, `∨`, `→`, `if`) to the relation of the
normal forms, with the negative terms moved across (no truncated subtraction at the top):

  `a ≤ b`   becomes   `P_a + N_b ≤ P_b + N_a`   (a = P_a - N_a, b = P_b - N_b),

the quotient atoms rendered as `(P - N) / k`. The result is a linear problem over the atoms and a handful
of distinct quotients, which `omega` solves quickly. The rewrite is kernel-checked: `a + N_a = P_a` and
`b + N_b = P_b` are proved by `janus_carry` (a certificate checked by kernel evaluation), and the
relation by `omega`-proved lemmas `nf_eq`/`nf_le`/`nf_lt`. If a side has no normal form or one of the two
equations is not proved, the relation is left alone.
-/

namespace Janus.Carry

open Lean Meta Elab Tactic Simp

/-- The quotient of a sum by a modulus, when the number of moduli it exceeds the remainder by is one of `0, 1, 2` (the
conditional subtractions of `AddMod`): a goal `S % M = E` becomes `S = E ∨ S = E + M ∨ S = E + 2 * M` and `E < M`, one
`omega` problem on the value-level facts instead of three attempts, two of which fail slowly. -/
theorem mod_cases3 (S E M : Nat) (h : S = E ∨ S = E + M ∨ S = E + 2 * M) (hE : E < M) : S % M = E := by
  rcases h with h | h | h
  · subst h; exact Nat.mod_eq_of_lt hE
  · subst h; rw [Nat.add_comm, Nat.add_mod_left]; exact Nat.mod_eq_of_lt hE
  · subst h; rw [Nat.add_comm, Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hE

/-- `S % M = E` from `S = E + k M` for `k ≤ 3` (arm64 `AddMod`: both operands reduced once, then a final reduction). -/
theorem mod_cases4 (S E M : Nat) (h : S = E ∨ S = E + M ∨ S = E + 2 * M ∨ S = E + 3 * M) (hE : E < M) : S % M = E := by
  rcases h with h | h | h | h
  · subst h; exact Nat.mod_eq_of_lt hE
  · subst h; rw [Nat.add_comm, Nat.add_mod_left]; exact Nat.mod_eq_of_lt hE
  · subst h; rw [Nat.add_comm, Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hE
  · subst h; rw [Nat.add_comm, Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hE

theorem nf_eq (a b Pa Na Pb Nb : Nat) (ha : a + Na = Pa) (hb : b + Nb = Pb) :
    (a = b) = (Pa + Nb = Pb + Na) := propext (by omega)
theorem nf_le (a b Pa Na Pb Nb : Nat) (ha : a + Na = Pa) (hb : b + Nb = Pb) :
    (a ≤ b) = (Pa + Nb ≤ Pb + Na) := propext (by omega)
theorem nf_lt (a b Pa Na Pb Nb : Nat) (ha : a + Na = Pa) (hb : b + Nb = Pb) :
    (a < b) = (Pa + Nb < Pb + Na) := propext (by omega)

/-- A 32-byte read is four 64-bit limbs. -/
theorem readLE_32 (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 32 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 +
      2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 := by
  rw [show 32 = 8 + 24 from rfl, Janus.Arm64.Memory.readLE_add, show 24 = 8 + 16 from rfl,
    Janus.Arm64.Memory.readLE_add, show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]
  simp only [Nat.add_assoc]
  omega

/-- The top limb of a 32-byte value is its quotient by `2^192` (all `omega` needs of the limbs of a value atom for
the comparisons of top limbs the code makes first). -/
theorem readLE_32_top (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 32 / 2 ^ 192 = m.readLE (a + 24) 8 := by
  have h := readLE_32 m a
  have h0 := Janus.Arm64.Memory.readLE_lt m a 8
  have h1 := Janus.Arm64.Memory.readLE_lt m (a + 8) 8
  have h2 := Janus.Arm64.Memory.readLE_lt m (a + 16) 8
  have h3 := Janus.Arm64.Memory.readLE_lt m (a + 24) 8
  simp only [Nat.reducePow] at *
  omega

private def natE (n : Nat) : Expr := mkNatLit n

/-- A family of four limbs `readLE m a 8`, `readLE m (a+8) 8`, … among the atoms: the indices of the limbs and the
value `readLE m a 32`. -/
structure Family where
  idx : Array Nat
  m : Expr
  base : Expr
  value : Expr
  deriving Inhabited

/-- The 32-byte values whose four limbs are all atoms (the limb at `a` fixes the family). -/
private def families (atoms : Array Expr) : MetaM (Array Family) := do
  let mut out : Array Family := #[]
  for i in [0:atoms.size] do
    let e := atoms[i]!
    unless e.isAppOfArity ``Janus.Arm64.Memory.readLE 3 && e.getArg! 2 == natE 8 do continue
    let m := e.getArg! 0; let a := e.getArg! 1
    let mut idx := #[i]
    for k in [8, 16, 24] do
      let ak ← mkAppM ``HAdd.hAdd #[a, natE k]
      let tgt := mkApp3 (mkConst ``Janus.Arm64.Memory.readLE) m ak (natE 8)
      match atoms.findIdx? (· == tgt) with
      | some j => idx := idx.push j
      | none => break
    if idx.size == 4 then
      out := out.push { idx, m, base := a, value := mkApp3 (mkConst ``Janus.Arm64.Memory.readLE) m a (natE 32) }
  return out

/-- Substitute `σ i` for the atom `i` in a polynomial. -/
private def substPoly (σ : Array Janus.Ring.Poly) (p : Janus.Ring.Poly) : Janus.Ring.Poly :=
  p.foldl (fun acc (m, c) =>
    acc.add (m.foldl (fun t i => t.mul (σ.getD i (Janus.Ring.Poly.atom i))) (Janus.Ring.Poly.const c))) []

/-- The product of the atoms of a monomial. -/
private def renderMono (atoms : Array Expr) (m : Janus.Ring.Mono) : MetaM (Option Expr) := do
  let mut acc : Option Expr := none
  for i in m do
    let some a := atoms[i]? | return none
    acc := some (← match acc with
      | none => pure a
      | some x => mkAppM ``HMul.hMul #[x, a])
  return acc

/-- A polynomial as `(P, N)`: the sums of its positive and of its negative terms (`none`: empty). A quotient atom
`D_j` may be negative (`⌊(X - M) / k⌋`); it is rendered as the natural number `Q_j = D_j + offs[j]`, so a term
`c · D_j` is `c · Q_j - c · offs[j]` (only as a monomial of its own: a product with a shifted atom fails). -/
private def renderPoly (atoms : Array Expr) (offs : Array Nat) (p : Janus.Ring.Poly) :
    MetaM (Option (Option Expr × Option Expr)) := do
  let mut pos : Option Expr := none
  let mut neg : Option Expr := none
  let mut cst : Int := 0
  -- terms in the order of their atoms' expressions (not of the atom indices, which depend on the relation): the same
  -- sum is rendered the same way in every hypothesis, so `omega` sees one atom for one quotient
  let key (m : Janus.Ring.Mono) : List Expr := m.map fun i => atoms.getD i (natE 0)
  let rec lexLt : List Expr → List Expr → Bool
    | [], [] => false
    | [], _ => true
    | _, [] => false
    | a :: as, b :: bs => if a == b then lexLt as bs else Expr.lt a b
  let sorted := (p.toArray.qsort fun (m1, _) (m2, _) => lexLt (key m1) (key m2)).toList
  for (m, c) in sorted do
    if m.isEmpty then cst := cst + c; continue
    if m.any (fun i => offs.getD i 0 > 0) then
      match m with
      | [i] => cst := cst - c * (offs.getD i 0 : Nat)
      | _ => return none
    let some x ← renderMono atoms m | return none
    let k := c.natAbs
    let term ← if k == 1 then pure x else mkAppM ``HMul.hMul #[natE k, x]
    if c > 0 then
      pos := some (← match pos with | none => pure term | some y => mkAppM ``HAdd.hAdd #[y, term])
    else
      neg := some (← match neg with | none => pure term | some y => mkAppM ``HAdd.hAdd #[y, term])
  if cst > 0 then
    let t := natE cst.natAbs
    pos := some (← match pos with | none => pure t | some y => mkAppM ``HAdd.hAdd #[y, t])
  else if cst < 0 then
    let t := natE cst.natAbs
    neg := some (← match neg with | none => pure t | some y => mkAppM ``HAdd.hAdd #[y, t])
  return some (pos, neg)

/-- `x + y` with `none` as zero. -/
private def addOpt (x y : Option Expr) : MetaM Expr := do
  match x, y with
  | none, none => pure (natE 0)
  | some a, none => pure a
  | none, some b => pure b
  | some a, some b => mkAppM ``HAdd.hAdd #[a, b]

/-- The normal forms of the two sides, as the expressions `P_a`, `N_a`, `P_b`, `N_b`. -/
private def normalForms (a b : Expr) :
    MetaM (Option (Option Expr × Option Expr × Option Expr × Option Expr × Array ((Expr × Expr) × Expr))) := do
  let (((_, ta), (_, tb)), st) ← (do
      let x ← reflect a
      let y ← reflect b
      return (x, y) : RM _).run {}
  let hyps ← hypBounds
  let mut bounds : Array (Option (Nat × Expr)) := #[]
  for e in st.atoms do
    let sb ← structBound e
    let hb := hyps.get? e
    bounds := bounds.push (match sb, hb with
      | some (u, p), some (u', p') => if u' < u then some (u', p') else some (u, p)
      | some x, none => some x
      | none, some x => some x
      | none, none => none)
  let ubs := bounds.toList.map (·.map (·.1))
  let (tbl, ivs) := build ubs [ta, tb]
  let c : Ctx := { n := ubs.length, tbl := tbl, ivs := ivs }
  let some (p, _) := chk c ta | return none
  let some (q, _) := chk c tb | return none
  -- 32-byte values: `l₀ ↦ V - 2^64 l₁ - 2^128 l₂ - 2^192 l₃`, so a combination of the limbs that is a combination of
  -- values leaves no limb behind and `omega` sees `V` (bounded by `< 2^256`) instead of four limbs
  let fams ← families st.atoms
  let nAll := st.atoms.size + tbl.length
  let mut atoms : Array Expr := st.atoms ++ Array.replicate tbl.length (natE 0) ++ fams.map (·.value)
  let mut σ : Array Janus.Ring.Poly := (Array.range nAll).map Janus.Ring.Poly.atom
  for f in [0:fams.size] do
    let fam := fams[f]!
    let v := Janus.Ring.Poly.atom (nAll + f)
    let rest := (List.range 3).foldl (fun acc k =>
      acc.sub ((Janus.Ring.Poly.atom (fam.idx[k+1]!)).scale (2 ^ (64 * (k + 1))))) v
    σ := σ.set! fam.idx[0]! rest
  let p := substPoly σ p
  let q := substPoly σ q
  -- the quotient atoms `(P - N + t k) / k` (= `D + t`) in table order
  let mut offs : Array Nat := Array.replicate (nAll + fams.size) 0
  for j in [0:tbl.length] do
    let (L, k) := tbl[j]!
    let L := substPoly σ L
    let some (lp, ln) ← renderPoly atoms offs L | return none
    -- the lower bound of `D_j = L / k` fixes the shift `t` (so that `L + t k ≥ 0`)
    let t : Nat := match (ivs[ubs.length + j]!).lo with
      | some lo => if lo < 0 then lo.natAbs else 0
      | none => 0
    if (ivs[ubs.length + j]!).lo.isNone then return none
    let lp' ← if t == 0 then pure lp else
      pure (some (← match lp with | none => pure (natE (t * k)) | some x => mkAppM ``HAdd.hAdd #[x, natE (t * k)]))
    let some lp' := lp' | return none
    let num ← match ln with
      | none => pure lp'
      | some n => mkAppM ``HSub.hSub #[lp', n]
    atoms := atoms.set! (ubs.length + j) (← mkAppM ``HDiv.hDiv #[num, natE k])
    offs := offs.set! (ubs.length + j) t
  let some (pa, na) ← renderPoly atoms offs p | return none
  let some (pb, nb) ← renderPoly atoms offs q | return none
  return some (pa, na, pb, nb, fams.map (·.value) |>.zip (fams.map (·.base)) |>.zip (fams.map (·.m)))

/-- Prove `lhs = rhs` (Nat) by `janus_carry`, after unfolding the 32-byte values `fams` (`value`, `base`, memory) that
the normal form introduced into the four limbs they stand for. -/
private def proveCarryEq (lhs rhs : Expr) (fams : Array ((Expr × Expr) × Expr)) : MetaM (Option Expr) := do
  let mut goal ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs rhs)
  let orig := goal
  let mut g := goal.mvarId!
  for ((v, base), m) in fams do
    let t ← instantiateMVars (← g.getType)
    unless (t.find? (· == v)).isSome do continue
    let heq ← mkAppM ``readLE_32 #[m, base]
    let r ← g.rewrite t heq
    g ← g.replaceTargetEq r.eNew r.eqProof
  if ← proveEq g then return some (← instantiateMVars orig) else return none

/-- Carry terms: a quotient, remainder or product of atoms, or a carry flag `(decide …).toNat`. -/
private def carryish (e : Expr) : Bool :=
  hasCarryOps e || (e.find? fun x => x.isAppOfArity ``Bool.toNat 1 && (x.getArg! 0).isAppOf ``Decidable.decide).isSome

/-- The rewrite of one relation. -/
def nfRel (e : Expr) : SimpM Step := do
  let (rel, a, b) ← match e.getAppFnArgs with
    | (``Eq, #[ty, a, b]) => if isNatTy ty then pure (0, a, b) else return .continue
    | (``LE.le, #[ty, _, a, b]) => if isNatTy ty then pure (1, a, b) else return .continue
    | (``LT.lt, #[ty, _, a, b]) => if isNatTy ty then pure (2, a, b) else return .continue
    | _ => return .continue
  let limbs (e : Expr) : Bool := (e.find? fun x => x.isAppOfArity ``Janus.Arm64.Memory.readLE 3 && x.getArg! 2 == natE 8).isSome
  unless carryish a || carryish b || limbs a || limbs b do return .continue
  let some (pa, na, pb, nb, fams) ← normalForms a b | do
    trace[janus.carry] "nf: a side has no normal form: {e}"; return .continue
  -- a relation without carry terms is rewritten only to put the limbs of a value into the value
  unless carryish a || carryish b || !fams.isEmpty do return .continue
  let Pa ← addOpt pa none; let Na ← addOpt na none
  let Pb ← addOpt pb none; let Nb ← addOpt nb none
  let some ha ← proveCarryEq (← mkAppM ``HAdd.hAdd #[a, Na]) Pa fams | do trace[janus.carry] "nf: left equation not proved: {e}"; return .continue
  let some hb ← proveCarryEq (← mkAppM ``HAdd.hAdd #[b, Nb]) Pb fams | do trace[janus.carry] "nf: right equation not proved: {e}"; return .continue
  let lemma := match rel with | 0 => ``nf_eq | 1 => ``nf_le | _ => ``nf_lt
  let pf ← mkAppM lemma #[a, b, Pa, Na, Pb, Nb, ha, hb]
  let e' := (← inferType pf).appArg!
  return .done { expr := e', proof? := some pf }

/-- `janus_carry_nf` rewrites the `Nat` relations of the goal (or of the listed hypotheses) to their carry normal
form (see the module comment). -/
simproc_decl janusCarryNfEq ((_ : Nat) = _) := nfRel
simproc_decl janusCarryNfLe ((_ : Nat) ≤ _) := nfRel
simproc_decl janusCarryNfLt ((_ : Nat) < _) := nfRel

end Janus.Carry

namespace Janus.Tactic

open Lean Janus.Carry

open Lean Meta Elab Tactic Janus.Carry in
/-- `janus_carry_values`: for each 32-byte value whose four 64-bit limbs occur in the goal or the hypotheses, add
`hv : m.readLE a 32 < 256 ^ 32` (the bound of the value atom `janus_carry_nf` introduces) and `hvt`, its top limb as its quotient
by `2^192` (`Janus.Carry.readLE_32_top`). -/
elab "janus_carry_values" : tactic => withMainContext do
  let mut reads : Array Expr := #[]
  let add (e : Expr) (acc : Array Expr) : Array Expr := Id.run do
    let mut acc := acc
    let mut seen : Std.HashSet Expr := {}
    let mut todo := #[e]
    while todo.size > 0 do
      let x := todo.back!
      todo := todo.pop
      if seen.contains x then continue
      seen := seen.insert x
      if x.isAppOfArity ``Janus.Arm64.Memory.readLE 3 && x.getArg! 2 == mkNatLit 8 then
        if !acc.contains x then acc := acc.push x
      match x with
      | .app f a => todo := todo.push f |>.push a
      | .mdata _ b | .proj _ _ b => todo := todo.push b
      | _ => pure ()
    return acc
  reads := add (← instantiateMVars (← getMainTarget)) reads
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    reads := add (← instantiateMVars d.type) reads
  for fam in ← families reads do
    let ty ← mkAppM ``LT.lt #[fam.value, ← mkAppM ``HPow.hPow #[mkNatLit 256, mkNatLit 32]]
    let mut have_ := false
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← instantiateMVars d.type) == ty then have_ := true
    unless have_ do
      let pf ← mkAppM ``Janus.Arm64.Memory.readLE_lt #[fam.m, fam.base, mkNatLit 32]
      let g ← getMainGoal
      let (_, g') ← (← g.assert `hv ty pf).intro1P
      replaceMainGoal [g']
      -- and its top limb as its quotient by `2^192`
      let pf2 ← mkAppM ``readLE_32_top #[fam.m, fam.base]
      let (_, g'') ← (← g'.assert `hvt (← inferType pf2) pf2).intro1P
      replaceMainGoal [g'']

open Lean Meta Elab Tactic in
/-- Does the proposition split `omega` into cases (`∨`, `¬ (a ∧ b)`, `↔`, `→` between propositions)? -/
private def splitsOmega (ty : Expr) : Bool :=
  (ty.find? fun e => e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2 ||
    (e.isAppOfArity ``Not 1 && (e.getArg! 0).isAppOfArity ``And 2)).isSome

open Lean Meta Elab Tactic in
/-- `janus_clear_splitting` (and `janus_omega_linear` = it, then `omega`): the context without the hypotheses that make it split (`∨`, `¬ (a ∧ b)`, `↔`: the
`Apart`/disjointness facts of a statement with many pointers, branch conditions on single limbs). `omega` splits on a
disjunction only after the facts without it fail to close the goal, and then on all of them in turn: a goal that
the linear facts decide costs seconds without them and minutes with them (the 13 disjunctions of the `AddMod` fast path).
Fails, with the state restored, if the linear facts do not close the goal. -/
elab "janus_clear_splitting" : tactic => do
  let g ← getMainGoal
  let mut g := g
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← g.withContext (isProp ty) do continue
    if ty.isForall then continue
    if splitsOmega ty then
      g ← (g.tryClear d.fvarId)
  replaceMainGoal [g]

register_option janus.nf.budget : Nat := {
  defValue := 30000
  descr := "`janus_omega_linear`: heartbeat budget (thousands, like `maxHeartbeats`) of its `omega` call; an `omega` that does not \
    close the goal within it fails (state restored), so that `first | janus_omega_linear | …` moves on"
}

open Lean Meta Elab Tactic in
/-- See `janus_clear_splitting`: then `omega`, within the budget `janus.nf.budget`. -/
elab "janus_omega_linear" : tactic => do
  let b := janus.nf.budget.get (← getOptions)
  let saved ← saveState
  evalTactic (← `(tactic| janus_clear_splitting))
  let ok ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := b * 1000 }) <|
      withCurrHeartbeats do
        evalTactic (← `(tactic| omega))
        pure true)
    (fun _ => pure false)
  unless ok do
    saved.restore
    throwError "janus_omega_linear: omega did not close the goal within janus.nf.budget = {b}"


/-- The size of `e` as a tree (saturating), over the DAG. -/
private partial def nodeCount (e : Expr) (memo : IO.Ref (Std.HashMap Expr Nat)) : IO Nat := do
  if let some n := (← memo.get).get? e then return n
  let r ← match e with
    | .app f a => pure (min 1000000000 ((← nodeCount f memo) + (← nodeCount a memo) + 1))
    | .mdata _ b | .proj _ _ b => pure ((← nodeCount b memo) + 1)
    | .lam _ t b _ | .forallE _ t b _ => pure (min 1000000000 ((← nodeCount t memo) + (← nodeCount b memo) + 1))
    | _ => pure 1
  memo.modify (·.insert e r)
  return r

open Lean Meta Elab Tactic in
/-- The quotients `a / k` (`k` a literal above 1) of the natural-number propositions of the goal and the context, smallest first. -/
private def quotientsOf (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let mut out : Array Expr := #[]
  let mut seen : Std.HashSet Expr := {}
  let mut todo : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (← isProp ty) then todo := todo.push ty
  while todo.size > 0 do
    let x := todo.back!
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    if x.isAppOfArity ``HDiv.hDiv 6 && isNatTy (x.getArg! 0) then
      if let some k := evalLit (x.getArg! 5) then
        if k > 1 && (evalLit x).isNone then out := out.push x
    match x with
    | .app f a => todo := todo.push f |>.push a
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
    | _ => pure ()
  let memo ← IO.mkRef ({} : Std.HashMap Expr Nat)
  let sizes ← out.mapM fun e => do return (← nodeCount e memo, e)
  return (sizes.qsort (fun a b => a.1 < b.1)).map (·.2)

open Lean Meta Elab Tactic Janus.Ring in
/-- The upper bound `hi` of the quotient `q = a / k` that the interval analysis of `janus_carry` finds (from the ranges
of the atoms alone), and the proof `q ≤ hi` (`janus_carry`). -/
private def quotientBound (g : MVarId) (q : Expr) : MetaM (Option (Nat × Expr)) := g.withContext do
  let (((_, ta)), st) ← (do let x ← reflect q; return x : RM _).run {}
  let hyps ← hypBounds
  let mut bounds : Array (Option (Nat × Expr)) := #[]
  for e in st.atoms do
    let sb ← structBound e
    let hb := hyps.get? e
    bounds := bounds.push (match sb, hb with
      | some (u, p), some (u', p') => if u' < u then some (u', p') else some (u, p)
      | some x, none => some x
      | none, some x => some x
      | none, none => none)
  let ubs := bounds.toList.map (·.map (·.1))
  let (tbl, ivs) := build ubs [ta]
  let c : Ctx := { n := ubs.length, tbl := tbl, ivs := ivs }
  let some (p, I) := chk c ta | return none
  let some hi := (I.inter (polyIv (ivNth ivs) p)).hi | return none
  if hi < 0 || hi > 1000000 then return none
  let hi := hi.toNat
  let goal ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[q, mkNatLit hi])
  if ← proveEq goal.mvarId! then return some (hi, ← instantiateMVars goal) else return none

open Lean Meta Elab Tactic in
/-- `janus_quotient_bounds`: for each quotient `a / k` of the goal and the hypotheses, the hypothesis `a / k ≤ hi` with
the bound `hi` the interval analysis of `janus_carry` finds from the ranges of the atoms (proved by `janus_carry`).
`omega` knows a quotient only through `k · q ≤ a < k · q + k`; with a bound on `q` itself the huge coefficients of a
four-limb carry chain no longer make it search (a problem with six such quotients: over two minutes without, two seconds
with). Only quotients of value atoms (`m.readLE a 32`); nothing for a quotient without a small bound; never fails. -/
elab "janus_quotient_bounds" : tactic => do
  let qs ← quotientsOf (← getMainGoal)
  for q in qs do
    -- the quotients of value atoms (32-byte reads): the carries between the limbs of a chain are what `janus_carry_nf` removed
    unless (q.find? fun x => x.isAppOfArity ``Janus.Arm64.Memory.readLE 3 && x.getArg! 2 == mkNatLit 32).isSome do continue
    let g ← getMainGoal
    let some (hi, pf) ← quotientBound g q | continue
    let ty ← g.withContext (mkAppM ``LE.le #[q, mkNatLit hi])
    let (_, g') ← (← g.assert `hqb ty pf).intro1P
    replaceMainGoal [g']

/-- `omega` on the value-level facts after `janus_carry_nf`: the bounds of the quotients first
(`janus_quotient_bounds`), then `janus_omega_linear`. -/
macro "janus_omega_values" : tactic => `(tactic| (janus_quotient_bounds; janus_omega_linear))

/-- Rewrite the natural-number relations (`=`, `≤`, `<`) with carry terms in the goal, or at `h₁ h₂ ⊢` / `*`, to the
relation of their carry normal forms (`Janus.Carry.nfRel`): few distinct quotients, linear in the atoms. A 32-byte value
whose four limbs occur is one atom `m.readLE a 32` (bounded by the hypothesis `janus_carry_values` adds). -/
macro "janus_carry_nf" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (janus_carry_values
             simp only [Janus.Carry.janusCarryNfEq, Janus.Carry.janusCarryNfLe, Janus.Carry.janusCarryNfLt] $[$loc]?))

end Janus.Tactic
