import Lean
import Janus.Tactic.Core
import Janus.Spec.Dynamic

/-!
# `janus_dyn`: dynamic-call hypotheses as executor equations

`janus_dyn h₁ h₂ …` takes hypotheses of the dynamic-call vocabulary (`Janus.Spec.Dynamic`) and
adds what the symbolic executors (`janus_run`, `janus64_run`) need to follow the call:

* `h : ItabIs ds m tab name` (`ds`, `name` closed): `h_tab : tab = BitVec.ofNat 64 base` with
  the itab's literal address (substituted when `tab` is a variable), `h_dyn_acc… :
  m.accessible base len false = true`, and one `h_dyn… : m.readLE (base + 8j) 8 = wⱼ` per word
  of the itab (`Fun[k]` is word `3 + k`), every literal evaluated from the extracted bytes;
* `h : FuncvalIs m fv fn` (`fn` closed, e.g. `segAddr p "pkg.F.func1"`):
  `h_dyn… : m.readLE fv.toNat 8 = <literal>`, its `accessible` fact and `fv.toNat + 8 ≤ 2^48`;
* `h : ClosureCtx m fv [v₀, …]`: `h_dyn… : m.readLE (fv.toNat + 8 + 8i) 8 = vᵢ.toNat` (offset
  as a literal), the `accessible` fact of the context words and their bound below `2^48`.

Equations named `h_dyn…` are rewrite rules of every step (see `stateHyps`). Each fact is proved
from `h` by a lemma of `Janus.Spec.Dynamic`; the evaluations are kernel-checked `rfl` lemmas.
-/

namespace Janus.Tactic.Dynamic

open Lean Meta Elab Tactic
open Janus Janus.Arm64 Janus.Spec

/-- `e = <its value>` for a closed `Nat` term, by a kernel-checked `rfl` lemma. -/
def evalEq (e : Expr) (what : String) : MetaM (Nat × Expr) := do
  let some v ← evalNat e | throwError "janus_dyn: cannot evaluate {what}:{indentExpr e}"
  let ty ← mkEq e (mkNatLit v)
  let name ← mkAuxLemma [] ty (← mkEqRefl (mkNatLit v))
  return (v, mkConst name)

def bv64 (n : Nat) : Expr := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit n)

/-- Add `name : ty := pf` to the goal. -/
def addHyp (g : MVarId) (name : Name) (ty pf : Expr) : MetaM MVarId := do
  let (_, g') ← (← g.assert name ty pf).intro1P
  return g'

def natLe (a b : Nat) : MetaM Expr := do mkDecideProof (← mkAppM ``LE.le #[mkNatLit a, mkNatLit b])

/-- One hypothesis. `k` numbers the generated names. -/
def dynOne (g : MVarId) (hE : Expr) (k : Nat) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← inferType hE)
  let nm (s : String) := Name.mkSimple s!"h_dyn{k}_{s}"
  match ty.getAppFnArgs with
  | (``ItabIs, #[ds, m, tab, name]) =>
    let (base, hb) ← evalEq (← mkAppM ``dataAddr #[ds, name]) "the itab's address"
    let (len, hl) ← evalEq (← mkAppM ``dataLen #[ds, name]) "the itab's length"
    if len == 0 then
      throwError "janus_dyn: there is no data object {name} in{indentExpr ds}\n(extract the \
        function with `janus extract … --targets '{name}'`)"
    let mut g := g
    -- the literal address of the itab
    let tabTy ← mkEq tab (bv64 base)
    g ← addHyp g (Name.mkSimple s!"h_tab{k}") tabTy (← mkAppM ``ItabIs.tab_lit #[hE, hb])
    -- readable
    let accTy ← mkEq (mkAppN (mkConst ``Memory.accessible) #[m, mkNatLit base, mkNatLit len,
      mkConst ``Bool.false]) (mkConst ``Bool.true)
    g ← g.withContext do
      addHyp g (nm "acc") accTy (← mkAppM ``ItabIs.accessible_lit #[hE, hb, hl])
    -- every 8-byte word
    for j in [0:len / 8] do
      let off := 8 * j
      let (v, hv) ← evalEq (← mkAppM ``dataWord #[ds, name, mkNatLit off, mkNatLit 8]) "an itab word"
      let a := base + off
      let rdTy ← mkEq (mkAppN (mkConst ``Memory.readLE) #[m, mkNatLit a, mkNatLit 8]) (mkNatLit v)
      let pf := mkAppN (mkConst ``ItabIs.readLE_lit) #[ds, m, tab, name, hE, mkNatLit base,
        mkNatLit len, mkNatLit a, mkNatLit v, mkNatLit off, mkNatLit 8, hb, hl,
        ← natLe (off + 8) len, ← mkEqRefl (mkNatLit a), hv]
      g ← g.withContext do addHyp g (nm s!"w{j}") rdTy pf
    -- disjoint from every writable range of the same memory in the context
    let mut i := 0
    for ld in ← g.withContext getLCtx do
      if ld.isImplementationDetail then continue
      let lty ← instantiateMVars ld.type
      let some (_, l, r) := lty.eq? | continue
      unless r.isConstOf ``Bool.true do continue
      let_expr Memory.accessible m' a n w := l | continue
      unless w.isConstOf ``Bool.true && m' == m do continue
      let pf ← mkAppOptM ``ItabIs.disjoint_lit #[none, none, none, none, hE, mkNatLit base,
        mkNatLit len, a, n, hb, hl, ld.toExpr]
      g ← g.withContext do addHyp g (nm s!"disj{i}") (← inferType pf) pf
      i := i + 1
    -- substitute a variable itab word
    if tab.isFVar then
      g ← g.withContext do
        let some d := (← getLCtx).findFromUserName? (Name.mkSimple s!"h_tab{k}") | return g
        try (subst g d.fvarId) catch _ => return g
    return g
  | (``FuncvalIs, #[m, fv, fn]) =>
    let (v, hv) ← evalEq fn "the funcval's code address"
    let rdTy ← mkEq (mkAppN (mkConst ``Memory.readLE) #[m, ← mkAppM ``BitVec.toNat #[fv], mkNatLit 8])
      (mkNatLit v)
    let g ← addHyp g (nm "fn") rdTy (← mkAppM ``FuncvalIs.read_lit #[hE, hv])
    let g ← g.withContext do
      let pf ← mkAppM ``FuncvalIs.accessible #[hE]
      addHyp g (nm "fnacc") (← inferType pf) pf
    g.withContext do
      let pf ← mkAppM ``FuncvalIs.bound #[hE]
      addHyp g (nm "fnbound") (← inferType pf) pf
  | (``ClosureCtx, #[m, fv, vars]) =>
    let some (_, elems) := (← instantiateMVars vars).listLit? |
      throwError "janus_dyn: the captured variables of{indentExpr ty}\nmust be a list literal"
    let n := elems.length
    let mut g := g
    let hn ← mkEqRefl (mkNatLit (8 * n))
    let accTy ← mkEq (mkAppN (mkConst ``Memory.accessible) #[m,
      ← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat #[fv], mkNatLit 8], mkNatLit (8 * n),
      mkConst ``Bool.false]) (mkConst ``Bool.true)
    let accPf ← mkExpectedTypeHint (← mkAppOptM ``ClosureCtx.accessible_lit #[none, none, none, hE,
        mkNatLit (8 * n), hn]) accTy
    g ← addHyp g (nm "ctxacc") accTy accPf
    g ← g.withContext do
      let pf ← mkAppOptM ``Memory.accessible_bound #[none, none, none, none, accPf]
      addHyp g (nm "ctxbound") (← inferType pf) pf
    for i in [0:n], v in elems do
      g ← g.withContext do
        let c := 8 + 8 * i
        let hi ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[vars]])
        let pf ← mkAppOptM ``ClosureCtx.read_lit #[none, none, none, hE, mkNatLit i, hi,
          mkNatLit c, v, ← mkEqRefl (mkNatLit c), ← mkEqRefl v]
        let rdTy ← mkEq (mkAppN (mkConst ``Memory.readLE) #[m,
          ← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat #[fv], mkNatLit c], mkNatLit 8])
          (← mkAppM ``BitVec.toNat #[v])
        addHyp g (nm s!"ctx{i}") rdTy (← mkExpectedTypeHint pf rdTy)
    return g
  | _ => throwError "janus_dyn: expected `ItabIs`, `FuncvalIs` or `ClosureCtx`, got{indentExpr ty}"

/-- See the module doc. -/
elab "janus_dyn" hs:(ppSpace colGt term:max)+ : tactic => withMainContext do
  let mut g ← getMainGoal
  let mut k := 0
  for h in hs do
    g ← g.withContext do
      let hE ← elabTerm h none
      dynOne g hE k
    k := k + 1
  replaceMainGoal [g]

end Janus.Tactic.Dynamic
