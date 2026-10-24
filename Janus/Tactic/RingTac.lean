import Lean
import Janus.Tactic.Carry

/-!
# `janus_ring`: commutative ring identities by reflection

`janus_ring` proves an equation `a = b` between integer (or natural-number) polynomial
expressions: `+`, `*`, `-`, unary `-`, `^` with a literal exponent and literals over arbitrary
atoms. Both sides are reflected into `RTm`, normalised to `Janus.Ring.Poly` (sorted sparse
polynomials) and compared; `ring_sound` turns the Boolean comparison, evaluated by the kernel
(`Eq.refl true`), into the equation. On `Nat`, it goes through `janus_carry` (which also
knows `/`, `%` and truncated `-` with bounds).

It is the closing step of carry-chain proofs once every `% 2^64` has been removed, and a
replacement for the `ring` tactic of Mathlib in proofs that only need polynomial identities.
No axioms beyond Lean's are involved.
-/

namespace Janus.Ring

open Lean Meta Elab Tactic

/-- An integer polynomial expression over the atoms of `env`. -/
inductive RTm where
  | var (i : Nat)
  | lit (n : Int)
  | add (a b : RTm)
  | mul (a b : RTm)
  | sub (a b : RTm)
  | neg (a : RTm)
  | pow (a : RTm) (n : Nat)

def inth : List Int → Nat → Int
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => inth xs i

def RTm.eval (env : List Int) : RTm → Int
  | .var i => inth env i
  | .lit n => n
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .sub a b => a.eval env - b.eval env
  | .neg a => - a.eval env
  | .pow a n => a.eval env ^ n

def Poly.pow (p : Poly) : Nat → Poly
  | 0 => Poly.const 1
  | n + 1 => Poly.mul (Poly.pow p n) p

theorem Poly.eval_pow (ρ : Nat → Int) (p : Poly) : ∀ n, (Poly.pow p n).eval ρ = p.eval ρ ^ n
  | 0 => by simp [Poly.pow, Int.pow_zero]
  | n + 1 => by simp [Poly.pow, Poly.eval_pow ρ p n, Int.pow_succ]

def RTm.norm : RTm → Poly
  | .var i => Poly.atom i
  | .lit n => Poly.const n
  | .add a b => a.norm.add b.norm
  | .mul a b => a.norm.mul b.norm
  | .sub a b => a.norm.sub b.norm
  | .neg a => a.norm.neg
  | .pow a n => a.norm.pow n

theorem RTm.eval_norm (env : List Int) :
    ∀ t : RTm, t.norm.eval (inth env) = t.eval env
  | .var i => by simp [RTm.norm, RTm.eval]
  | .lit n => by simp [RTm.norm, RTm.eval]
  | .add a b => by simp [RTm.norm, RTm.eval, RTm.eval_norm env a, RTm.eval_norm env b]
  | .mul a b => by simp [RTm.norm, RTm.eval, RTm.eval_norm env a, RTm.eval_norm env b]
  | .sub a b => by simp [RTm.norm, RTm.eval, RTm.eval_norm env a, RTm.eval_norm env b]
  | .neg a => by simp [RTm.norm, RTm.eval, RTm.eval_norm env a]
  | .pow a n => by simp [RTm.norm, RTm.eval, Poly.eval_pow, RTm.eval_norm env a]

/-- **Soundness of `janus_ring`.** -/
theorem ring_sound (env : List Int) (a b : RTm) (h : Poly.beq a.norm b.norm = true) :
    a.eval env = b.eval env := by
  rw [← RTm.eval_norm env a, ← RTm.eval_norm env b, Poly.beq_eq h]

/-! ## The tactic -/

def isIntTy (e : Expr) : Bool := e.isConstOf ``Int

/-- An integer literal expression (`OfNat`, `Int.ofNat`, `Nat.cast` of a literal, `-`). -/
partial def intLit? (e : Expr) : Option Int :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => (Janus.Carry.evalLit n).map Int.ofNat
  | (``Int.ofNat, #[n]) => (Janus.Carry.evalLit n).map Int.ofNat
  | (``Nat.cast, #[_, _, n]) => (Janus.Carry.evalLit n).map Int.ofNat
  | (``Neg.neg, #[_, _, a]) => (intLit? a).map (- ·)
  | _ => none

structure RS where
  atoms : Array Expr := #[]
  idx : Std.HashMap Expr Nat := {}

partial def reflectR (e : Expr) : StateT RS MetaM (Expr × RTm) := do
  if let some n := intLit? e then
    return (mkApp (mkConst ``RTm.lit) (Janus.Carry.intE n), .lit n)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[t, _, _, _, a, b]) =>
    if isIntTy t then
      let (ea, ta) ← reflectR a; let (eb, tb) ← reflectR b
      return (mkApp2 (mkConst ``RTm.add) ea eb, .add ta tb)
  | (``HMul.hMul, #[t, _, _, _, a, b]) =>
    if isIntTy t then
      let (ea, ta) ← reflectR a; let (eb, tb) ← reflectR b
      return (mkApp2 (mkConst ``RTm.mul) ea eb, .mul ta tb)
  | (``HSub.hSub, #[t, _, _, _, a, b]) =>
    if isIntTy t then
      let (ea, ta) ← reflectR a; let (eb, tb) ← reflectR b
      return (mkApp2 (mkConst ``RTm.sub) ea eb, .sub ta tb)
  | (``Neg.neg, #[t, _, a]) =>
    if isIntTy t then
      let (ea, ta) ← reflectR a
      return (mkApp (mkConst ``RTm.neg) ea, .neg ta)
  | (``HPow.hPow, #[t, n, _, _, a, k]) =>
    if isIntTy t && n.isConstOf ``Nat then
      if let some k := Janus.Carry.evalLit k then
        if k ≤ 64 then
          let (ea, ta) ← reflectR a
          return (mkApp2 (mkConst ``RTm.pow) ea (mkRawNatLit k), .pow ta k)
  | _ => pure ()
  let s ← get
  let i ← match s.idx.get? e with
    | some i => pure i
    | none => do
      modify fun s => { s with atoms := s.atoms.push e, idx := s.idx.insert e s.atoms.size }
      pure s.atoms.size
  return (mkApp (mkConst ``RTm.var) (mkRawNatLit i), .var i)

/-- Prove an `Int` equation by normalisation. -/
def proveRingInt (g : MVarId) : MetaM Bool := g.withContext do
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let some (ty, lhs, rhs) := t.eq? | return false
  unless isIntTy ty do return false
  let (((ea, ta), (eb, tb)), st) ←
    (do return (← reflectR lhs, ← reflectR rhs) : StateT RS MetaM _).run {}
  -- decided here first: the kernel check of the auxiliary lemma is deferred
  unless Poly.beq ta.norm tb.norm do return false
  let envE := Janus.Carry.listE (mkConst ``Int) st.atoms.toList
  let chkTy ← mkEq (mkApp2 (mkConst ``Poly.beq) (mkApp (mkConst ``RTm.norm) ea)
    (mkApp (mkConst ``RTm.norm) eb)) (mkConst ``Bool.true)
  let val := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let name ← mkAuxLemma [] chkTy val
  g.assign (← mkExpectedTypeHint (mkAppN (mkConst ``ring_sound) #[envE, ea, eb, mkConst name]) (← g.getType))
  return true

/-- `janus_ring`: close a polynomial identity over `Int` or `Nat` (on `Nat` also with `/`, `%`
by literals and truncated `-`, via `janus_carry`). -/
elab "janus_ring" : tactic => do
  let g ← getMainGoal
  let saved ← saveState
  let ok ← try
      if ← proveRingInt g then pure true else Janus.Carry.proveAll g
    catch _ => pure false
  if ok then replaceMainGoal [] else
    saved.restore
    throwError "janus_ring: the two sides have different normal forms"

end Janus.Ring
