/-!
# A reflective solver for linear address side conditions

Proof automation for the side conditions of memory steps and frames (`a + n ≤ b ∨ b + k ≤ a`
style disjointness facts over a handful of symbolic addresses) used to call `omega`, whose
case splitting on the many disjunctive aliasing hypotheses of a large context is exponential.

The decision procedure here is *untrusted search plus a verified checker*:

* the search (`Janus.AddrSolve.Search`, meta code) finds a Fourier-Motzkin refutation tree: a case
  split on disjunctive hypotheses with, at each leaf, a nonnegative combination (Farkas
  certificate) of the linear facts of that branch;
* the checker (`check`, below) is a total computable function on closed data, and
  `refute` proves in Lean that `check pool alts tree = true` rules out any assignment of the
  atoms that satisfies the facts. The tactic applies `refute` and the kernel evaluates `check`
  (`Eq.refl true`; no `native_decide`, no `ofReduceBool`, no axiom).

A wrong certificate can therefore only make the proof fail to check; it can never prove a false
statement. Everything here is plain Lean: only `propext`, `Quot.sound` and `Classical.choice` (and
usually fewer) occur in the axiom closure.
-/

namespace Janus.AddrSolve

/-- A natural number expression over the atoms `0, 1, …` (the entries of an environment). -/
inductive NE where
  | atom (i : Nat)
  | lit (n : Nat)
  | add (a b : NE)
  | mul (k : Nat) (a : NE)
deriving Repr, Inhabited

/-- Environment lookup (structural, so the kernel unfolds it on a literal index). -/
def lkp : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: t, n + 1 => lkp t n

def NE.eval (env : List Nat) : NE → Nat
  | .atom i => lkp env i
  | .lit n => n
  | .add a b => a.eval env + b.eval env
  | .mul k a => k * a.eval env

/-- Dense coefficient vectors (missing entries are `0`). -/
def vadd : List Nat → List Nat → List Nat
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => (x + y) :: vadd a b

def vscale (k : Nat) : List Nat → List Nat
  | [] => []
  | x :: a => (k * x) :: vscale k a

/-- Pointwise `≤` (missing entries are `0`). -/
def vle : List Nat → List Nat → Bool
  | [], _ => true
  | x :: a, [] => x == 0 && vle a []
  | x :: a, y :: b => Nat.ble x y && vle a b

def dot : List Nat → List Nat → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: a, y :: b => x * y + dot a b

structure Lin where
  cs : List Nat
  c : Nat

def Lin.eval (env : List Nat) (l : Lin) : Nat := dot l.cs env + l.c

def unit : Nat → List Nat
  | 0 => [1]
  | n + 1 => 0 :: unit n

def Lin.ofNE : NE → Lin
  | .atom i => ⟨unit i, 0⟩
  | .lit n => ⟨[], n⟩
  | .add a b => ⟨vadd (Lin.ofNE a).cs (Lin.ofNE b).cs, (Lin.ofNE a).c + (Lin.ofNE b).c⟩
  | .mul k a => ⟨vscale k (Lin.ofNE a).cs, k * (Lin.ofNE a).c⟩

theorem dot_vadd (a b env : List Nat) : dot (vadd a b) env = dot a env + dot b env := by
  induction a generalizing b env with
  | nil => simp [vadd, dot]
  | cons x a ih =>
    cases b with
    | nil => simp [vadd, dot]
    | cons y b =>
      cases env with
      | nil => simp [vadd, dot]
      | cons z e => simp only [vadd, dot, ih]; rw [Nat.add_mul]; omega

theorem dot_vscale (k : Nat) (a env : List Nat) : dot (vscale k a) env = k * dot a env := by
  induction a generalizing env with
  | nil => simp [vscale, dot]
  | cons x a ih =>
    cases env with
    | nil => simp [vscale, dot]
    | cons z e => simp only [vscale, dot, ih, Nat.mul_add, Nat.mul_assoc]

theorem dot_unit (i : Nat) (env : List Nat) : dot (unit i) env = lkp env i := by
  induction i generalizing env with
  | zero => cases env <;> simp [unit, dot, lkp]
  | succ i ih => cases env <;> simp [unit, dot, lkp, ih]

theorem eval_ofNE (env : List Nat) (e : NE) : (Lin.ofNE e).eval env = e.eval env := by
  induction e with
  | atom i => simp [Lin.ofNE, Lin.eval, dot_unit, NE.eval]
  | lit n => simp [Lin.ofNE, Lin.eval, dot, NE.eval]
  | add a b iha ihb =>
    simp only [Lin.ofNE, Lin.eval, NE.eval] at *
    rw [dot_vadd]; omega
  | mul k a ih =>
    simp only [Lin.ofNE, Lin.eval, NE.eval] at *
    rw [dot_vscale, ← Nat.mul_add, ih]

theorem dot_mono (a b env : List Nat) (h : vle a b = true) : dot a env ≤ dot b env := by
  induction a generalizing b env with
  | nil => simp [dot]
  | cons x a ih =>
    cases b with
    | nil =>
      simp only [vle, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h2⟩ := h
      cases env with
      | nil => simp [dot]
      | cons z e =>
        have := ih [] e h2
        simp only [dot] at this ⊢
        omega
    | cons y b =>
      simp only [vle, Bool.and_eq_true, Nat.ble_eq] at h
      cases env with
      | nil => simp [dot]
      | cons z e =>
        simp only [dot]
        exact Nat.add_le_add (Nat.mul_le_mul_right _ h.1) (ih b e h.2)

/-- A constraint `lhs ≤ rhs`. -/
abbrev Con := NE × NE

/-- All constraints of a list hold. -/
def Sat (env : List Nat) : List Con → Prop
  | [] => True
  | c :: cs => c.1.eval env ≤ c.2.eval env ∧ Sat env cs

theorem Sat.append {env : List Nat} {a b : List Con} (ha : Sat env a) (hb : Sat env b) :
    Sat env (a ++ b) := by
  induction a with
  | nil => exact hb
  | cons c a ih => exact ⟨ha.1, ih ha.2⟩

/-- `Σ mᵢ·Rᵢ` and `Σ mᵢ·Lᵢ` of a pool with multipliers `ms` (missing multipliers are `0`). -/
def comb : List Con → List Nat → Lin × Lin
  | [], _ => (⟨[], 0⟩, ⟨[], 0⟩)
  | _ :: _, [] => (⟨[], 0⟩, ⟨[], 0⟩)
  | (l, r) :: cs, m :: ms =>
    let (P, Q) := comb cs ms
    let lr := Lin.ofNE r
    let ll := Lin.ofNE l
    (⟨vadd (vscale m lr.cs) P.cs, m * lr.c + P.c⟩, ⟨vadd (vscale m ll.cs) Q.cs, m * ll.c + Q.c⟩)

/-- A Farkas refutation: `Σ mᵢ·Rᵢ ≥ Σ mᵢ·Lᵢ` while the variable part of the left side is pointwise
`≤` that of the right and its constant is strictly smaller. -/
def farkas (pool : List Con) (ms : List Nat) : Bool :=
  let (P, Q) := comb pool ms
  vle P.cs Q.cs && Nat.blt P.c Q.c

theorem comb_sound (env : List Nat) (pool : List Con) (ms : List Nat) (h : Sat env pool) :
    ((comb pool ms).2).eval env ≤ ((comb pool ms).1).eval env := by
  induction pool generalizing ms with
  | nil => simp [comb, Lin.eval, dot]
  | cons c cs ih =>
    cases ms with
    | nil => simp [comb, Lin.eval, dot]
    | cons m ms =>
      obtain ⟨l, r⟩ := c
      have h1 := ih ms h.2
      have h2 := h.1
      simp only [comb, Lin.eval, dot_vadd, dot_vscale] at h1 ⊢
      have h3 := Nat.mul_le_mul_left m (show (Lin.ofNE l).eval env ≤ (Lin.ofNE r).eval env by
        rw [eval_ofNE, eval_ofNE]; exact h2)
      simp only [Lin.eval] at h3
      rw [Nat.mul_add, Nat.mul_add] at h3
      omega

theorem farkas_sound {env : List Nat} {pool : List Con} {ms : List Nat}
    (h : farkas pool ms = true) (hs : Sat env pool) : False := by
  simp only [farkas, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2⟩ := h
  have := comb_sound env pool ms hs
  simp only [Lin.eval] at this
  have h3 := dot_mono _ _ env h1
  omega

/-- A disjunction of conjunctions: the alternatives (`alts = [A₁, A₂, …]` means `A₁ ∨ A₂ ∨ …`). -/
abbrev Alts := List (List Con)

def ASat (env : List Nat) : Alts → Prop
  | [] => False
  | a :: as => Sat env a ∨ ASat env as

/-- Every disjunction of the list holds. -/
def DS (env : List Nat) : List Alts → Prop
  | [] => True
  | d :: ds => ASat env d ∧ DS env ds

inductive Tree where
  | leaf (ms : List Nat)
  | split (k : Nat) (ts : List Tree)
deriving Repr, Inhabited

def getAlts : List Alts → Nat → Option Alts
  | [], _ => none
  | d :: _, 0 => some d
  | _ :: ds, n + 1 => getAlts ds n

mutual
def check (pool : List Con) (ds : List Alts) : Tree → Bool
  | .leaf ms => farkas pool ms
  | .split k ts =>
    match getAlts ds k with
    | none => false
    | some alts => checkAll pool ds alts ts
def checkAll (pool : List Con) (ds : List Alts) : List (List Con) → List Tree → Bool
  | [], [] => true
  | a :: as, t :: ts => check (pool ++ a) ds t && checkAll pool ds as ts
  | _, _ => false
end

theorem DS.get {env : List Nat} {ds : List Alts} (h : DS env ds) {k : Nat} {alts : Alts}
    (hk : getAlts ds k = some alts) : ASat env alts := by
  induction ds generalizing k with
  | nil => simp [getAlts] at hk
  | cons d ds ih =>
    cases k with
    | zero => simp only [getAlts, Option.some.injEq] at hk; subst hk; exact h.1
    | succ k => exact ih h.2 hk

mutual
theorem check_sound {env : List Nat} {ds : List Alts} (hd : DS env ds) :
    ∀ (t : Tree) (pool : List Con), check pool ds t = true → Sat env pool → False
  | .leaf ms, pool, h, hs => farkas_sound h hs
  | .split k ts, pool, h, hs => by
    simp only [check] at h
    split at h
    · cases h
    · rename_i alts hk
      exact checkAll_sound hd alts ts pool h hs (hd.get hk)
theorem checkAll_sound {env : List Nat} {ds : List Alts} (hd : DS env ds) :
    ∀ (alts : List (List Con)) (ts : List Tree) (pool : List Con),
      checkAll pool ds alts ts = true → Sat env pool → ASat env alts → False
  | [], [], _, _, _, h => h.elim
  | [], _ :: _, _, h, _, _ => by simp [checkAll] at h
  | _ :: _, [], _, h, _, _ => by simp [checkAll] at h
  | a :: as, t :: ts, pool, h, hs, hα => by
    simp only [checkAll, Bool.and_eq_true] at h
    rcases hα with ha | has
    · exact check_sound hd t (pool ++ a) h.1 (hs.append ha)
    · exact checkAll_sound hd as ts pool h.2 hs has
end

/-- The soundness theorem the tactic applies: if `check` accepts, no assignment satisfies the
facts. -/
theorem refute {env : List Nat} {pool : List Con} {ds : List Alts} {t : Tree}
    (h : check pool ds t = true) (hs : Sat env pool) (hd : DS env ds) : False :=
  check_sound hd t pool h hs

end Janus.AddrSolve
