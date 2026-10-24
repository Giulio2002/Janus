import Janus.Tactic.Ring

/-!
# A verified decision procedure for carry chains

The goals left after executing multi-limb arithmetic are equations between natural-number
terms built from limbs (64-bit values, memory reads, products), `+`, `*`, literals, `/ 2^64`
and `% 2^64` (carries and limbs), truncated `-` and `(decide (2^64 ≤ a)).toNat` (amd64 carry
flags). They hold because of the carry-chain identity
`a = a % 2^64 + 2^64 · (a / 2^64)` and bounds on the limbs: no `% 2^64` of a carry-sized term
wraps.

`check` decides such an equation by computing a *carry normal form* for each side:

* every subterm `t` gets a canonical value `P(t)`, an integer polynomial (`Janus.Ring.Poly`)
  over **atoms**: the input atoms (the opaque leaves, `x₀ … x_{n-1}`) and *quotient atoms*
  `D_j = L_j / k_j` (an `Int` division of a polynomial in earlier atoms, listed in a table);
* `P(a / k)` and `P(a % k)` split `P(a) = L + k·Y` with the coefficients of `L` in `[0, k)`.
  If `L` is known to lie in `[0, k)` (by interval arithmetic), `a / k = Y` and `a % k = L`;
  otherwise `a / k = D_j + Y` and `a % k = L - k·D_j` for the table entry `D_j = L / k`.
  This merges the two halves of a carry: `p / B + (z + p % B) / B` becomes `(p + z) / B`;
* every subterm also gets an interval (from its structure and from its normal form), which
  is what shows that a carry `hi + c₁ + c₂` is below `2^64`.

The two sides are equal if their normal forms are equal, or if their difference is a multiple
`g·Z` (with `g` the gcd of its coefficients) and both sides lie in `[0, g)`: this closes
"low half" statements such as `Σ 2^(64i)·zᵢ = (X·Y) % 2^256`.

The table of quotient atoms and the atom intervals are a certificate produced by the tactic
(`Janus.Tactic.Carry`, by running `build`); `check` only verifies it. `check_sound` is the
soundness theorem; the tactic proves `check … = true` by `Eq.refl true`, which the kernel
evaluates. No axioms beyond Lean's are involved.
-/

namespace Janus.Carry

open Janus.Ring

/-! ## Terms -/

/-- A natural-number term. `var i` is the `i`-th atom of the environment. -/
inductive Tm where
  | var (i : Nat)
  | lit (n : Nat)
  | add (a b : Tm)
  | mul (a b : Tm)
  | sub (a b : Tm)
  | div (a : Tm) (k : Nat)
  | mod (a : Tm) (k : Nat)
  /-- `(decide (k ≤ a)).toNat`, the carry flag of an addition. -/
  | geb (a : Tm) (k : Nat)
  deriving Inhabited

/-- List lookup with default `0`. -/
def nth : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => nth xs i

def lnth {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => lnth xs i

def Tm.eval (env : List Nat) : Tm → Nat
  | .var i => nth env i
  | .lit n => n
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .sub a b => a.eval env - b.eval env
  | .div a k => a.eval env / k
  | .mod a k => a.eval env % k
  | .geb a k => (decide (k ≤ a.eval env)).toNat

/-! ## Intervals -/

/-- An interval `[lo, hi]`; `none` is unbounded. -/
structure Iv where
  lo : Option Int
  hi : Option Int
  deriving Inhabited

def Iv.top : Iv := ⟨none, none⟩

def Iv.mem (I : Iv) (v : Int) : Prop :=
  (∀ l, I.lo = some l → l ≤ v) ∧ (∀ h, I.hi = some h → v ≤ h)

theorem Iv.mem_top (v : Int) : Iv.top.mem v := ⟨fun _ h => by simp [Iv.top] at h, fun _ h => by simp [Iv.top] at h⟩

def oadd : Option Int → Option Int → Option Int
  | some a, some b => some (a + b)
  | _, _ => none

def omap (f : Int → Int) : Option Int → Option Int
  | some a => some (f a)
  | none => none

def omax : Option Int → Option Int → Option Int
  | some a, some b => cond (intBle a b) (some b) (some a)
  | some a, none => some a
  | none, b => b

def omin : Option Int → Option Int → Option Int
  | some a, some b => cond (intBle a b) (some a) (some b)
  | some a, none => some a
  | none, b => b

def Iv.add (I J : Iv) : Iv := ⟨oadd I.lo J.lo, oadd I.hi J.hi⟩
def Iv.neg (I : Iv) : Iv := ⟨omap (fun x => -x) I.hi, omap (fun x => -x) I.lo⟩
def Iv.sub (I J : Iv) : Iv := I.add J.neg
def Iv.scale (c : Int) (I : Iv) : Iv :=
  cond (intNonneg c) ⟨omap (c * ·) I.lo, omap (c * ·) I.hi⟩ ⟨omap (c * ·) I.hi, omap (c * ·) I.lo⟩
def Iv.inter (I J : Iv) : Iv := ⟨omax I.lo J.lo, omin I.hi J.hi⟩
def Iv.divK (k : Int) (I : Iv) : Iv := ⟨omap (· / k) I.lo, omap (· / k) I.hi⟩
def Iv.const (c : Int) : Iv := ⟨some c, some c⟩

/-- Products of intervals, for nonnegative intervals only (everything else is unbounded). -/
def Iv.mul (I J : Iv) : Iv :=
  match I.lo, J.lo with
  | some a, some b =>
    cond (intNonneg a && intNonneg b)
      ⟨some (a * b), match I.hi, J.hi with | some c, some d => some (c * d) | _, _ => none⟩ Iv.top
  | _, _ => Iv.top

/-- `I ⊆ [0, k)`. -/
def Iv.within (I : Iv) (k : Int) : Bool :=
  match I.lo, I.hi with
  | some l, some h => intNonneg l && intBle (h + 1) k
  | _, _ => false

/-- Every element of `I` is `≤` every element of `J`. -/
def Iv.ble (I J : Iv) : Bool :=
  match I.hi, J.lo with
  | some h, some l => intBle h l
  | _, _ => false

def obeq : Option Int → Option Int → Bool
  | some a, some b => intBeq a b
  | none, none => true
  | _, _ => false

def Iv.beq (I J : Iv) : Bool := obeq I.lo J.lo && obeq I.hi J.hi

def ivNth : List Iv → Nat → Iv
  | [], _ => Iv.top
  | x :: _, 0 => x
  | _ :: xs, i + 1 => ivNth xs i

/-! ### Braun trees, for logarithmic lookups by the kernel -/

/-- A binary tree holding a list: element `0` at the root, the odd positions of the tail in
the left subtree and the even ones in the right subtree. -/
inductive BT (α : Type) where
  | leaf
  | node (l : BT α) (v : α) (r : BT α)

def BT.get {α : Type} (d : α) : BT α → Nat → α
  | .leaf, _ => d
  | .node l v r, i =>
    cond (Nat.beq i 0) v (cond (Nat.beq (i % 2) 1) (BT.get d l (i / 2)) (BT.get d r (i / 2 - 1)))

/-- The elements at even positions. -/
def evens {α : Type} : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: evens xs

/-- The elements at odd positions. -/
def odds {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | _ :: y :: xs => y :: odds xs

def BT.ofListF {α : Type} : Nat → List α → BT α
  | 0, _ => .leaf
  | _ + 1, [] => .leaf
  | f + 1, x :: xs => .node (BT.ofListF f (evens xs)) x (BT.ofListF f (odds xs))

def BT.ofList {α : Type} (l : List α) : BT α := BT.ofListF l.length l

/-- `l` without its first `n` elements. -/
def ivDrop : List Iv → Nat → List Iv
  | l, 0 => l
  | [], _ + 1 => []
  | _ :: xs, n + 1 => ivDrop xs n

def monoIv (σ : Nat → Iv) : Mono → Iv
  | [] => Iv.const 1
  | i :: m => (σ i).mul (monoIv σ m)

def polyIv (σ : Nat → Iv) : Poly → Iv
  | [] => Iv.const 0
  | (m, c) :: p => ((monoIv σ m).scale c).add (polyIv σ p)

/-! ## The checker -/

/-- The certificate: `n` input atoms, the quotient atoms `D_j = tbl[j].1 / tbl[j].2` (atom
`n + j`), and an interval for every atom. -/
structure Ctx where
  n : Nat
  tbl : List (Poly × Nat)
  ivs : List Iv
  /-- `ivs` as a tree (for lookups) -/
  ivt : BT Iv := BT.ofList ivs
  /-- `tbl` as a tree (for lookups) -/
  tbt : BT (Option (Poly × Nat)) := BT.ofList (tbl.map some)

/-- The interval of atom `i`. -/
def Ctx.iv (c : Ctx) (i : Nat) : Iv := c.ivt.get Iv.top i

def lookup (L : Poly) (k : Nat) : List (Poly × Nat) → Nat → Option Nat
  | [], _ => none
  | (L', k') :: t, j => cond (Nat.beq k k' && Poly.beq L L') (some j) (lookup L k t (j + 1))

/-- The numerator and modulus of atom `i`, if it is a quotient atom. -/
def qatom (c : Ctx) (i : Nat) : Option (Poly × Nat) :=
  cond (Nat.ble c.n i) (c.tbt.get none (i - c.n)) none

/-- A term `e·D_j` of `p` with `D_j` a quotient atom of modulus `k`. -/
def findPos (c : Ctx) (k : Nat) (e : Int) : Poly → Option (Nat × Poly)
  | [] => none
  | (m, e') :: p =>
    match m with
    | [j] =>
      cond (intBeq e e')
        (match qatom c j with
         | some (Lj, kj) => cond (Nat.beq k kj) (some (j, Lj)) (findPos c k e p)
         | none => findPos c k e p)
        (findPos c k e p)
    | _ => findPos c k e p

/-- Terms `-e·D_i` and `e·D_j` of `all` (`e > 0`, quotient atoms of the same modulus). -/
def findPair (c : Ctx) (all : Poly) : Poly → Option (Nat × Poly × Nat × Poly × Nat × Int)
  | [] => none
  | (m, d) :: p =>
    match m with
    | [i] =>
      cond (intNonneg d) (findPair c all p)
        (match qatom c i with
         | some (Li, k) =>
           match findPos c k (-d) all with
           | some (j, Lj) => some (i, Li, j, Lj, k, -d)
           | none => findPair c all p
         | none => findPair c all p)
    | _ => findPair c all p

/-- `L_j / k - L_i / k` lies in `[⌊lo/k⌋, ⌊hi/k⌋ + 1]` for `L_j - L_i ∈ [lo, hi]`. -/
def pairIv (c : Ctx) (Li Lj : Poly) (k : Nat) : Iv :=
  let I := polyIv (c.iv) (Lj.sub Li)
  ⟨omap (· / (k : Int)) I.lo, omap (fun h => h / (k : Int) + 1) I.hi⟩

/-- The interval of a normal form, refined by differences of quotient atoms: a carry minus
the carry of a smaller sum (`(a + b) / k - a / k`) is bounded by `b / k + 1`, which the
intervals of the two atoms alone do not show. -/
def civF (c : Ctx) : Nat → Poly → Iv
  | 0, p => polyIv (c.iv) p
  | f + 1, p =>
    match findPair c p p with
    | some (i, Li, j, Lj, k, e) =>
      let rest := p.sub (((Poly.atom j).sub (Poly.atom i)).scale e)
      (polyIv (c.iv) p).inter ((civF c f rest).add ((pairIv c Li Lj k).scale e))
    | none => polyIv (c.iv) p

def civ (c : Ctx) (p : Poly) : Iv := civF c 4 p

/-- The interval `I` of a value with normal form `p`, refined by `civ` only if `I` alone does
not show that the value lies in `[0, k)` (which saves most interval computations). -/
def refine (c : Ctx) (p : Poly) (I : Iv) (k : Int) : Iv :=
  cond (I.within k) I (I.inter (civ c p))

/-- `(v / k, v % k)` for a value `v` with normal form `p` and interval `J`. -/
def divmod (c : Ctx) (p : Poly) (J : Iv) (k : Nat) : Option (Poly × Poly) :=
  let s := p.splitMod (k : Int)
  let JL := cond s.2.isNil J (civ c s.1)
  cond (JL.within k) (some (s.2, s.1))
    (match lookup s.1 k c.tbl 0 with
     | some j => some ((Poly.atom (c.n + j)).add s.2, s.1.sub ((Poly.atom (c.n + j)).scale k))
     | none => none)

/-- Normal form and interval of a term. -/
def chk (c : Ctx) : Tm → Option (Poly × Iv)
  | .var i => cond (Nat.blt i c.n) (some (Poly.atom i, c.iv i)) none
  | .lit v => some (Poly.const v, Iv.const v)
  | .add a b =>
    match chk c a, chk c b with
    | some (p, I), some (q, J) => some (p.add q, I.add J)
    | _, _ => none
  | .mul a b =>
    match chk c a, chk c b with
    | some (p, I), some (q, J) => some (p.mul q, I.mul J)
    | _, _ => none
  | .sub a b =>
    match chk c a, chk c b with
    | some (p, I), some (q, J) =>
      cond (J.ble I) (some (p.sub q, I.sub J))
        (let I' := I.inter (civ c p)
         let J' := J.inter (civ c q)
         cond (J'.ble I') (some (p.sub q, I'.sub J'))
          (cond (I'.ble J') (some ([], Iv.const 0)) none))
    | _, _ => none
  | .div a k =>
    match chk c a with
    | some (p, I) =>
      let J := refine c p I k
      cond (Nat.blt 0 k)
        (match divmod c p J k with
         | some (d, _) => some (d, J.divK k)
         | none => none) none
    | none => none
  | .mod a k =>
    match chk c a with
    | some (p, I) =>
      let J := refine c p I k
      cond (Nat.blt 0 k)
        (match divmod c p J k with
         | some (_, r) => some (r, cond (J.within k) J ⟨some 0, some ((k : Int) - 1)⟩)
         | none => none) none
    | none => none
  | .geb a k =>
    match chk c a with
    | some (p, I) =>
      let J := refine c p I (2 * k)
      cond (J.within k) (some ([], Iv.const 0))
        (cond (Iv.ble (Iv.const k) J) (some (Poly.const 1, Iv.const 1))
          (cond (Nat.blt 0 k && J.within (2 * k))
            (match divmod c p J k with
             | some (d, _) => some (d, ⟨some 0, some 1⟩)
             | none => none) none))
    | none => none

/-- The interval of every input atom is `[0, ub]` (`ivs` and `ubs` walked together). -/
def varsOK : List Iv → List (Option Nat) → Bool
  | _, [] => true
  | iv :: ivs, u :: us =>
    Iv.beq iv ⟨some 0, match u with | some u => some (u : Int) | none => none⟩ && varsOK ivs us
  | [], _ :: _ => false

/-- Every quotient atom divides by a positive constant, only mentions earlier atoms, and has
the interval computed from its numerator (`rest`: the intervals of the quotient atoms). -/
def tblOK (n : Nat) (σ : Nat → Iv) : List Iv → List (Poly × Nat) → Nat → Bool
  | _, [], _ => true
  | iv :: rest, (L, k) :: t, j =>
    Nat.blt 0 k && L.below (n + j) && Iv.beq iv ((polyIv σ L).divK k) && tblOK n σ rest t (j + 1)
  | [], _ :: _, _ => false

/-- The certificate is well formed: one interval per atom, input atoms `[0, ub]`, quotient
atoms well founded with the interval of their numerator. -/
def certOK (ubs : List (Option Nat)) (tbl : List (Poly × Nat)) (ivs : List Iv) : Bool :=
  Nat.beq ivs.length (ubs.length + tbl.length) && varsOK ivs ubs &&
    tblOK ubs.length ((BT.ofList ivs).get Iv.top) (ivDrop ivs ubs.length) tbl 0

/-- Decide `a.eval env = b.eval env` for every environment within the bounds `ubs`. -/
def check (ubs : List (Option Nat)) (tbl : List (Poly × Nat)) (ivs : List Iv) (a b : Tm) : Bool :=
  let c : Ctx := { n := ubs.length, tbl := tbl, ivs := ivs }
  certOK ubs tbl ivs &&
  match chk c a, chk c b with
  | some (p, I), some (q, J) =>
    let d := p.sub q
    d.isNil ||
      (Nat.blt 0 d.gcdCoeffs && d.dvdAll d.gcdCoeffs &&
        (I.inter (civ c p)).within d.gcdCoeffs &&
        (J.inter (civ c q)).within d.gcdCoeffs)
  | _, _ => false

/-- Decide `a.eval env ≤ b.eval env` for every environment within the bounds `ubs`: by the
intervals of the two sides, or by the interval of the normal form of `b - a`. -/
def checkLe (ubs : List (Option Nat)) (tbl : List (Poly × Nat)) (ivs : List Iv) (a b : Tm) : Bool :=
  let c : Ctx := { n := ubs.length, tbl := tbl, ivs := ivs }
  certOK ubs tbl ivs &&
  match chk c a, chk c b with
  | some (p, I), some (q, J) =>
    Iv.ble (I.inter (civ c p)) (J.inter (civ c q)) ||
      (match (civ c (q.sub p)).lo with
       | some l => intNonneg l
       | none => false)
  | _, _ => false

/-! ## Building the certificate (run by the tactic; not trusted) -/

/-- Like `divmod`, but adds a missing quotient atom to the table. -/
def divmodB (c : Ctx) (p : Poly) (J : Iv) (k : Nat) : (Poly × Poly) × Ctx :=
  let s := p.splitMod (k : Int)
  let JL := cond s.2.isNil J (civ c s.1)
  if JL.within k then ((s.2, s.1), c) else
  match lookup s.1 k c.tbl 0 with
  | some j => (((Poly.atom (c.n + j)).add s.2, s.1.sub ((Poly.atom (c.n + j)).scale k)), c)
  | none =>
    let j := c.tbl.length
    let iv := (polyIv (c.iv) s.1).divK k
    let c' : Ctx := { n := c.n, tbl := c.tbl ++ [(s.1, k)], ivs := c.ivs ++ [iv] }
    (((Poly.atom (c.n + j)).add s.2, s.1.sub ((Poly.atom (c.n + j)).scale k)), c')

/-- Like `chk`, growing the table of quotient atoms as needed. -/
def chkB (c : Ctx) : Tm → Option (Poly × Iv) × Ctx
  | .var i => (if i < c.n then some (Poly.atom i, c.iv i) else none, c)
  | .lit v => (some (Poly.const v, Iv.const v), c)
  | .add a b =>
    match chkB c a with
    | (some (p, I), c) =>
      match chkB c b with
      | (some (q, J), c) => (some (p.add q, I.add J), c)
      | (none, c) => (none, c)
    | (none, c) => (none, c)
  | .mul a b =>
    match chkB c a with
    | (some (p, I), c) =>
      match chkB c b with
      | (some (q, J), c) => (some (p.mul q, I.mul J), c)
      | (none, c) => (none, c)
    | (none, c) => (none, c)
  | .sub a b =>
    match chkB c a with
    | (some (p, I), c) =>
      match chkB c b with
      | (some (q, J), c) =>
        if J.ble I then (some (p.sub q, I.sub J), c) else
        let I' := I.inter (civ c p)
        let J' := J.inter (civ c q)
        if J'.ble I' then (some (p.sub q, I'.sub J'), c)
        else if I'.ble J' then (some ([], Iv.const 0), c) else (none, c)
      | (none, c) => (none, c)
    | (none, c) => (none, c)
  | .div a k =>
    match chkB c a with
    | (some (p, I), c) =>
      let J := refine c p I k
      if 0 < k then
        let ((d, _), c) := divmodB c p J k
        (some (d, J.divK k), c)
      else (none, c)
    | (none, c) => (none, c)
  | .mod a k =>
    match chkB c a with
    | (some (p, I), c) =>
      let J := refine c p I k
      if 0 < k then
        let ((_, r), c) := divmodB c p J k
        (some (r, if J.within k then J else ⟨some 0, some ((k : Int) - 1)⟩), c)
      else (none, c)
    | (none, c) => (none, c)
  | .geb a k =>
    match chkB c a with
    | (some (p, I), c) =>
      let J := refine c p I (2 * k)
      if J.within k then (some ([], Iv.const 0), c)
      else if Iv.ble (Iv.const k) J then (some (Poly.const 1, Iv.const 1), c)
      else if 0 < k && J.within (2 * k) then
        let ((d, _), c) := divmodB c p J k
        (some (d, ⟨some 0, some 1⟩), c)
      else (none, c)
    | (none, c) => (none, c)

/-- The certificate (table and atom intervals) for statements about the terms `ts`. -/
def build (ubs : List (Option Nat)) (ts : List Tm) : List (Poly × Nat) × List Iv :=
  let ivs0 := ubs.map fun u => (⟨some 0, match u with | some u => some (u : Int) | none => none⟩ : Iv)
  let c := ts.foldl (fun c t => (chkB c t).2) { n := ubs.length, tbl := [], ivs := ivs0 }
  (c.tbl, c.ivs)

end Janus.Carry
