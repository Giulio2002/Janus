/-!
# Verified polynomial normal forms over `Int`

`Poly` is a sparse polynomial with integer coefficients over atoms indexed by `Nat`: a list of
(monomial, coefficient) pairs, where a monomial is a sorted list of atom indices (with
repetition). The operations below keep the list sorted by monomial and free of zero
coefficients, so two polynomials are equal as functions iff they are equal as lists. Only the
direction needed for proofs is proved: every operation is correct with respect to `Poly.eval`
(whether or not its inputs are sorted), so a structural equality check `Poly.beq p q = true`
implies `p.eval ρ = q.eval ρ`.

Everything is written for evaluation by the kernel (`Eq.refl true` proofs of `Bool` checks):
structural recursion only (merges carry an explicit fuel argument), `Bool`-valued comparisons
on `Nat` (which the kernel evaluates with GMP), no type classes in the hot paths.

This file is used by `Janus.Tactic.Carry` (the carry-chain decision procedure behind
`janus_arith`) and by the `janus_ring` tactic (`Janus.Tactic.RingTac`).
-/

namespace Janus.Ring

/-- A monomial: a sorted list of atom indices. -/
abbrev Mono := List Nat
/-- A polynomial: (monomial, nonzero coefficient) pairs, sorted by monomial. -/
abbrev Poly := List (Mono × Int)

/-! ## Evaluation -/

def Mono.eval (ρ : Nat → Int) : Mono → Int
  | [] => 1
  | i :: m => ρ i * Mono.eval ρ m

def Poly.eval (ρ : Nat → Int) : Poly → Int
  | [] => 0
  | (m, c) :: p => c * Mono.eval ρ m + Poly.eval ρ p

@[simp] theorem Mono.eval_nil (ρ : Nat → Int) : Mono.eval ρ [] = 1 := rfl
@[simp] theorem Mono.eval_cons (ρ : Nat → Int) (i : Nat) (m : Mono) :
    Mono.eval ρ (i :: m) = ρ i * Mono.eval ρ m := rfl
@[simp] theorem Poly.eval_nil (ρ : Nat → Int) : Poly.eval ρ [] = 0 := rfl
@[simp] theorem Poly.eval_cons (ρ : Nat → Int) (m : Mono) (c : Int) (p : Poly) :
    Poly.eval ρ ((m, c) :: p) = c * Mono.eval ρ m + Poly.eval ρ p := rfl

theorem Poly.eval_append (ρ : Nat → Int) (p q : Poly) :
    Poly.eval ρ (p ++ q) = Poly.eval ρ p + Poly.eval ρ q := by
  induction p with
  | nil => simp
  | cons t p ih => obtain ⟨m, c⟩ := t; simp [ih]; omega

/-! ## Boolean comparisons -/

/-- Equality of integers, by the constructors (kernel-friendly). -/
def intBeq : Int → Int → Bool
  | .ofNat a, .ofNat b => Nat.beq a b
  | .negSucc a, .negSucc b => Nat.beq a b
  | _, _ => false

theorem intBeq_eq : ∀ {a b : Int}, intBeq a b = true → a = b
  | .ofNat a, .ofNat b, h => by simp [intBeq] at h; rw [h]
  | .negSucc a, .negSucc b, h => by simp [intBeq] at h; rw [h]
  | .ofNat _, .negSucc _, h => by simp [intBeq] at h
  | .negSucc _, .ofNat _, h => by simp [intBeq] at h

/-- `0 ≤ a`. -/
def intNonneg : Int → Bool
  | .ofNat _ => true
  | .negSucc _ => false

theorem intNonneg_le : ∀ {a : Int}, intNonneg a = true → 0 ≤ a
  | .ofNat a, _ => Int.natCast_nonneg a
  | .negSucc _, h => by simp [intNonneg] at h

/-- `a ≤ b`. -/
def intBle (a b : Int) : Bool := intNonneg (b - a)

theorem intBle_le {a b : Int} (h : intBle a b = true) : a ≤ b := by
  have := intNonneg_le h; omega

def Mono.beq : Mono → Mono → Bool
  | [], [] => true
  | i :: m, j :: n => Nat.beq i j && Mono.beq m n
  | _, _ => false

theorem Mono.beq_eq : ∀ {m n : Mono}, Mono.beq m n = true → m = n
  | [], [], _ => rfl
  | i :: m, j :: n, h => by
    simp only [Mono.beq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1, Mono.beq_eq h.2]
  | [], _ :: _, h => by simp [Mono.beq] at h
  | _ :: _, [], h => by simp [Mono.beq] at h

/-- Lexicographic order on monomials. -/
def Mono.blt : Mono → Mono → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | i :: m, j :: n => Nat.blt i j || (Nat.beq i j && Mono.blt m n)

def Poly.beq : Poly → Poly → Bool
  | [], [] => true
  | (m, c) :: p, (n, d) :: q => Mono.beq m n && intBeq c d && Poly.beq p q
  | _, _ => false

theorem Poly.beq_eq : ∀ {p q : Poly}, Poly.beq p q = true → p = q
  | [], [], _ => rfl
  | (m, c) :: p, (n, d) :: q, h => by
    simp only [Poly.beq, Bool.and_eq_true] at h
    rw [Mono.beq_eq h.1.1, intBeq_eq h.1.2, Poly.beq_eq h.2]
  | [], _ :: _, h => by simp [Poly.beq] at h
  | _ :: _, [], h => by simp [Poly.beq] at h

def Poly.isNil : Poly → Bool
  | [] => true
  | _ :: _ => false

theorem Poly.eval_of_isNil {p : Poly} (h : p.isNil = true) (ρ : Nat → Int) : p.eval ρ = 0 := by
  cases p with
  | nil => rfl
  | cons _ _ => simp [Poly.isNil] at h

/-! ## Ring operations -/

/-- Merge two sorted polynomials (`f` is fuel, at least the total length). -/
def Poly.addF : Nat → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, (m, c) :: p, [] => (m, c) :: p
  | f + 1, (m, c) :: p, (n, d) :: q =>
    cond (Mono.beq m n)
      (cond (intBeq (c + d) 0) (Poly.addF f p q) ((m, c + d) :: Poly.addF f p q))
      (cond (Mono.blt m n) ((m, c) :: Poly.addF f p ((n, d) :: q))
        ((n, d) :: Poly.addF f ((m, c) :: p) q))

theorem Poly.eval_addF (ρ : Nat → Int) :
    ∀ f p q, Poly.eval ρ (Poly.addF f p q) = Poly.eval ρ p + Poly.eval ρ q
  | 0, p, q => Poly.eval_append ρ p q
  | _ + 1, [], q => by simp [Poly.addF]
  | _ + 1, (m, c) :: p, [] => by simp [Poly.addF]
  | f + 1, (m, c) :: p, (n, d) :: q => by
    simp only [Poly.addF]
    cases h1 : Mono.beq m n
    · cases h2 : Mono.blt m n
      · simp only [Bool.cond_false, Poly.eval_cons, Poly.eval_addF ρ f]; omega
      · simp only [Bool.cond_false, Bool.cond_true, Poly.eval_cons, Poly.eval_addF ρ f]; omega
    · have hmn := Mono.beq_eq h1; subst hmn
      cases h2 : intBeq (c + d) 0
      · simp only [Bool.cond_false, Bool.cond_true, Poly.eval_cons, Poly.eval_addF ρ f, Int.add_mul]; omega
      · have hz := intBeq_eq h2
        simp only [Bool.cond_true, Poly.eval_cons, Poly.eval_addF ρ f]
        have : c * Mono.eval ρ m + d * Mono.eval ρ m = 0 := by rw [← Int.add_mul, hz, Int.zero_mul]
        omega

def Poly.add (p q : Poly) : Poly := Poly.addF (p.length + q.length) p q

@[simp] theorem Poly.eval_add (ρ : Nat → Int) (p q : Poly) :
    Poly.eval ρ (Poly.add p q) = Poly.eval ρ p + Poly.eval ρ q := Poly.eval_addF ρ _ p q

/-- Multiply every coefficient by `k`. -/
def Poly.scaleN (k : Int) : Poly → Poly
  | [] => []
  | (m, c) :: p => (m, k * c) :: Poly.scaleN k p

theorem Poly.eval_scaleN (ρ : Nat → Int) (k : Int) :
    ∀ p, Poly.eval ρ (Poly.scaleN k p) = k * Poly.eval ρ p
  | [] => by simp [Poly.scaleN]
  | (m, c) :: p => by
    simp only [Poly.scaleN, Poly.eval_cons, Poly.eval_scaleN ρ k p, Int.mul_add, Int.mul_assoc]

def Poly.scale (k : Int) (p : Poly) : Poly := cond (intBeq k 0) [] (Poly.scaleN k p)

@[simp] theorem Poly.eval_scale (ρ : Nat → Int) (k : Int) (p : Poly) :
    Poly.eval ρ (Poly.scale k p) = k * Poly.eval ρ p := by
  unfold Poly.scale
  cases h : intBeq k 0
  · simp [Poly.eval_scaleN]
  · simp [intBeq_eq h]

def Poly.neg (p : Poly) : Poly := Poly.scaleN (-1) p

@[simp] theorem Poly.eval_neg (ρ : Nat → Int) (p : Poly) :
    Poly.eval ρ (Poly.neg p) = - Poly.eval ρ p := by
  simp [Poly.neg, Poly.eval_scaleN]

def Poly.sub (p q : Poly) : Poly := Poly.add p (Poly.neg q)

@[simp] theorem Poly.eval_sub (ρ : Nat → Int) (p q : Poly) :
    Poly.eval ρ (Poly.sub p q) = Poly.eval ρ p - Poly.eval ρ q := by
  simp [Poly.sub]; omega

def Poly.const (c : Int) : Poly := cond (intBeq c 0) [] [([], c)]

@[simp] theorem Poly.eval_const (ρ : Nat → Int) (c : Int) : Poly.eval ρ (Poly.const c) = c := by
  unfold Poly.const
  cases h : intBeq c 0
  · simp
  · simp [intBeq_eq h]

def Poly.atom (i : Nat) : Poly := [([i], 1)]

@[simp] theorem Poly.eval_atom (ρ : Nat → Int) (i : Nat) : Poly.eval ρ (Poly.atom i) = ρ i := by
  simp [Poly.atom]

/-- Insert an index into a sorted monomial. -/
def Mono.insert (i : Nat) : Mono → Mono
  | [] => [i]
  | j :: m => cond (Nat.ble i j) (i :: j :: m) (j :: Mono.insert i m)

theorem Mono.eval_insert (ρ : Nat → Int) (i : Nat) :
    ∀ m, Mono.eval ρ (Mono.insert i m) = ρ i * Mono.eval ρ m
  | [] => by simp [Mono.insert]
  | j :: m => by
    unfold Mono.insert
    cases Nat.ble i j
    · simp only [Bool.cond_false, Mono.eval_cons, Mono.eval_insert ρ i m]
      rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm (ρ j)]
    · simp

def Mono.mul : Mono → Mono → Mono
  | [], n => n
  | i :: m, n => Mono.insert i (Mono.mul m n)

theorem Mono.eval_mul (ρ : Nat → Int) :
    ∀ m n, Mono.eval ρ (Mono.mul m n) = Mono.eval ρ m * Mono.eval ρ n
  | [], n => by simp [Mono.mul]
  | i :: m, n => by simp [Mono.mul, Mono.eval_insert, Mono.eval_mul ρ m n, Int.mul_assoc]

/-- Add `c·m` to a sorted polynomial. -/
def Poly.addTerm (acc : Poly) (m : Mono) (c : Int) : Poly :=
  cond (intBeq c 0) acc (Poly.add acc [(m, c)])

theorem Poly.eval_addTerm (ρ : Nat → Int) (acc : Poly) (m : Mono) (c : Int) :
    Poly.eval ρ (Poly.addTerm acc m c) = Poly.eval ρ acc + c * Mono.eval ρ m := by
  unfold Poly.addTerm
  cases h : intBeq c 0
  · simp
  · simp [intBeq_eq h]

def Poly.mulTerm (m : Mono) (c : Int) : Poly → Poly → Poly
  | [], acc => acc
  | (n, d) :: q, acc => Poly.mulTerm m c q (Poly.addTerm acc (Mono.mul m n) (c * d))

theorem Poly.eval_mulTerm (ρ : Nat → Int) (m : Mono) (c : Int) :
    ∀ q acc, Poly.eval ρ (Poly.mulTerm m c q acc) =
      Poly.eval ρ acc + c * Mono.eval ρ m * Poly.eval ρ q
  | [], acc => by simp [Poly.mulTerm]
  | (n, d) :: q, acc => by
    simp only [Poly.mulTerm, Poly.eval_mulTerm ρ m c q, Poly.eval_addTerm, Mono.eval_mul,
      Poly.eval_cons]
    rw [Int.mul_add (c * Mono.eval ρ m)]
    have : c * d * (Mono.eval ρ m * Mono.eval ρ n) = c * Mono.eval ρ m * (d * Mono.eval ρ n) := by
      rw [Int.mul_assoc, Int.mul_assoc, ← Int.mul_assoc d, Int.mul_comm d, Int.mul_assoc]
    rw [this]; omega

def Poly.mulAcc : Poly → Poly → Poly → Poly
  | [], _, acc => acc
  | (m, c) :: p, q, acc => Poly.mulAcc p q (Poly.mulTerm m c q acc)

theorem Poly.eval_mulAcc (ρ : Nat → Int) :
    ∀ p q acc, Poly.eval ρ (Poly.mulAcc p q acc) = Poly.eval ρ acc + Poly.eval ρ p * Poly.eval ρ q
  | [], q, acc => by simp [Poly.mulAcc]
  | (m, c) :: p, q, acc => by
    simp only [Poly.mulAcc, Poly.eval_mulAcc ρ p q, Poly.eval_mulTerm, Poly.eval_cons, Int.add_mul]
    omega

def Poly.mul (p q : Poly) : Poly := Poly.mulAcc p q []

@[simp] theorem Poly.eval_mul (ρ : Nat → Int) (p q : Poly) :
    Poly.eval ρ (Poly.mul p q) = Poly.eval ρ p * Poly.eval ρ q := by
  simp [Poly.mul, Poly.eval_mulAcc]

/-- The constant polynomial `c`, if `p` is one. -/
def Poly.asConst? : Poly → Option Int
  | [] => some 0
  | [([], c)] => some c
  | _ => none

theorem Poly.eval_of_asConst {p : Poly} {c : Int} (h : p.asConst? = some c) (ρ : Nat → Int) :
    p.eval ρ = c := by
  match p, h with
  | [], h => simp [Poly.asConst?] at h; simp [h]
  | [([], d)], h => simp [Poly.asConst?] at h; simp [h]

/-! ## Atoms used -/

/-- Every atom of `p` is below `n`. -/
def Poly.below (n : Nat) (p : Poly) : Bool := p.all fun t => t.1.all fun i => Nat.blt i n

theorem Mono.eval_congr {ρ ρ' : Nat → Int} {n : Nat} (h : ∀ i, i < n → ρ i = ρ' i) :
    ∀ m : Mono, (m.all fun i => Nat.blt i n) = true → Mono.eval ρ m = Mono.eval ρ' m
  | [], _ => rfl
  | i :: m, hm => by
    simp only [List.all_cons, Bool.and_eq_true, Nat.blt_eq] at hm
    simp only [Mono.eval_cons, h i hm.1, Mono.eval_congr h m (by simpa using hm.2)]

theorem Poly.eval_congr {ρ ρ' : Nat → Int} {n : Nat} (h : ∀ i, i < n → ρ i = ρ' i) :
    ∀ p : Poly, p.below n = true → Poly.eval ρ p = Poly.eval ρ' p
  | [], _ => rfl
  | (m, c) :: p, hp => by
    simp only [Poly.below, List.all_cons, Bool.and_eq_true] at hp
    simp only [Poly.eval_cons, Mono.eval_congr h m hp.1, Poly.eval_congr h p hp.2]

/-! ## Division by a constant -/

/-- Split `p` as `L + k·Y` with every coefficient of `L` in `[0, k)` (for `k > 0`). -/
def Poly.splitMod (k : Int) : Poly → Poly × Poly
  | [] => ([], [])
  | (m, c) :: p =>
    let r := Poly.splitMod k p
    -- the remainder in `(-k/2, k/2]`, so that `-x` stays `-x` (not `(k-1)·x - k·x`)
    let big := intBle (k + 1) (2 * (c % k))
    let lo := cond big (c % k - k) (c % k)
    let hi := cond big (c / k + 1) (c / k)
    (cond (intBeq lo 0) r.1 ((m, lo) :: r.1), cond (intBeq hi 0) r.2 ((m, hi) :: r.2))

theorem Poly.eval_splitMod (ρ : Nat → Int) (k : Int) :
    ∀ p, Poly.eval ρ p = Poly.eval ρ (Poly.splitMod k p).1 + k * Poly.eval ρ (Poly.splitMod k p).2
  | [] => by simp [Poly.splitMod]
  | (m, c) :: p => by
    have ih := Poly.eval_splitMod ρ k p
    have hc : c = cond (intBle (k + 1) (2 * (c % k))) (c % k - k) (c % k) +
        k * cond (intBle (k + 1) (2 * (c % k))) (c / k + 1) (c / k) := by
      have := (Int.emod_add_mul_ediv c k).symm
      cases intBle (k + 1) (2 * (c % k)) <;> simp only [Bool.cond_true, Bool.cond_false] <;>
        (try rw [Int.mul_add]) <;> omega
    have key : ∀ (lo hi : Int) (r1 r2 : Poly), c = lo + k * hi →
        Poly.eval ρ p = Poly.eval ρ r1 + k * Poly.eval ρ r2 →
        c * Mono.eval ρ m + Poly.eval ρ p =
          (lo * Mono.eval ρ m + Poly.eval ρ r1) + k * (hi * Mono.eval ρ m + Poly.eval ρ r2) := by
      intro lo hi r1 r2 h1 h2
      rw [h1, h2, Int.add_mul, Int.mul_add, Int.mul_assoc]; omega
    have kc := key _ _ _ _ hc ih
    simp only [Poly.splitMod]
    generalize cond (intBle (k + 1) (2 * (c % k))) (c % k - k) (c % k) = lo at kc ⊢
    generalize cond (intBle (k + 1) (2 * (c % k))) (c / k + 1) (c / k) = hi at kc ⊢
    cases h1 : intBeq lo 0 <;> cases h2 : intBeq hi 0 <;>
      simp only [Bool.cond_true, Bool.cond_false, Poly.eval_cons]
    · omega
    · have := intBeq_eq h2; rw [this] at kc; simp only [Int.zero_mul, Int.zero_add] at kc; omega
    · have := intBeq_eq h1; rw [this] at kc; simp only [Int.zero_mul, Int.zero_add] at kc; omega
    · have e1 := intBeq_eq h1; have e2 := intBeq_eq h2
      rw [e1, e2] at kc; simp only [Int.zero_mul, Int.zero_add] at kc; omega

/-- All coefficients are divisible by `g`. -/
def Poly.dvdAll (g : Int) (p : Poly) : Bool := p.all fun t => intBeq (t.2 % g) 0

theorem Poly.eval_of_dvdAll (ρ : Nat → Int) (g : Int) :
    ∀ p, Poly.dvdAll g p = true → Poly.eval ρ p = g * Poly.eval ρ (p.map fun t => (t.1, t.2 / g))
  | [], _ => by simp
  | (m, c) :: p, h => by
    simp only [Poly.dvdAll, List.all_cons, Bool.and_eq_true] at h
    have hc := intBeq_eq h.1
    have ih := Poly.eval_of_dvdAll ρ g p h.2
    simp only [List.map_cons, Poly.eval_cons, ih, Int.mul_add]
    have : c = g * (c / g) := by
      have := Int.emod_add_mul_ediv c g; rw [hc] at this; omega
    conv => lhs; rw [this]
    rw [Int.mul_assoc]

/-- The gcd of the coefficients. -/
def Poly.gcdCoeffs : Poly → Nat
  | [] => 0
  | (_, c) :: p => Nat.gcd c.natAbs (Poly.gcdCoeffs p)

end Janus.Ring
