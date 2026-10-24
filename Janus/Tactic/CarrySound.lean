import Janus.Tactic.CarryDefs

/-!
# Soundness of the carry-chain checker

`check_sound`: if `check ubs tbl ivs a b = true` and the environment satisfies the bounds
`ubs`, then `a.eval env = b.eval env`. The quotient atoms are given their meaning by `extend`
(atom `n + j` is `tbl[j].1 / tbl[j].2`, evaluated over the earlier atoms).
-/

namespace Janus.Carry

open Janus.Ring

/-! ## Environments and bounds -/

/-- Every atom with a bound `some u` is at most `u` (and the lists have the same length). -/
def BoundsOK : List Nat → List (Option Nat) → Prop
  | [], [] => True
  | _ :: es, none :: us => BoundsOK es us
  | e :: es, some u :: us => e ≤ u ∧ BoundsOK es us
  | _, _ => False

theorem BoundsOK.le : ∀ {env : List Nat} {ubs : List (Option Nat)} {i u : Nat},
    BoundsOK env ubs → lnth ubs i = some (some u) → nth env i ≤ u
  | [], [], _, _, _, h => by simp [lnth] at h
  | _ :: es, none :: us, 0, _, _, h => by simp [lnth] at h
  | _ :: es, none :: us, i + 1, u, hb, h => BoundsOK.le (env := es) (ubs := us) hb h
  | e :: es, some u' :: us, 0, u, hb, h => by
    simp [lnth] at h; subst h; exact hb.1
  | e :: es, some u' :: us, i + 1, u, hb, h => BoundsOK.le (env := es) (ubs := us) hb.2 h
  | [], _ :: _, _, _, hb, _ => hb.elim
  | _ :: _, [], _, _, hb, _ => hb.elim

theorem lnth_isSome {α : Type} : ∀ (l : List α) (i : Nat), i < l.length → ∃ x, lnth l i = some x
  | [], _, h => by simp at h
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, i + 1, h => lnth_isSome xs i (by simp at h; omega)

theorem ivNth_ge : ∀ (l : List Iv) (i : Nat), l.length ≤ i → ivNth l i = Iv.top
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: xs, i + 1, h => ivNth_ge xs i (by simp at h; omega)

def rho0 (env : List Nat) : Nat → Int := fun i => (nth env i : Int)

/-- The values of the atoms: the environment, then the quotient atoms of the table. -/
def extend (ρ : Nat → Int) (n : Nat) : List (Poly × Nat) → Nat → Int
  | [] => ρ
  | (L, k) :: t => extend (fun i => if i = n then L.eval ρ / (k : Int) else ρ i) (n + 1) t

theorem extend_lt : ∀ (ρ : Nat → Int) (n : Nat) (t : List (Poly × Nat)) (i : Nat), i < n →
    extend ρ n t i = ρ i
  | _, _, [], _, _ => rfl
  | ρ, n, (L, k) :: t, i, h => by
    simp only [extend]
    rw [extend_lt _ (n + 1) t i (by omega)]
    simp [Nat.ne_of_lt h]

theorem extend_at : ∀ (ρ : Nat → Int) (n : Nat) (t : List (Poly × Nat)) (j : Nat) (L : Poly)
    (k : Nat), lnth t j = some (L, k) → L.below (n + j) = true →
    extend ρ n t (n + j) = L.eval (extend ρ n t) / (k : Int)
  | _, _, [], _, _, _, h, _ => by simp [lnth] at h
  | ρ, n, (L', k') :: t, 0, L, k, h, hb => by
    simp [lnth] at h
    rw [← h.1] at hb ⊢; rw [← h.2]
    simp only [extend]
    rw [extend_lt _ (n + 1) t (n + 0) (by omega)]
    simp only [Nat.add_zero, ite_true]
    congr 1
    apply Poly.eval_congr (n := n) _ L' (by simpa using hb)
    intro i hi
    rw [extend_lt _ (n + 1) t i (by omega)]
    simp [Nat.ne_of_lt hi]
  | ρ, n, (L', k') :: t, j + 1, L, k, h, hb => by
    simp only [lnth] at h
    simp only [extend]
    have := extend_at (fun i => if i = n then L'.eval ρ / (k' : Int) else ρ i) (n + 1) t j L k h
      (by rw [show n + 1 + j = n + (j + 1) by omega]; exact hb)
    rw [show n + (j + 1) = n + 1 + j by omega, this]

/-! ## Intervals -/

theorem obeq_eq : ∀ {a b : Option Int}, obeq a b = true → a = b
  | some a, some b, h => by simp [obeq] at h; rw [intBeq_eq h]
  | none, none, _ => rfl
  | some _, none, h => by simp [obeq] at h
  | none, some _, h => by simp [obeq] at h

theorem Iv.beq_eq {I J : Iv} (h : Iv.beq I J = true) : I = J := by
  cases I; cases J
  simp only [Iv.beq, Bool.and_eq_true] at h
  rw [obeq_eq h.1, obeq_eq h.2]

theorem Iv.mem_const (c : Int) : (Iv.const c).mem c :=
  ⟨fun l h => by simp [Iv.const] at h; omega, fun l h => by simp [Iv.const] at h; omega⟩

theorem Iv.mem_add {I J : Iv} {a b : Int} (ha : I.mem a) (hb : J.mem b) : (I.add J).mem (a + b) := by
  constructor
  · intro l hl
    simp only [Iv.add] at hl
    cases h1 : I.lo <;> cases h2 : J.lo <;> simp [h1, h2, oadd] at hl
    have := ha.1 _ h1; have := hb.1 _ h2; omega
  · intro l hl
    simp only [Iv.add] at hl
    cases h1 : I.hi <;> cases h2 : J.hi <;> simp [h1, h2, oadd] at hl
    have := ha.2 _ h1; have := hb.2 _ h2; omega

theorem Iv.mem_neg {I : Iv} {a : Int} (ha : I.mem a) : I.neg.mem (-a) := by
  constructor
  · intro l hl
    simp only [Iv.neg] at hl
    cases h1 : I.hi <;> simp [h1, omap] at hl
    have := ha.2 _ h1; omega
  · intro l hl
    simp only [Iv.neg] at hl
    cases h1 : I.lo <;> simp [h1, omap] at hl
    have := ha.1 _ h1; omega

theorem Iv.mem_sub {I J : Iv} {a b : Int} (ha : I.mem a) (hb : J.mem b) : (I.sub J).mem (a - b) := by
  rw [Int.sub_eq_add_neg]; exact Iv.mem_add ha (Iv.mem_neg hb)

theorem Iv.mem_scale {I : Iv} {a : Int} (c : Int) (ha : I.mem a) : (I.scale c).mem (c * a) := by
  unfold Iv.scale
  cases hc : intNonneg c
  · have hc' : c < 0 := by
      cases c with
      | ofNat _ => simp [intNonneg] at hc
      | negSucc _ => exact Int.negSucc_lt_zero _
    constructor
    · intro l hl
      cases h1 : I.hi <;> simp [h1, omap] at hl
      subst hl; exact Int.mul_le_mul_of_nonpos_left (by omega) (ha.2 _ h1)
    · intro l hl
      cases h1 : I.lo <;> simp [h1, omap] at hl
      subst hl; exact Int.mul_le_mul_of_nonpos_left (by omega) (ha.1 _ h1)
  · have hc' := intNonneg_le hc
    constructor
    · intro l hl
      cases h1 : I.lo <;> simp [h1, omap] at hl
      subst hl; exact Int.mul_le_mul_of_nonneg_left (ha.1 _ h1) hc'
    · intro l hl
      cases h1 : I.hi <;> simp [h1, omap] at hl
      subst hl; exact Int.mul_le_mul_of_nonneg_left (ha.2 _ h1) hc'

theorem Iv.mem_mul {I J : Iv} {a b : Int} (ha : I.mem a) (hb : J.mem b) : (I.mul J).mem (a * b) := by
  unfold Iv.mul
  cases h1 : I.lo with
  | none => exact Iv.mem_top _
  | some la =>
    cases h2 : J.lo with
    | none => exact Iv.mem_top _
    | some lb =>
      simp only
      cases hn : (intNonneg la && intNonneg lb)
      · exact Iv.mem_top _
      · simp only [Bool.and_eq_true] at hn
        have hla := intNonneg_le hn.1
        have hlb := intNonneg_le hn.2
        have hal := ha.1 _ h1
        have hbl := hb.1 _ h2
        simp only [Bool.cond_true]
        constructor
        · intro l hl
          simp at hl; subst hl
          exact Int.mul_le_mul hal hbl hlb (by omega)
        · intro l hl
          cases h3 : I.hi <;> cases h4 : J.hi <;> simp [h3, h4] at hl
          subst hl
          have := ha.2 _ h3; have := hb.2 _ h4
          exact Int.mul_le_mul (by assumption) (by assumption) (by omega) (by omega)

theorem Iv.mem_inter {I J : Iv} {a : Int} (h1 : I.mem a) (h2 : J.mem a) : (I.inter J).mem a := by
  constructor
  · intro l hl
    simp only [Iv.inter] at hl
    cases e1 : I.lo <;> cases e2 : J.lo <;> simp only [e1, e2, omax] at hl
    · simp at hl
    · exact h2.1 _ (e2.trans hl)
    · simp at hl; subst hl; exact h1.1 _ e1
    · rename_i x y
      cases hxy : intBle x y <;> simp [hxy] at hl <;> subst hl
      · exact h1.1 _ e1
      · exact h2.1 _ e2
  · intro l hl
    simp only [Iv.inter] at hl
    cases e1 : I.hi <;> cases e2 : J.hi <;> simp only [e1, e2, omin] at hl
    · simp at hl
    · exact h2.2 _ (e2.trans hl)
    · simp at hl; subst hl; exact h1.2 _ e1
    · rename_i x y
      cases hxy : intBle x y <;> simp [hxy] at hl <;> subst hl
      · exact h2.2 _ e2
      · exact h1.2 _ e1

theorem Iv.mem_divK {I : Iv} {a k : Int} (hk : 0 < k) (ha : I.mem a) : (I.divK k).mem (a / k) := by
  constructor
  · intro l hl
    simp only [Iv.divK] at hl
    cases e : I.lo <;> simp [e, omap] at hl
    subst hl; exact Int.ediv_le_ediv hk (ha.1 _ e)
  · intro l hl
    simp only [Iv.divK] at hl
    cases e : I.hi <;> simp [e, omap] at hl
    subst hl; exact Int.ediv_le_ediv hk (ha.2 _ e)

theorem Iv.within_spec {I : Iv} {a k : Int} (h : I.within k = true) (ha : I.mem a) :
    0 ≤ a ∧ a < k := by
  rcases I with ⟨_ | l, _ | u⟩ <;> simp only [Iv.within, Bool.false_eq_true] at h
  simp only [Bool.and_eq_true] at h
  have := intNonneg_le h.1; have := intBle_le h.2
  have := ha.1 _ rfl; have := ha.2 _ rfl
  omega

theorem Iv.ble_spec {I J : Iv} {a b : Int} (h : I.ble J = true) (ha : I.mem a) (hb : J.mem b) :
    a ≤ b := by
  rcases I with ⟨_, _ | u⟩ <;> rcases J with ⟨_ | l, _⟩ <;>
    simp only [Iv.ble, Bool.false_eq_true] at h
  have := intBle_le h; have := ha.2 _ rfl; have := hb.1 _ rfl
  omega

theorem monoIv_sound {σ : Nat → Iv} {ρ : Nat → Int} {N : Nat}
    (hσ : ∀ i, i < N → (σ i).mem (ρ i)) :
    ∀ m : Mono, (m.all fun i => Nat.blt i N) = true → (monoIv σ m).mem (Mono.eval ρ m)
  | [], _ => Iv.mem_const 1
  | i :: m, hm => by
    simp only [List.all_cons, Bool.and_eq_true, Nat.blt_eq] at hm
    exact Iv.mem_mul (hσ i hm.1) (monoIv_sound hσ m (by simpa using hm.2))

theorem polyIv_sound {σ : Nat → Iv} {ρ : Nat → Int} {N : Nat}
    (hσ : ∀ i, i < N → (σ i).mem (ρ i)) :
    ∀ p : Poly, p.below N = true → (polyIv σ p).mem (Poly.eval ρ p)
  | [], _ => Iv.mem_const 0
  | (m, c) :: p, hp => by
    simp only [Poly.below, List.all_cons, Bool.and_eq_true] at hp
    exact Iv.mem_add (Iv.mem_scale c (monoIv_sound hσ m hp.1)) (polyIv_sound hσ p hp.2)

/-- `polyIv_sound` when every atom has a sound interval. -/
theorem polyIv_sound' {σ : Nat → Iv} {ρ : Nat → Int} (hσ : ∀ i, (σ i).mem (ρ i)) (p : Poly) :
    (polyIv σ p).mem (Poly.eval ρ p) := by
  have hm : ∀ (N : Nat) (m : Mono), (∀ i ∈ m, i < N) → (monoIv σ m).mem (Mono.eval ρ m) := by
    intro N m h
    induction m with
    | nil => exact Iv.mem_const 1
    | cons i m ih =>
      exact Iv.mem_mul (hσ i) (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))
  induction p with
  | nil => exact Iv.mem_const 0
  | cons t p ih =>
    obtain ⟨m, c⟩ := t
    have := hm (m.foldr max 0 + 1) m (by
      intro i hi
      have : i ≤ m.foldr max 0 := by
        clear ih hm
        induction m with
        | nil => simp at hi
        | cons j m ih2 =>
          simp only [List.foldr_cons]
          rcases List.mem_cons.mp hi with rfl | hi
          · exact Nat.le_max_left _ _
          · exact Nat.le_trans (ih2 hi) (Nat.le_max_right _ _)
      omega)
    exact Iv.mem_add (Iv.mem_scale c this) ih

/-! ## The certificate -/

/-! ### Trees -/

theorem lnth_evens {α : Type} : ∀ (l : List α) (m : Nat), lnth (evens l) m = lnth l (2 * m)
  | [], _ => rfl
  | [_], 0 => rfl
  | [_], m + 1 => by simp [evens, lnth]; rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]; rfl
  | _ :: _ :: _, 0 => rfl
  | _ :: _ :: xs, m + 1 => by
    simp only [evens, lnth]
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, lnth_evens xs m]; rfl

theorem lnth_odds {α : Type} : ∀ (l : List α) (m : Nat), lnth (odds l) m = lnth l (2 * m + 1)
  | [], _ => rfl
  | [_], m => by simp [odds, lnth]
  | _ :: _ :: _, 0 => rfl
  | _ :: _ :: xs, m + 1 => by
    simp only [odds, lnth]
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
    exact lnth_odds xs m

theorem evens_length {α : Type} : ∀ l : List α, (evens l).length ≤ l.length
  | [] => Nat.le_refl _
  | [_] => Nat.le_refl _
  | _ :: _ :: xs => by simp only [evens, List.length_cons]; have := evens_length xs; omega

theorem odds_length {α : Type} : ∀ l : List α, (odds l).length ≤ l.length
  | [] => Nat.le_refl _
  | [_] => by simp [odds]
  | _ :: _ :: xs => by simp only [odds, List.length_cons]; have := odds_length xs; omega

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem beq_true_of_eq {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h; exact Nat.beq_refl a

theorem BT.get_ofListF {α : Type} (d : α) : ∀ (f : Nat) (l : List α), l.length ≤ f →
    ∀ i, (BT.ofListF f l).get d i = (lnth l i).getD d
  | 0, [], _, i => by simp [BT.ofListF, BT.get, lnth]
  | 0, _ :: _, h, _ => by simp at h
  | f + 1, [], _, i => by simp [BT.ofListF, BT.get, lnth]
  | f + 1, x :: xs, h, i => by
    simp only [List.length_cons] at h
    obtain ⟨m, rfl | rfl⟩ : ∃ m, i = 2 * m ∨ i = 2 * m + 1 := ⟨i / 2, by omega⟩
    · cases m with
      | zero => simp [BT.ofListF, BT.get, lnth]
      | succ m =>
        have h1 : Nat.beq (2 * (m + 1)) 0 = false := beq_false_of_ne (by omega)
        have h2 : Nat.beq (2 * (m + 1) % 2) 1 = false := beq_false_of_ne (by omega)
        have h3 : 2 * (m + 1) / 2 - 1 = m := by omega
        simp only [BT.ofListF, BT.get, h1, h2, h3, Bool.cond_false]
        rw [BT.get_ofListF d f (odds xs) (Nat.le_trans (odds_length xs) (by omega)) m, lnth_odds,
          show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
        rfl
    · have h1 : Nat.beq (2 * m + 1) 0 = false := beq_false_of_ne (by omega)
      have h2 : Nat.beq ((2 * m + 1) % 2) 1 = true := beq_true_of_eq (by omega)
      have h3 : (2 * m + 1) / 2 = m := by omega
      simp only [BT.ofListF, BT.get, h1, h2, h3, Bool.cond_false, Bool.cond_true]
      rw [BT.get_ofListF d f (evens xs) (Nat.le_trans (evens_length xs) (by omega)) m, lnth_evens]
      rfl

theorem BT.get_ofList {α : Type} (d : α) (l : List α) (i : Nat) :
    (BT.ofList l).get d i = (lnth l i).getD d := BT.get_ofListF d _ l (Nat.le_refl _) i

theorem ivNth_eq : ∀ (l : List Iv) (i : Nat), ivNth l i = (lnth l i).getD Iv.top
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => ivNth_eq xs i

theorem ivNth_ivDrop : ∀ (l : List Iv) (n j : Nat), ivNth (ivDrop l n) j = ivNth l (n + j)
  | l, 0, j => by simp [ivDrop]
  | [], n + 1, j => by simp [ivDrop, ivNth_eq, lnth]
  | _ :: xs, n + 1, j => by
    simp only [ivDrop]; rw [ivNth_ivDrop xs n j, show n + 1 + j = (n + j) + 1 by omega]; rfl

theorem lnth_map_some {α : Type} : ∀ (l : List α) (i : Nat),
    (lnth (l.map some) i).getD none = lnth l i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => lnth_map_some xs i

theorem varsOK_spec : ∀ (ivs : List Iv) (ubs : List (Option Nat)),
    varsOK ivs ubs = true → ∀ i u, lnth ubs i = some u →
    ivNth ivs i = ⟨some 0, match u with | some u => some (u : Int) | none => none⟩
  | _, [], _, i, u, h => by simp [lnth] at h
  | [], _ :: _, hv, _, _, _ => by simp [varsOK] at hv
  | iv :: ivs, v :: us, hv, 0, u, h => by
    simp only [lnth, Option.some.injEq] at h; subst h
    simp only [varsOK, Bool.and_eq_true] at hv
    exact Iv.beq_eq hv.1
  | iv :: ivs, v :: us, hv, i + 1, u, h => by
    simp only [varsOK, Bool.and_eq_true] at hv
    simp only [lnth] at h
    exact varsOK_spec ivs us hv.2 i u h

theorem tblOK_spec (n : Nat) (σ : Nat → Iv) : ∀ (rest : List Iv) (t : List (Poly × Nat)) (j0 : Nat),
    tblOK n σ rest t j0 = true → ∀ j L k, lnth t j = some (L, k) →
    0 < k ∧ L.below (n + (j0 + j)) = true ∧ ivNth rest j = (polyIv σ L).divK k
  | _, [], _, _, j, _, _, h => by simp [lnth] at h
  | [], _ :: _, _, ht, _, _, _, _ => by simp [tblOK] at ht
  | iv :: rest, (L', k') :: t, j0, ht, 0, L, k, h => by
    simp [lnth] at h; obtain ⟨rfl, rfl⟩ := h
    simp only [tblOK, Bool.and_eq_true, Nat.blt_eq] at ht
    exact ⟨ht.1.1.1, by simpa using ht.1.1.2, by simpa [ivNth] using Iv.beq_eq ht.1.2⟩
  | iv :: rest, (L', k') :: t, j0, ht, j + 1, L, k, h => by
    simp only [tblOK, Bool.and_eq_true] at ht
    simp only [lnth] at h
    rw [show j0 + (j + 1) = (j0 + 1) + j by omega]
    exact tblOK_spec n σ rest t (j0 + 1) ht.2 j L k h

theorem lookup_spec : ∀ (L : Poly) (k : Nat) (t : List (Poly × Nat)) (j0 j : Nat),
    lookup L k t j0 = some j → ∃ j', j = j0 + j' ∧ lnth t j' = some (L, k)
  | _, _, [], _, _, h => by simp [lookup] at h
  | L, k, (L', k') :: t, j0, j, h => by
    simp only [lookup] at h
    cases hc : (Nat.beq k k' && Poly.beq L L')
    · rw [hc] at h
      obtain ⟨j', rfl, h'⟩ := lookup_spec L k t (j0 + 1) j h
      exact ⟨j' + 1, by omega, h'⟩
    · rw [hc] at h
      simp only [Bool.and_eq_true, Nat.beq_eq] at hc
      simp only [Bool.cond_true, Option.some.injEq] at h
      refine ⟨0, by omega, ?_⟩
      simp [lnth, hc.1, Poly.beq_eq hc.2]

/-- What the checker may assume about the atom values `ρ`. -/
structure Sem (c : Ctx) (env : List Nat) (ρ : Nat → Int) : Prop where
  iv : ∀ i, (ivNth c.ivs i).mem (ρ i)
  ivt : c.ivt = BT.ofList c.ivs
  tbt : c.tbt = BT.ofList (c.tbl.map some)
  var : ∀ i, i < c.n → ρ i = (nth env i : Int)
  tbl : ∀ j L k, lnth c.tbl j = some (L, k) → 0 < k ∧ ρ (c.n + j) = L.eval ρ / (k : Int)

theorem sem_of_check {env : List Nat} {ubs : List (Option Nat)} {tbl : List (Poly × Nat)}
    {ivs : List Iv} (hb : BoundsOK env ubs) (hc : certOK ubs tbl ivs = true) :
    Sem { n := ubs.length, tbl := tbl, ivs := ivs } env (extend (rho0 env) ubs.length tbl) := by
  unfold certOK at hc
  simp only [Bool.and_eq_true, Nat.beq_eq] at hc
  obtain ⟨⟨hlen, hv⟩, ht⟩ := hc
  have hσ : ((BT.ofList ivs).get Iv.top) = ivNth ivs := by
    funext i; rw [BT.get_ofList, ivNth_eq]
  rw [hσ] at ht
  let n := ubs.length
  let ρ := extend (rho0 env) n tbl
  have hvar : ∀ i, i < n → ρ i = (nth env i : Int) := fun i hi => extend_lt _ _ _ _ hi
  have htbl : ∀ j L k, lnth tbl j = some (L, k) → 0 < k ∧ ρ (n + j) = L.eval ρ / (k : Int) := by
    intro j L k h
    obtain ⟨hk, hbl, -⟩ := tblOK_spec n (ivNth ivs) _ tbl 0 ht j L k h
    exact ⟨hk, extend_at _ _ _ _ _ _ h (by simpa using hbl)⟩
  refine ⟨?_, rfl, rfl, hvar, htbl⟩
  -- strong induction on the atom index
  have key : ∀ N i, i < N → (ivNth ivs i).mem (ρ i) := by
    intro N
    induction N with
    | zero => intro i h; omega
    | succ N ih =>
      intro i hi
      by_cases h1 : i < n
      · obtain ⟨u, hu⟩ := lnth_isSome ubs i h1
        have hiv := varsOK_spec ivs ubs hv i u hu
        rw [hiv, hvar i h1]
        constructor
        · intro l hl; simp at hl; subst hl; exact Int.natCast_nonneg _
        · intro l hl
          cases u with
          | none => simp at hl
          | some u =>
            simp at hl; subst hl
            exact Int.ofNat_le.mpr (BoundsOK.le hb hu)
      · by_cases h2 : i < n + tbl.length
        · obtain ⟨⟨L, k⟩, hj⟩ := lnth_isSome tbl (i - n) (by omega)
          obtain ⟨hk, hbl, hiv⟩ := tblOK_spec n (ivNth ivs) _ tbl 0 ht (i - n) L k hj
          rw [Nat.zero_add, show n + (i - n) = i by omega] at hbl
          rw [ivNth_ivDrop, show n + (i - n) = i by omega] at hiv
          have hval := (htbl (i - n) L k hj).2
          rw [show n + (i - n) = i by omega] at hval
          rw [hiv, hval]
          exact Iv.mem_divK (by omega) (polyIv_sound (N := i)
            (fun i' hi' => ih i' (by omega)) L hbl)
        · rw [ivNth_ge ivs i (by omega)]; exact Iv.mem_top _
  exact fun i => key (i + 1) i (Nat.lt_succ_self i)

theorem Sem.iv' {c : Ctx} {env : List Nat} {ρ : Nat → Int} (hs : Sem c env ρ) (i : Nat) :
    (c.iv i).mem (ρ i) := by
  unfold Ctx.iv; rw [hs.ivt, BT.get_ofList, ← ivNth_eq]; exact hs.iv i

/-! ## The checker is sound -/

theorem qatom_spec {c : Ctx} {env : List Nat} {ρ : Nat → Int} (hs : Sem c env ρ) {i : Nat}
    {L : Poly} {k : Nat} (h : qatom c i = some (L, k)) : 0 < k ∧ ρ i = L.eval ρ / (k : Int) := by
  unfold qatom at h
  cases hb : Nat.ble c.n i
  · rw [hb] at h; simp at h
  · rw [hb] at h
    simp only [Bool.cond_true] at h
    rw [hs.tbt, BT.get_ofList, lnth_map_some] at h
    have := hs.tbl (i - c.n) L k h
    have hi : c.n + (i - c.n) = i := by have := Nat.le_of_ble_eq_true hb; omega
    rw [hi] at this; exact this

theorem findPos_spec {c : Ctx} {k : Nat} {e : Int} :
    ∀ {p : Poly} {j : Nat} {Lj : Poly}, findPos c k e p = some (j, Lj) → qatom c j = some (Lj, k)
  | [], _, _, h => by simp [findPos] at h
  | (m, e') :: p, j, Lj, h => by
    unfold findPos at h
    split at h
    · rename_i j'
      cases h1 : intBeq e e'
      · rw [h1] at h; exact findPos_spec h
      · rw [h1] at h
        simp only [Bool.cond_true] at h
        cases hq : qatom c j' with
        | none => rw [hq] at h; exact findPos_spec h
        | some x =>
          obtain ⟨Lj', kj⟩ := x
          rw [hq] at h
          simp only at h
          cases hk : Nat.beq k kj
          · rw [hk] at h; exact findPos_spec h
          · rw [hk] at h
            simp only [Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [hq, Nat.eq_of_beq_eq_true hk]
    · exact findPos_spec h

theorem findPair_spec {c : Ctx} {all : Poly} :
    ∀ {p : Poly} {i : Nat} {Li : Poly} {j : Nat} {Lj : Poly} {k : Nat} {e : Int},
      findPair c all p = some (i, Li, j, Lj, k, e) →
      qatom c i = some (Li, k) ∧ qatom c j = some (Lj, k)
  | [], _, _, _, _, _, _, h => by simp [findPair] at h
  | (m, d) :: p, i, Li, j, Lj, k, e, h => by
    unfold findPair at h
    split at h
    · rename_i i'
      cases h1 : intNonneg d
      · rw [h1] at h
        simp only [Bool.cond_false] at h
        cases hq : qatom c i' with
        | none => rw [hq] at h; exact findPair_spec h
        | some x =>
          obtain ⟨Li', k'⟩ := x
          rw [hq] at h
          simp only at h
          cases hp : findPos c k' (-d) all with
          | none => rw [hp] at h; exact findPair_spec h
          | some y =>
            obtain ⟨j', Lj'⟩ := y
            rw [hp] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
            exact ⟨hq, findPos_spec hp⟩
      · rw [h1] at h; exact findPair_spec h
    · exact findPair_spec h

/-- `a/k - b/k` is `(a-b)/k` or one more. -/
theorem ediv_sub_ediv (a b k : Int) (hk : 0 < k) :
    (a - b) / k ≤ a / k - b / k ∧ a / k - b / k ≤ (a - b) / k + 1 := by
  have h1 := Int.emod_add_mul_ediv a k
  have h2 := Int.emod_add_mul_ediv b k
  have h3 := Int.emod_add_mul_ediv (a - b) k
  have r1 := Int.emod_nonneg a (show k ≠ 0 by omega)
  have r2 := Int.emod_nonneg b (show k ≠ 0 by omega)
  have r3 := Int.emod_nonneg (a - b) (show k ≠ 0 by omega)
  have s1 := Int.emod_lt_of_pos a hk
  have s2 := Int.emod_lt_of_pos b hk
  have s3 := Int.emod_lt_of_pos (a - b) hk
  -- k·X = r3 - r1 + r2 with X = a/k - b/k - (a-b)/k, so -k < k·X < 2k
  have hX : k * (a / k - b / k - (a - b) / k) = (a - b) % k - a % k + b % k := by
    rw [Int.mul_sub, Int.mul_sub]; omega
  have lo : k * (-1) < k * (a / k - b / k - (a - b) / k) := by rw [hX]; omega
  have hi : k * (a / k - b / k - (a - b) / k) < k * 2 := by rw [hX]; omega
  have := Int.lt_of_mul_lt_mul_left lo (by omega)
  have := Int.lt_of_mul_lt_mul_left hi (by omega)
  omega

theorem pairIv_mem {c : Ctx} {env : List Nat} {ρ : Nat → Int} (hs : Sem c env ρ)
    {i j : Nat} {Li Lj : Poly} {k : Nat} (hi : qatom c i = some (Li, k))
    (hj : qatom c j = some (Lj, k)) : (pairIv c Li Lj k).mem (ρ j - ρ i) := by
  obtain ⟨hk, ei⟩ := qatom_spec hs hi
  obtain ⟨-, ej⟩ := qatom_spec hs hj
  have hI := polyIv_sound' hs.iv' (Lj.sub Li)
  rw [Poly.eval_sub] at hI
  have hk' : (0 : Int) < k := by omega
  obtain ⟨b1, b2⟩ := ediv_sub_ediv (Lj.eval ρ) (Li.eval ρ) k hk'
  rw [ei, ej]
  constructor
  · intro l hl
    simp only [pairIv] at hl
    cases e : (polyIv (c.iv) (Lj.sub Li)).lo <;> rw [e] at hl <;> simp [omap] at hl
    subst hl
    have := Int.ediv_le_ediv hk' (hI.1 _ e)
    omega
  · intro l hl
    simp only [pairIv] at hl
    cases e : (polyIv (c.iv) (Lj.sub Li)).hi <;> rw [e] at hl <;> simp [omap] at hl
    subst hl
    have := Int.ediv_le_ediv hk' (hI.2 _ e)
    omega

theorem civF_sound {c : Ctx} {env : List Nat} {ρ : Nat → Int} (hs : Sem c env ρ) :
    ∀ (f : Nat) (p : Poly), (civF c f p).mem (p.eval ρ)
  | 0, p => polyIv_sound' hs.iv' p
  | f + 1, p => by
    unfold civF
    split
    · rename_i i Li j Lj k e hf
      obtain ⟨hi, hj⟩ := findPair_spec hf
      apply Iv.mem_inter (polyIv_sound' hs.iv' p)
      have hr := civF_sound hs f (p.sub (((Poly.atom j).sub (Poly.atom i)).scale e))
      have hpair := Iv.mem_scale e (pairIv_mem hs hi hj)
      have := Iv.mem_add hr hpair
      simp only [Poly.eval_sub, Poly.eval_scale, Poly.eval_atom] at this
      rwa [Int.sub_add_cancel] at this
    · exact polyIv_sound' hs.iv' p

theorem civ_sound {c : Ctx} {env : List Nat} {ρ : Nat → Int} (hs : Sem c env ρ) (p : Poly) :
    (civ c p).mem (p.eval ρ) := civF_sound hs _ p

theorem refine_mem {c : Ctx} {env : List Nat} {ρ : Nat → Int} (hs : Sem c env ρ) {p : Poly}
    {I : Iv} {v : Int} (k : Int) (hp : p.eval ρ = v) (hI : I.mem v) : (refine c p I k).mem v := by
  unfold refine
  cases I.within k
  · exact Iv.mem_inter hI (hp ▸ civ_sound hs p)
  · exact hI

theorem divmod_sound {c : Ctx} {env : List Nat} {ρ : Nat → Int} (hs : Sem c env ρ)
    {p : Poly} {J : Iv} {k : Nat} {d r : Poly} {v : Int} (hk : 0 < k)
    (h : divmod c p J k = some (d, r)) (hp : p.eval ρ = v) (hJ : J.mem v) :
    d.eval ρ = v / (k : Int) ∧ r.eval ρ = v % (k : Int) := by
  have hk' : (k : Int) ≠ 0 := by omega
  have hsplit := Poly.eval_splitMod ρ (k : Int) p
  rw [hp] at hsplit
  generalize hL : (p.splitMod (k : Int)).1 = L at hsplit
  generalize hY : (p.splitMod (k : Int)).2 = Y at hsplit
  have hv : v = L.eval ρ + (k : Int) * Y.eval ρ := hsplit
  unfold divmod at h
  simp only [hL, hY] at h
  have hdiv : v / (k : Int) = L.eval ρ / (k : Int) + Y.eval ρ := by
    rw [hv]; exact Int.add_mul_ediv_left _ _ hk'
  have hmod : v % (k : Int) = v - (k : Int) * (v / (k : Int)) := Int.emod_def _ _
  cases hw : (cond Y.isNil J (civ c L)).within (k : Int)
  · rw [hw] at h
    simp only [Bool.cond_false] at h
    cases hl : lookup L k c.tbl 0 with
    | none => rw [hl] at h; simp at h
    | some j =>
      rw [hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨j', rfl, hj⟩ := lookup_spec L k c.tbl 0 j hl
      have hat := (hs.tbl j' L k hj).2
      rw [Nat.zero_add]
      simp only [Poly.eval_add, Poly.eval_atom, Poly.eval_sub, Poly.eval_scale]
      rw [hat]
      constructor
      · rw [hdiv]
      · rw [hmod, hdiv, hv, Int.mul_add, Int.mul_comm (k : Int) (L.eval ρ / (k : Int))]; omega
  · rw [hw] at h
    simp only [Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hLm : (cond Y.isNil J (civ c L)).mem (L.eval ρ) := by
      cases hn : Y.isNil
      · exact civ_sound hs L
      · simp only [Bool.cond_true]
        have := Poly.eval_of_isNil hn ρ
        rw [this, Int.mul_zero, Int.add_zero] at hv
        rw [← hv]; exact hJ
    obtain ⟨h0, h1⟩ := Iv.within_spec hw hLm
    have hz : L.eval ρ / (k : Int) = 0 := Int.ediv_eq_zero_of_lt h0 h1
    constructor
    · rw [hdiv, hz, Int.zero_add]
    · rw [hmod, hdiv, hz, Int.zero_add, hv]; omega

theorem geb_eq_div {a k : Nat} (hk : 0 < k) (h : a < 2 * k) : (decide (k ≤ a)).toNat = a / k := by
  by_cases hka : k ≤ a
  · simp only [hka, decide_true, Bool.toNat_true]
    have : a / k = 1 := by
      rw [Nat.div_eq_iff hk]; constructor <;> omega
    omega
  · simp only [hka, decide_false, Bool.toNat_false]
    exact (Nat.div_eq_of_lt (by omega)).symm

theorem chk_sound {c : Ctx} {env : List Nat} {ρ : Nat → Int} (hs : Sem c env ρ) :
    ∀ (t : Tm) (P : Poly) (I : Iv), chk c t = some (P, I) →
      P.eval ρ = (t.eval env : Int) ∧ I.mem (t.eval env : Int)
  | .var i, P, I, h => by
    simp only [chk] at h
    cases hi : Nat.blt i c.n
    · rw [hi] at h; simp at h
    · rw [hi] at h
      simp only [Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := hs.var i (by simpa using hi)
      simp only [Poly.eval_atom, Tm.eval]
      rw [← this]; exact ⟨by first | rfl | trivial, hs.iv' i⟩
  | .lit v, P, I, h => by
    simp only [chk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Poly.eval_const, Tm.eval]
    exact ⟨by first | rfl | trivial, Iv.mem_const _⟩
  | .add a b, P, I, h => by
    simp only [chk] at h
    cases ha : chk c a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases hb : chk c b with
      | none => rw [ha, hb] at h; simp at h
      | some y =>
        obtain ⟨p, I1⟩ := x; obtain ⟨q, J⟩ := y
        rw [ha, hb] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨e1, m1⟩ := chk_sound hs a p I1 ha
        obtain ⟨e2, m2⟩ := chk_sound hs b q J hb
        simp only [Poly.eval_add, Tm.eval, Int.natCast_add, e1, e2]
        exact ⟨by first | rfl | trivial, Iv.mem_add m1 m2⟩
  | .mul a b, P, I, h => by
    simp only [chk] at h
    cases ha : chk c a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases hb : chk c b with
      | none => rw [ha, hb] at h; simp at h
      | some y =>
        obtain ⟨p, I1⟩ := x; obtain ⟨q, J⟩ := y
        rw [ha, hb] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨e1, m1⟩ := chk_sound hs a p I1 ha
        obtain ⟨e2, m2⟩ := chk_sound hs b q J hb
        simp only [Poly.eval_mul, Tm.eval, Int.natCast_mul, e1, e2]
        exact ⟨by first | rfl | trivial, Iv.mem_mul m1 m2⟩
  | .sub a b, P, I, h => by
    simp only [chk] at h
    cases ha : chk c a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases hb : chk c b with
      | none => rw [ha, hb] at h; simp at h
      | some y =>
        obtain ⟨p, I1⟩ := x; obtain ⟨q, J⟩ := y
        rw [ha, hb] at h
        obtain ⟨e1, m1⟩ := chk_sound hs a p I1 ha
        obtain ⟨e2, m2⟩ := chk_sound hs b q J hb
        have m1' := Iv.mem_inter m1 (e1 ▸ civ_sound hs p)
        have m2' := Iv.mem_inter m2 (e2 ▸ civ_sound hs q)
        simp only at h
        cases h0 : J.ble I1
        case true =>
          rw [h0] at h
          simp only [Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hle := Iv.ble_spec h0 m2 m1
          have hc : ((a.eval env - b.eval env : Nat) : Int) = (a.eval env : Int) - b.eval env :=
            Int.natCast_sub (by omega)
          simp only [Tm.eval, hc, Poly.eval_sub, e1, e2]
          exact ⟨by first | rfl | trivial, Iv.mem_sub m1 m2⟩
        rw [h0] at h
        simp only [Bool.cond_false] at h
        cases h1 : (J.inter (civ c q)).ble (I1.inter (civ c p))
        · rw [h1] at h
          cases h2 : (I1.inter (civ c p)).ble (J.inter (civ c q))
          · rw [h2] at h; simp at h
          · rw [h2] at h
            simp only [Bool.cond_false, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have := Iv.ble_spec h2 m1' m2'
            have hz : a.eval env - b.eval env = 0 := Nat.sub_eq_zero_of_le (by omega)
            simp only [Tm.eval, hz]
            exact ⟨by first | rfl | trivial, Iv.mem_const 0⟩
        · rw [h1] at h
          simp only [Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hle := Iv.ble_spec h1 m2' m1'
          have hc : ((a.eval env - b.eval env : Nat) : Int) = (a.eval env : Int) - b.eval env :=
            Int.natCast_sub (by omega)
          simp only [Tm.eval, hc, Poly.eval_sub, e1, e2]
          exact ⟨by first | rfl | trivial, Iv.mem_sub m1' m2'⟩
  | .div a k, P, I, h => by
    simp only [chk] at h
    cases ha : chk c a with
    | none => rw [ha] at h; simp at h
    | some x =>
      obtain ⟨p, I1⟩ := x
      rw [ha] at h
      obtain ⟨e1, m1⟩ := chk_sound hs a p I1 ha
      have m1' := refine_mem hs (k : Int) e1 m1
      simp only at h
      cases hk : Nat.blt 0 k
      · rw [hk] at h; simp at h
      · rw [hk] at h
        simp only [Bool.cond_true] at h
        have hk' : 0 < k := by simpa using hk
        cases hd : divmod c p (refine c p I1 k) k with
        | none => rw [hd] at h; simp at h
        | some y =>
          obtain ⟨d, r⟩ := y
          rw [hd] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have := (divmod_sound hs hk' hd e1 m1').1
          simp only [Tm.eval, Int.natCast_ediv]
          exact ⟨this, Iv.mem_divK (by omega) m1'⟩
  | .mod a k, P, I, h => by
    simp only [chk] at h
    cases ha : chk c a with
    | none => rw [ha] at h; simp at h
    | some x =>
      obtain ⟨p, I1⟩ := x
      rw [ha] at h
      obtain ⟨e1, m1⟩ := chk_sound hs a p I1 ha
      have m1' := refine_mem hs (k : Int) e1 m1
      simp only at h
      cases hk : Nat.blt 0 k
      · rw [hk] at h; simp at h
      · rw [hk] at h
        simp only [Bool.cond_true] at h
        have hk' : 0 < k := by simpa using hk
        cases hd : divmod c p (refine c p I1 k) k with
        | none => rw [hd] at h; simp at h
        | some y =>
          obtain ⟨d, r⟩ := y
          rw [hd] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have := (divmod_sound hs hk' hd e1 m1').2
          simp only [Tm.eval, Int.natCast_emod]
          refine ⟨this, ?_⟩
          cases hw : (refine c p I1 k).within (k : Int)
          · simp only [Bool.cond_false]
            constructor
            · intro l hl; simp at hl; subst hl; exact Int.emod_nonneg _ (by omega)
            · intro l hl; simp at hl; subst hl
              have := Int.emod_lt_of_pos (a.eval env : Int) (show (0 : Int) < k by omega)
              omega
          · simp only [Bool.cond_true]
            obtain ⟨h0, h1⟩ := Iv.within_spec hw m1'
            rw [Int.emod_eq_of_lt h0 h1]; exact m1'
  | .geb a k, P, I, h => by
    simp only [chk] at h
    cases ha : chk c a with
    | none => rw [ha] at h; simp at h
    | some x =>
      obtain ⟨p, I1⟩ := x
      rw [ha] at h
      obtain ⟨e1, m1⟩ := chk_sound hs a p I1 ha
      have m1' := refine_mem hs (2 * (k : Int)) e1 m1
      simp only at h
      cases hw : (refine c p I1 (2 * k)).within (k : Int)
      · rw [hw] at h
        simp only [Bool.cond_false] at h
        cases hb : Iv.ble (Iv.const (k : Int)) (refine c p I1 (2 * k))
        · rw [hb] at h
          simp only [Bool.cond_false] at h
          cases h2 : (Nat.blt 0 k && (refine c p I1 (2 * k)).within (2 * (k : Int)))
          · rw [h2] at h; simp at h
          · rw [h2] at h
            simp only [Bool.cond_true] at h
            simp only [Bool.and_eq_true, Nat.blt_eq] at h2
            cases hd : divmod c p (refine c p I1 (2 * k)) k with
            | none => rw [hd] at h; simp at h
            | some y =>
              obtain ⟨d, r⟩ := y
              rw [hd] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hd' := (divmod_sound hs h2.1 hd e1 m1').1
              obtain ⟨h0, h1⟩ := Iv.within_spec h2.2 m1'
              have hg := geb_eq_div (a := a.eval env) h2.1 (by omega)
              simp only [Tm.eval, hg, Int.natCast_ediv]
              refine ⟨hd', ?_⟩
              rw [← Int.natCast_ediv, ← hg]
              constructor
              · intro l hl; simp at hl; subst hl; exact Int.natCast_nonneg _
              · intro l hl; simp at hl; subst hl
                cases decide (k ≤ a.eval env) <;> simp
        · rw [hb] at h
          simp only [Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have := Iv.ble_spec hb (Iv.mem_const _) m1'
          have hka : k ≤ a.eval env := by omega
          simp only [Tm.eval, hka, decide_true, Bool.toNat_true, Poly.eval_const]
          exact ⟨by first | rfl | trivial, Iv.mem_const 1⟩
      · rw [hw] at h
        simp only [Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h0, h1⟩ := Iv.within_spec hw m1'
        have hka : ¬ k ≤ a.eval env := by omega
        simp only [Tm.eval, hka, decide_false, Bool.toNat_false]
        exact ⟨by first | rfl | trivial, Iv.mem_const 0⟩

theorem eq_zero_of_mul_bound {g z : Int} (hg : 0 < g) (h1 : -g < g * z) (h2 : g * z < g) : z = 0 := by
  rcases Int.lt_trichotomy z 0 with hz | hz | hz
  · have : g * z ≤ g * (-1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  · exact hz
  · have : g * 1 ≤ g * z := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega

/-- **Soundness of the carry-chain checker.** -/
theorem check_sound (env : List Nat) (ubs : List (Option Nat)) (tbl : List (Poly × Nat))
    (ivs : List Iv) (a b : Tm) (hb : BoundsOK env ubs) (h : check ubs tbl ivs a b = true) :
    a.eval env = b.eval env := by
  unfold check at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hc, h⟩ := h
  have hs := sem_of_check hb hc
  cases ha : chk { n := ubs.length, tbl := tbl, ivs := ivs } a with
  | none => rw [ha] at h; simp at h
  | some x =>
    cases hb' : chk { n := ubs.length, tbl := tbl, ivs := ivs } b with
    | none => rw [ha, hb'] at h; simp at h
    | some y =>
      obtain ⟨p, I⟩ := x; obtain ⟨q, J⟩ := y
      rw [ha, hb'] at h
      obtain ⟨e1, m1⟩ := chk_sound hs a p I ha
      obtain ⟨e2, m2⟩ := chk_sound hs b q J hb'
      simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
      apply Int.ofNat_inj.mp
      rcases h with h | ⟨⟨⟨hg, hdvd⟩, w1⟩, w2⟩
      · have := Poly.eval_of_isNil h (extend (rho0 env) ubs.length tbl)
        rw [Poly.eval_sub, e1, e2] at this
        omega
      · have hd := Poly.eval_of_dvdAll (extend (rho0 env) ubs.length tbl) _ _ hdvd
        rw [Poly.eval_sub, e1, e2] at hd
        have m1' := Iv.mem_inter m1 (e1 ▸ civ_sound hs p)
        have m2' := Iv.mem_inter m2 (e2 ▸ civ_sound hs q)
        obtain ⟨h0, h1⟩ := Iv.within_spec w1 m1'
        obtain ⟨h2, h3⟩ := Iv.within_spec w2 m2'
        have hz := eq_zero_of_mul_bound (g := ((p.sub q).gcdCoeffs : Int)) (by omega)
          (by rw [← hd]; omega) (by rw [← hd]; omega)
        rw [hz, Int.mul_zero] at hd
        omega

/-- **Soundness of the inequality checker.** -/
theorem checkLe_sound (env : List Nat) (ubs : List (Option Nat)) (tbl : List (Poly × Nat))
    (ivs : List Iv) (a b : Tm) (hb : BoundsOK env ubs) (h : checkLe ubs tbl ivs a b = true) :
    a.eval env ≤ b.eval env := by
  unfold checkLe at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hc, h⟩ := h
  have hs := sem_of_check hb hc
  cases ha : chk { n := ubs.length, tbl := tbl, ivs := ivs } a with
  | none => rw [ha] at h; simp at h
  | some x =>
    cases hb' : chk { n := ubs.length, tbl := tbl, ivs := ivs } b with
    | none => rw [ha, hb'] at h; simp at h
    | some y =>
      obtain ⟨p, I⟩ := x; obtain ⟨q, J⟩ := y
      rw [ha, hb'] at h
      obtain ⟨e1, m1⟩ := chk_sound hs a p I ha
      obtain ⟨e2, m2⟩ := chk_sound hs b q J hb'
      have m1' := Iv.mem_inter m1 (e1 ▸ civ_sound hs p)
      have m2' := Iv.mem_inter m2 (e2 ▸ civ_sound hs q)
      simp only [Bool.or_eq_true] at h
      apply Int.ofNat_le.mp
      rcases h with h | h
      · exact Iv.ble_spec h m1' m2'
      · have hd := civ_sound hs (q.sub p)
        rw [Poly.eval_sub, e1, e2] at hd
        cases hl : (civ { n := ubs.length, tbl := tbl, ivs := ivs } (q.sub p)).lo with
        | none => rw [hl] at h; simp at h
        | some l =>
          rw [hl] at h
          have := intNonneg_le h
          have := hd.1 l hl
          omega

end Janus.Carry
