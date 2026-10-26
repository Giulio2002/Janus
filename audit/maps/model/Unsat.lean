import Janus

/-!
# Audit R3-C1: the pre-fix `mapassign_fast64` and `makemap_small` contracts admitted no call

Before agent/maps2 (main f84051a), `Janus.Contracts.Map.Assign` and `MakeSmall` (and their amd64
twins) were stated with a perpetual runtime environment: `M.Env` held after every call, and the
precondition said nothing else about the runtime's state. But both allocate. Repeating the call
from the state it returns in is always allowed by those contracts, so:

* `Assign`: from any non-nil map, assigning a fresh key each time (one always exists while fewer
  than `2^64` keys are present) would reach a map with `2^64` keys, whose header word (`used`,
  `MapModel.Laws.len`) cannot hold `2^64`.
* `MakeSmall`: every call returns a new non-nil map distinct from all existing ones and keeps the
  old ones, so `2^48` calls would give `2^48` distinct non-zero header addresses below `2^48`.

So no implementation, model and call state meet them together, as soon as the goroutine's stack
guard word `16(g)` is outside what the call may write (`Map.rtWrites`). Every example caller
provides that (`Map.CallerOK`: the guard is outside the private memory and outside the caller's
window, which contains the callee's stack; `guard_of_callerOK` below). The theorems Insert,
InsertGet and NewMap on both ISAs, which assumed these contracts, were therefore vacuous. The
fix (agent/maps2) adds the readiness predicate `H : RtReady` of round 9 C1 to every allocating
map contract; `UnsatFixed.lean` shows this argument no longer goes through, and
`Janus.Contracts.MapSat` / `MapSatAmd64` give witnesses for the fixed contracts.

The old definitions are copied verbatim below (renamed `Old…`).
-/

namespace Janus.Audit.MapsR3

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Map

/-! ## Pigeonhole -/

theorem subset_length_le {α : Type} [DecidableEq α] :
    ∀ (A B : List α), A.Nodup → (∀ x ∈ A, x ∈ B) → A.length ≤ B.length
  | [], _, _, _ => Nat.zero_le _
  | x :: A, B, hA, hs => by
    obtain ⟨hx, hA'⟩ := List.nodup_cons.1 hA
    have hxB : x ∈ B := hs x (List.mem_cons_self ..)
    have ih := subset_length_le A (B.erase x) hA' fun y hy => by
      have hne : y ≠ x := fun h => hx (h ▸ hy)
      exact (List.mem_erase_of_ne hne).2 (hs y (List.mem_cons_of_mem _ hy))
    rw [List.length_erase_of_mem hxB] at ih
    have : 0 < B.length := List.length_pos_of_mem hxB
    simp only [List.length_cons]; omega

theorem nodup_map_toNat : ∀ (l : List (BitVec 64)), l.Nodup → (l.map BitVec.toNat).Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    obtain ⟨hx, hl⟩ := List.nodup_cons.1 h
    refine List.nodup_cons.2 ⟨fun hm => ?_, nodup_map_toNat l hl⟩
    obtain ⟨y, hy, he⟩ := List.mem_map.1 hm
    exact hx (BitVec.eq_of_toNat_eq he ▸ hy)

/-- A finite map with fewer than `2^64` keys misses some 64-bit key. -/
theorem exists_fresh {V : Type} {f : AMap (BitVec 64) V} {ks : List (BitVec 64)} (hk : Keys f ks)
    (hlt : ks.length < 2 ^ 64) : ∃ k, f k = none := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ k, (f k).isSome := fun k => by
    cases h : f k with
    | none => exact absurd ⟨k, h⟩ hno
    | some _ => rfl
  have := subset_length_le (List.range (2 ^ 64)) (ks.map BitVec.toNat) List.nodup_range fun i hi => by
    have hi' := List.mem_range.1 hi
    refine List.mem_map.2 ⟨BitVec.ofNat 64 i, (hk.2 _).2 (hall _), ?_⟩
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hi'
  simp only [List.length_range, List.length_map] at this
  omega

theorem keys_set_fresh {V : Type} {f : AMap (BitVec 64) V} {ks : List (BitVec 64)} (hk : Keys f ks)
    {k : BitVec 64} (hn : f k = none) (v : V) : Keys (f.set k v) (k :: ks) := by
  refine ⟨List.nodup_cons.2 ⟨fun hm => by have := (hk.2 k).1 hm; simp [hn] at this, hk.1⟩, fun k' => ?_⟩
  by_cases h : k' = k
  · subst h; simp
  · simp only [List.mem_cons, h, false_or, AMap.set_other _ _ h]; exact hk.2 k'

/-! ## arm64 -/

/-- The pre-fix `Map.Assign` (main f84051a), verbatim. -/
def OldAssign (p : Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧
      M.Rep s.mem (s.regs 1).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun r m =>
      m.accessible (r 0).toNat 8 true = true ∧ InRanges (r 0).toNat 8 M.priv ∧
      ∀ v : BitVec 64, M.Rep (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 1).toNat (f.set (s.regs 2) v) ∧
        M.Env (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 28) ∧
        OthersKept M m (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 1).toNat)

/-- The pre-fix `Map.MakeSmall` (main f84051a), verbatim. -/
def OldMakeSmall {K V : Type} (p : Program) (addr : Nat) (M : MapModel K V) : Prop :=
  Summary p addr (fun s => RTPre M 0 s)
    (fun s s' => RTReturn M 0 [] 0 s s' fun r m =>
      (r 0).toNat ≠ 0 ∧ M.Rep m (r 0).toNat AMap.empty ∧
      ∀ mp f, M.Rep s.mem mp f → mp ≠ (r 0).toNat)

/-- The call state `s` with memory `m` and the key register `X2 = k`. -/
def nxt (s : State) (m : Memory) (k : BitVec 64) : State :=
  { s with mem := m, regs := fun i => if i = 2 then k else s.regs i }

/-- `RTPre` depends on memory only through `M.Env`, the accessible ranges and the guard word. -/
theorem rtPre_nxt {K V : Type} {M : MapModel K V} {n : Nat} {s : State} {m : Memory} (k : BitVec 64)
    (h : RTPre M n s) (hacc : ∀ a n w, m.accessible a n w = s.mem.accessible a n w)
    (hg : m.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (he : M.Env m (s.regs 28)) : RTPre M n (nxt s m k) := by
  obtain ⟨-, ⟨g1, g2, g3⟩, ⟨c1, c2, c3, c4, c5, c6, c7⟩, ho⟩ := h
  refine ⟨he, ⟨g1, ?_, ?_⟩, ⟨c1, c2, c3, c4, c5, c6, ?_⟩, ho⟩
  · show m.accessible _ 8 false = true; rw [hacc]; exact g2
  · show m.readLE ((s.regs 28).toNat + 16) 8 + M.depth < s.sp.toNat
    rw [hg]; exact g3
  · show m.accessible _ _ true = true; rw [hacc]; exact c7

theorem nxt_regs (s : State) (m : Memory) (k : BitVec 64) (i : Nat) (hi : i ≠ 2) :
    (nxt s m k).regs i = s.regs i := by simp [nxt, hi]

/-- **R3-C1 (arm64, `mapassign_fast64`).** No model, code and call state meet the pre-fix
`Assign` contract together, once the guard word is outside what the call may write. -/
theorem old_assign_unsat (p : Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64))
    (hl : M.Laws) (hA : OldAssign p addr M) (s : State) (f : AMap (BitVec 64) (BitVec 64))
    (hpc : s.pc = BitVec.ofNat 64 addr)
    (hpre : RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧
      M.Rep s.mem (s.regs 1).toNat f)
    (hg : Outside ((s.regs 28).toNat + 16) 8 (rtWrites M s 3)) : False := by
  obtain ⟨hrt, hty, hne, hrep⟩ := hpre
  have hgp : Outside ((s.regs 28).toNat + 16) 8 M.priv := by
    simp only [rtWrites, outside_append] at hg; exact hg.1
  let G := (s.regs 28).toNat + 16
  let Inv : Memory → AMap (BitVec 64) (BitVec 64) → List (BitVec 64) → Prop := fun m f ks =>
    Keys f ks ∧ M.Rep m (s.regs 1).toNat f ∧ M.Env m (s.regs 28) ∧
      (∀ a n w, m.accessible a n w = s.mem.accessible a n w) ∧ m.readLE G 8 = s.mem.readLE G 8
  have step : ∀ m f ks k, Inv m f ks → f k = none → ∃ m', Inv m' (f.set k 0) (k :: ks) := by
    intro m f ks k ⟨hk, hr, he, hacc, hgd⟩ hn
    obtain ⟨_, s', -, -, r, v, fl, m', -, hfr, -, -, hw, hin, hall⟩ :=
      hA f (nxt s m k) hpc ⟨rtPre_nxt k hrt hacc hgd he, by rw [nxt_regs _ _ _ 0 (by decide)]; exact hty,
        by rw [nxt_regs _ _ _ 1 (by decide)]; exact hne, by rw [nxt_regs _ _ _ 1 (by decide)]; exact hr⟩
    have hg2 : Outside G 8 (rtWrites M (nxt s m k) 3 ++ []) := by rw [List.append_nil]; exact hg
    obtain ⟨hr', he', -⟩ := hall 0#64
    simp only [nxt_regs _ _ _ 1 (by decide), nxt_regs _ _ _ 28 (by decide),
      show (nxt s m k).regs 2 = k from rfl, BitVec.toNat_zero] at hr' he'
    refine ⟨_, keys_set_fresh hk hn 0, hr', he', fun a n w => ?_, ?_⟩
    · rw [Memory.accessible_writeLE, hfr.accessible]; exact hacc a n w
    · rw [Memory.readLE_writeLE_of_disjoint _ _ (InRanges.disjoint hin hgp), hfr.readLE _ _ hg2]
      exact hgd
  have key : ∀ d m f ks, Inv m f ks → ks.length + d = 2 ^ 64 → False := by
    intro d
    induction d with
    | zero =>
      intro m f ks hinv hlen
      obtain ⟨hk, hr, -⟩ := hinv
      have h1 := (hl.len m _ f hr).2.2 ks hk
      have h2 := Memory.readLE_lt m ((s.regs 1).toNat) 8
      rw [h1, show (256 : Nat) ^ 8 = 2 ^ 64 by decide] at h2
      omega
    | succ d ih =>
      intro m f ks hinv hlen
      obtain ⟨k, hn⟩ := exists_fresh hinv.1 (by omega)
      obtain ⟨m', hinv'⟩ := step m f ks k hinv hn
      exact ih m' _ _ hinv' (by simp only [List.length_cons]; omega)
  obtain ⟨ks, hk⟩ := hl.finite _ _ _ hrep
  have h1 := (hl.len _ _ f hrep).2.2 ks hk
  have h2 := Memory.readLE_lt s.mem ((s.regs 1).toNat) 8
  rw [h1, show (256 : Nat) ^ 8 = 2 ^ 64 by decide] at h2
  exact key (2 ^ 64 - ks.length) s.mem f ks ⟨hk, hrep, hrt.1, fun _ _ _ => rfl, rfl⟩ (by omega)

/-- The maps a sequence of creations produced: distinct, non-zero, each (still) an empty map. -/
theorem created_bound {K V : Type} {M : MapModel K V} (hl : M.Laws) {m : Memory} {L : List Nat}
    (hnd : L.Nodup) (hL : ∀ a ∈ L, a ≠ 0 ∧ M.Rep m a AMap.empty) : L.length + 1 ≤ 2 ^ 48 := by
  have := subset_length_le (0 :: L) (List.range (2 ^ 48))
    (List.nodup_cons.2 ⟨fun h => (hL 0 h).1 rfl, hnd⟩) fun a ha => by
      rcases List.mem_cons.1 ha with rfl | ha
      · exact List.mem_range.2 (by decide)
      · have := (hl.len m a _ (hL a ha).2).2.1
        exact List.mem_range.2 (by omega)
  simpa using this

/-- **R3-C1 (arm64, `makemap_small`).** No model, code and call state meet the pre-fix
`MakeSmall` contract together, once the guard word is outside what the call may write. -/
theorem old_makeSmall_unsat {K V : Type} (p : Program) (addr : Nat) (M : MapModel K V)
    (hl : M.Laws) (hA : OldMakeSmall p addr M) (s : State) (hpc : s.pc = BitVec.ofNat 64 addr)
    (hpre : RTPre M 0 s) (hg : Outside ((s.regs 28).toNat + 16) 8 (rtWrites M s 0)) : False := by
  let G := (s.regs 28).toNat + 16
  let Inv : Memory → List Nat → Prop := fun m L =>
    L.Nodup ∧ (∀ a ∈ L, a ≠ 0 ∧ M.Rep m a AMap.empty) ∧ M.Env m (s.regs 28) ∧
      (∀ a n w, m.accessible a n w = s.mem.accessible a n w) ∧ m.readLE G 8 = s.mem.readLE G 8
  have step : ∀ m L, Inv m L → ∃ m' a, Inv m' (a :: L) := by
    intro m L ⟨hnd, hL, he, hacc, hgd⟩
    obtain ⟨_, s', -, -, r, v, fl, m', -, hfr, he', hok, hne0, hnew, hdist⟩ :=
      hA (nxt s m (s.regs 2)) hpc (rtPre_nxt _ hpre hacc hgd he)
    have hg2 : Outside G 8 (rtWrites M (nxt s m (s.regs 2)) 0 ++ []) := by
      rw [List.append_nil]; exact hg
    refine ⟨m', (r 0).toNat, List.nodup_cons.2 ⟨fun h => hdist _ _ (hL _ h).2 rfl, hnd⟩,
      fun a ha => ?_, he', fun a n w => (hfr.accessible a n w).trans (hacc a n w),
      (hfr.readLE _ _ hg2).trans hgd⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨hne0, hnew⟩
    · exact ⟨(hL a ha).1, hok a _ (hL a ha).1 (hL a ha).2⟩
  have key : ∀ d m L, Inv m L → L.length + d = 2 ^ 48 → False := by
    intro d
    induction d with
    | zero =>
      intro m L hinv hlen
      have := created_bound hl hinv.1 hinv.2.1
      omega
    | succ d ih =>
      intro m L hinv hlen
      obtain ⟨m', a, hinv'⟩ := step m L hinv
      exact ih m' _ hinv' (by simp only [List.length_cons]; omega)
  exact key (2 ^ 48) s.mem [] ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil, hpre.1,
    fun _ _ _ => rfl, rfl⟩ (by simp)

/-- The guard hypothesis holds at every call an example makes: `Map.CallerOK` at the caller's
entry `s` (the guard word outside the private memory and outside the caller's window, which
contains the callee's stack) gives it at the call state `S`, `frame` bytes lower. -/
theorem guard_of_callerOK {K V : Type} {M : MapModel K V} {s S : State} {frame above nargs : Nat}
    (hc : CallerOK M s frame above) (hsp : S.sp.toNat = s.sp.toNat - frame)
    (hg : S.regs 28 = s.regs 28) (hn : 8 + 8 * nargs ≤ frame + above) :
    Outside ((S.regs 28).toNat + 16) 8 (rtWrites M S nargs) := by
  obtain ⟨-, -, -, hd8, hd, -, -, -, hgd, hgo⟩ := hc
  simp only [Spec.Disjoint] at hgd
  simp only [rtWrites, outside_append, calleeStack, outside_cons, outside_nil, and_true, hg, hsp]
  exact ⟨hgo, by omega, by omega⟩

/-- **R3-C1, as it bites the examples (arm64).** With `Map.CallerOK` at the caller's entry
(the precondition of Insert and InsertGet), no call of an implementation of the pre-fix
`Assign` can satisfy the contract's precondition. -/
theorem old_assign_vacuous (p : Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64))
    (hl : M.Laws) (hA : OldAssign p addr M) {s S : State} {frame above : Nat} (f : AMap (BitVec 64) (BitVec 64))
    (hc : CallerOK M s frame above) (hsp : S.sp.toNat = s.sp.toNat - frame) (hg : S.regs 28 = s.regs 28)
    (hn : 8 + 8 * 3 ≤ frame + above) (hpc : S.pc = BitVec.ofNat 64 addr)
    (hpre : RTPre M 3 S ∧ M.Typ (S.regs 0).toNat ∧ (S.regs 1).toNat ≠ 0 ∧ M.Rep S.mem (S.regs 1).toNat f) :
    False :=
  old_assign_unsat p addr M hl hA S f hpc hpre (guard_of_callerOK hc hsp hg hn)

/-- The same for the pre-fix `MakeSmall` (NewMap). -/
theorem old_makeSmall_vacuous {K V : Type} (p : Program) (addr : Nat) (M : MapModel K V)
    (hl : M.Laws) (hA : OldMakeSmall p addr M) {s S : State} {frame above : Nat}
    (hc : CallerOK M s frame above) (hsp : S.sp.toNat = s.sp.toNat - frame) (hg : S.regs 28 = s.regs 28)
    (hn : 8 ≤ frame + above) (hpc : S.pc = BitVec.ofNat 64 addr) (hpre : RTPre M 0 S) : False :=
  old_makeSmall_unsat p addr M hl hA S hpc hpre (guard_of_callerOK hc hsp hg (by omega))

end Janus.Audit.MapsR3

/-! ## amd64 -/

namespace Janus.Audit.MapsR3.Amd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64
open Janus (Outside InRanges MemFrame outside_append outside_cons outside_nil)
open Janus.Audit.MapsR3 (exists_fresh keys_set_fresh created_bound)

/-- The pre-fix `MapAmd64.Assign` (main f84051a), verbatim. -/
def OldAssign64 (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 3).toNat ≠ 0 ∧
      M.Rep s.mem (s.regs 3).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun r m =>
      m.accessible (r 0).toNat 8 true = true ∧ InRanges (r 0).toNat 8 M.priv ∧
      ∀ v : BitVec 64, M.Rep (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 3).toNat (f.set (s.regs 1) v) ∧
        M.Env (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 14) ∧
        OthersKept M m (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 3).toNat)

/-- The pre-fix `MapAmd64.MakeSmall` (main f84051a), verbatim. -/
def OldMakeSmall64 {K V : Type} (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel K V) : Prop :=
  Janus.Amd64.Tactic.Summary p addr (fun s => RTPre M 0 s)
    (fun s s' => RTReturn M 0 [] 0 s s' fun r m =>
      (r 0).toNat ≠ 0 ∧ M.Rep m (r 0).toNat AMap.empty ∧
      ∀ mp f, M.Rep s.mem mp f → mp ≠ (r 0).toNat)

/-- The call state `s` with memory `m` and the key register `RCX = k`. -/
def nxt (s : State) (m : Janus.Arm64.Memory) (k : BitVec 64) : State :=
  { s with mem := m, regs := fun i => if i = 1 then k else s.regs i }

theorem nxt_regs (s : State) (m : Janus.Arm64.Memory) (k : BitVec 64) (i : Nat) (hi : i ≠ 1) :
    (nxt s m k).regs i = s.regs i := by simp [nxt, hi]

/-- `RTPre` (amd64) depends on memory only through `M.Env`, the accessible ranges, the guard
word and the return-address slot `[RSP]`. -/
theorem rtPre_nxt {K V : Type} {M : MapModel K V} {n : Nat} {s : State} {m : Janus.Arm64.Memory}
    (k : BitVec 64) (h : RTPre M n s) (hacc : ∀ a n w, m.accessible a n w = s.mem.accessible a n w)
    (hg : m.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8)
    (hra : m.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (he : M.Env m (s.regs 14)) : RTPre M n (nxt s m k) := by
  obtain ⟨-, ⟨g1, g2, g3⟩, c1, c2, c3, c4, c5, c6, c7, ho⟩ := h
  refine ⟨he, ⟨g1, ?_, ?_⟩, c1, c2, c3, ?_, c5, c6, ?_, ho⟩
  · show m.accessible _ 8 false = true; rw [hacc]; exact g2
  · show m.readLE ((s.regs 14).toNat + 16) 8 + M.depth < (s.regs 4).toNat
    rw [hg]; exact g3
  · show m.accessible _ _ true = true; rw [hacc]; exact c4
  · show m.readLE (s.regs 4).toNat 8 < 2 ^ 47; rw [hra]; exact c7

/-- The return-address slot is outside everything a call may write. -/
theorem retSlot_outside {K V : Type} {M : MapModel K V} {n : Nat} {s : State} (h : RTPre M n s) :
    Outside (s.regs 4).toNat 8 (rtWrites M s n) := by
  obtain ⟨-, -, -, hd, -, -, -, -, -, ho⟩ := h
  simp only [rtWrites, outside_append]
  refine ⟨Outside.of_sub ho (by omega) (by omega), ?_⟩
  simp only [calleeStack, outside_cons, outside_nil, and_true]; omega

/-- **R3-C1 (amd64, `mapassign_fast64`).** As `old_assign_unsat`. -/
theorem old_assign64_unsat (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64))
    (hl : M.Laws) (hA : OldAssign64 p addr M) (s : State) (f : AMap (BitVec 64) (BitVec 64))
    (hpc : s.rip = BitVec.ofNat 64 addr)
    (hpre : RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 3).toNat ≠ 0 ∧
      M.Rep s.mem (s.regs 3).toNat f)
    (hg : Outside ((s.regs 14).toNat + 16) 8 (rtWrites M s 3)) : False := by
  obtain ⟨hrt, hty, hne, hrep⟩ := hpre
  have hgp : Outside ((s.regs 14).toNat + 16) 8 M.priv := by
    simp only [rtWrites, outside_append] at hg; exact hg.1
  have hro := retSlot_outside hrt
  have hrp : Outside (s.regs 4).toNat 8 M.priv := by
    simp only [rtWrites, outside_append] at hro; exact hro.1
  let G := (s.regs 14).toNat + 16
  let R := (s.regs 4).toNat
  let Inv : Janus.Arm64.Memory → AMap (BitVec 64) (BitVec 64) → List (BitVec 64) → Prop := fun m f ks =>
    Keys f ks ∧ M.Rep m (s.regs 3).toNat f ∧ M.Env m (s.regs 14) ∧
      (∀ a n w, m.accessible a n w = s.mem.accessible a n w) ∧ m.readLE G 8 = s.mem.readLE G 8 ∧
      m.readLE R 8 = s.mem.readLE R 8
  have step : ∀ m f ks k, Inv m f ks → f k = none → ∃ m', Inv m' (f.set k 0) (k :: ks) := by
    intro m f ks k ⟨hk, hr, he, hacc, hgd, hrd⟩ hn
    obtain ⟨_, s', -, -, r, x, y, fl, m', -, hfr, -, -, hw, hin, hall⟩ :=
      hA f (nxt s m k) hpc ⟨rtPre_nxt k hrt hacc hgd hrd he,
        by rw [nxt_regs _ _ _ 0 (by decide)]; exact hty,
        by rw [nxt_regs _ _ _ 3 (by decide)]; exact hne, by rw [nxt_regs _ _ _ 3 (by decide)]; exact hr⟩
    have hg2 : Outside G 8 (rtWrites M (nxt s m k) 3 ++ []) := by rw [List.append_nil]; exact hg
    have hr2 : Outside R 8 (rtWrites M (nxt s m k) 3 ++ []) := by rw [List.append_nil]; exact hro
    obtain ⟨hr', he', -⟩ := hall 0#64
    simp only [nxt_regs _ _ _ 3 (by decide), nxt_regs _ _ _ 14 (by decide),
      show (nxt s m k).regs 1 = k from rfl, BitVec.toNat_zero] at hr' he'
    refine ⟨_, keys_set_fresh hk hn 0, hr', he', fun a n w => ?_, ?_, ?_⟩
    · rw [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible]; exact hacc a n w
    · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (InRanges.disjoint hin hgp), hfr.readLE _ _ hg2]
      exact hgd
    · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (InRanges.disjoint hin hrp), hfr.readLE _ _ hr2]
      exact hrd
  have key : ∀ d m f ks, Inv m f ks → ks.length + d = 2 ^ 64 → False := by
    intro d
    induction d with
    | zero =>
      intro m f ks hinv hlen
      obtain ⟨hk, hr, -⟩ := hinv
      have h1 := (hl.len m _ f hr).2.2 ks hk
      have h2 := Janus.Arm64.Memory.readLE_lt m ((s.regs 3).toNat) 8
      rw [h1, show (256 : Nat) ^ 8 = 2 ^ 64 by decide] at h2
      omega
    | succ d ih =>
      intro m f ks hinv hlen
      obtain ⟨k, hn⟩ := exists_fresh hinv.1 (by omega)
      obtain ⟨m', hinv'⟩ := step m f ks k hinv hn
      exact ih m' _ _ hinv' (by simp only [List.length_cons]; omega)
  obtain ⟨ks, hk⟩ := hl.finite _ _ _ hrep
  have h1 := (hl.len _ _ f hrep).2.2 ks hk
  have h2 := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 3).toNat) 8
  rw [h1, show (256 : Nat) ^ 8 = 2 ^ 64 by decide] at h2
  exact key (2 ^ 64 - ks.length) s.mem f ks ⟨hk, hrep, hrt.1, fun _ _ _ => rfl, rfl, rfl⟩ (by omega)

/-- **R3-C1 (amd64, `makemap_small`).** As `old_makeSmall_unsat`. -/
theorem old_makeSmall64_unsat {K V : Type} (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel K V)
    (hl : M.Laws) (hA : OldMakeSmall64 p addr M) (s : State) (hpc : s.rip = BitVec.ofNat 64 addr)
    (hpre : RTPre M 0 s) (hg : Outside ((s.regs 14).toNat + 16) 8 (rtWrites M s 0)) : False := by
  have hro := retSlot_outside hpre
  let G := (s.regs 14).toNat + 16
  let R := (s.regs 4).toNat
  let Inv : Janus.Arm64.Memory → List Nat → Prop := fun m L =>
    L.Nodup ∧ (∀ a ∈ L, a ≠ 0 ∧ M.Rep m a AMap.empty) ∧ M.Env m (s.regs 14) ∧
      (∀ a n w, m.accessible a n w = s.mem.accessible a n w) ∧ m.readLE G 8 = s.mem.readLE G 8 ∧
      m.readLE R 8 = s.mem.readLE R 8
  have step : ∀ m L, Inv m L → ∃ m' a, Inv m' (a :: L) := by
    intro m L ⟨hnd, hL, he, hacc, hgd, hrd⟩
    obtain ⟨_, s', -, -, r, x, y, fl, m', -, hfr, he', hok, hne0, hnew, hdist⟩ :=
      hA (nxt s m (s.regs 1)) hpc (rtPre_nxt _ hpre hacc hgd hrd he)
    have hg2 : Outside G 8 (rtWrites M (nxt s m (s.regs 1)) 0 ++ []) := by
      rw [List.append_nil]; exact hg
    have hr2 : Outside R 8 (rtWrites M (nxt s m (s.regs 1)) 0 ++ []) := by
      rw [List.append_nil]; exact hro
    refine ⟨m', (r 0).toNat, List.nodup_cons.2 ⟨fun h => hdist _ _ (hL _ h).2 rfl, hnd⟩,
      fun a ha => ?_, he', fun a n w => (hfr.accessible a n w).trans (hacc a n w),
      (hfr.readLE _ _ hg2).trans hgd, (hfr.readLE _ _ hr2).trans hrd⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨hne0, hnew⟩
    · exact ⟨(hL a ha).1, hok a _ (hL a ha).1 (hL a ha).2⟩
  have key : ∀ d m L, Inv m L → L.length + d = 2 ^ 48 → False := by
    intro d
    induction d with
    | zero =>
      intro m L hinv hlen
      have := created_bound hl hinv.1 hinv.2.1
      omega
    | succ d ih =>
      intro m L hinv hlen
      obtain ⟨m', a, hinv'⟩ := step m L hinv
      exact ih m' _ hinv' (by simp only [List.length_cons]; omega)
  exact key (2 ^ 48) s.mem [] ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil, hpre.1,
    fun _ _ _ => rfl, rfl, rfl⟩ (by simp)

/-- `MapAmd64.CallerOK` at the caller's entry gives the guard hypothesis at the call state. -/
theorem guard_of_callerOK64 {K V : Type} {M : MapModel K V} {s S : State} {frame above nargs : Nat}
    (hc : CallerOK M s frame above) (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame)
    (hg : S.regs 14 = s.regs 14) (hn : 8 + 8 * nargs ≤ frame + above) :
    Outside ((S.regs 14).toNat + 16) 8 (rtWrites M S nargs) := by
  obtain ⟨-, -, -, hd, -, -, -, hgd, hgo⟩ := hc
  simp only [Janus.Spec.Disjoint] at hgd
  simp only [rtWrites, outside_append, calleeStack, outside_cons, outside_nil, and_true, hg, hsp]
  exact ⟨hgo, by omega, by omega⟩

theorem old_assign64_vacuous (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64))
    (hl : M.Laws) (hA : OldAssign64 p addr M) {s S : State} {frame above : Nat} (f : AMap (BitVec 64) (BitVec 64))
    (hc : CallerOK M s frame above) (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame)
    (hg : S.regs 14 = s.regs 14) (hn : 8 + 8 * 3 ≤ frame + above) (hpc : S.rip = BitVec.ofNat 64 addr)
    (hpre : RTPre M 3 S ∧ M.Typ (S.regs 0).toNat ∧ (S.regs 3).toNat ≠ 0 ∧ M.Rep S.mem (S.regs 3).toNat f) :
    False :=
  old_assign64_unsat p addr M hl hA S f hpc hpre (guard_of_callerOK64 hc hsp hg hn)

theorem old_makeSmall64_vacuous {K V : Type} (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel K V)
    (hl : M.Laws) (hA : OldMakeSmall64 p addr M) {s S : State} {frame above : Nat}
    (hc : CallerOK M s frame above) (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame)
    (hg : S.regs 14 = s.regs 14) (hn : 8 ≤ frame + above) (hpc : S.rip = BitVec.ofNat 64 addr)
    (hpre : RTPre M 0 S) : False :=
  old_makeSmall64_unsat p addr M hl hA S hpc hpre (guard_of_callerOK64 hc hsp hg (by omega))

end Janus.Audit.MapsR3.Amd64

open Janus.Audit.MapsR3 Janus.Audit.MapsR3.Amd64 in
#print axioms old_assign_unsat
open Janus.Audit.MapsR3 in
#print axioms old_makeSmall_unsat
open Janus.Audit.MapsR3 in
#print axioms old_assign_vacuous
open Janus.Audit.MapsR3 in
#print axioms old_makeSmall_vacuous
open Janus.Audit.MapsR3.Amd64 in
#print axioms old_assign64_unsat
open Janus.Audit.MapsR3.Amd64 in
#print axioms old_makeSmall64_unsat
open Janus.Audit.MapsR3.Amd64 in
#print axioms old_assign64_vacuous
open Janus.Audit.MapsR3.Amd64 in
#print axioms old_makeSmall64_vacuous
