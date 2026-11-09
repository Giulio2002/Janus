import Janus
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Map

/-! Round 10 V2b: the argument of `MapUnsat.lean`, restated against the fixed contracts (with the
readiness predicate `H`), must NOT compile: `H` is required at every call and not handed back.
Original comment: the map contract `Assign` (as of merge/b23,
`Janus/Contracts/Map.lean`, copied below verbatim as `OldAssign`; `MakeSmall` as `OldMakeSmall`)
cannot hold together with `M.Laws` for any program, address and
model `M` once a single call state meets its precondition. `Assign`'s precondition needs
`M.Env`, and its postcondition hands `M.Env` back for the memory after the caller's store into
the returned slot. So from one call state the contract chains to `2^64` inserts of distinct keys,
each still meeting the precondition, and the map then holds `2^64` keys, while the law `len`
says its header's first word (less than `2^64`) is that count. Hence every theorem that assumes
`Assign` together with a precondition that provides such a call state is vacuous (Insert,
InsertGet, ...). The real runtime fails much earlier: it runs out of memory. -/

namespace R10

/-- `Assign` before round 10 (merge/b23), verbatim. -/
def OldAssign (p : Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧
      M.Rep s.mem (s.regs 1).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun r m =>
      m.accessible (r 0).toNat 8 true = true ∧ InRanges (r 0).toNat 8 M.priv ∧
      ∀ v : BitVec 64, M.Rep (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 1).toNat (f.set (s.regs 2) v) ∧
        M.Env (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 28) ∧
        OthersKept M m (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 1).toNat)

/-- `MakeSmall` before round 10 (merge/b23), verbatim. -/
def OldMakeSmall {K V : Type} (p : Program) (addr : Nat) (M : MapModel K V) : Prop :=
  Summary p addr (fun s => RTPre M 0 s)
    (fun s s' => RTReturn M 0 [] 0 s s' fun r m =>
      (r 0).toNat ≠ 0 ∧ M.Rep m (r 0).toNat AMap.empty ∧
      ∀ mp f, M.Rep s.mem mp f → mp ≠ (r 0).toNat)

theorem nodup_len_ge : ∀ (N : Nat) (l : List (BitVec 64)), N ≤ 2 ^ 64 → l.Nodup →
    (∀ i, i < N → BitVec.ofNat 64 i ∈ l) → N ≤ l.length
  | 0, _, _, _, _ => Nat.zero_le _
  | N + 1, l, hN, hnd, hall => by
    have hx := hall N (by omega)
    have hlen := List.length_erase_of_mem hx
    have ih := nodup_len_ge N (l.erase (BitVec.ofNat 64 N)) (by omega) (hnd.erase _) (fun i hi => by
      rw [List.Nodup.mem_erase_iff hnd]
      refine ⟨fun h => ?_, hall i (by omega)⟩
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega)
    have : 0 < l.length := List.length_pos_of_mem hx
    omega

/-- `f` with the keys `0, …, n-1` set to `0`. -/
def insN (f : AMap (BitVec 64) (BitVec 64)) : Nat → AMap (BitVec 64) (BitVec 64)
  | 0 => f
  | n + 1 => (insN f n).set (BitVec.ofNat 64 n) 0

theorem insN_some (f : AMap (BitVec 64) (BitVec 64)) :
    ∀ n i, i < n → (insN f n (BitVec.ofNat 64 i)).isSome
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    simp only [insN, AMap.set]
    split
    · rfl
    · rename_i hne
      exact insN_some f n i (by
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
        · exact h
        · exact absurd (by rw [h]) hne)

/-- The call state `s` with memory `m` and key register `X2 = k`. -/
def callAt (s : State) (m : Memory) (k : BitVec 64) : State :=
  { s with mem := m, regs := fun i => if i = 2 then k else s.regs i }

/-- What carries from one insert to the next. -/
def Inv (M : MapModel (BitVec 64) (BitVec 64)) (s : State) (m : Memory) (f : AMap (BitVec 64) (BitVec 64)) : Prop :=
  M.Env m (s.regs 28) ∧ M.Rep m (s.regs 1).toNat f ∧ (∀ a n w, m.accessible a n w = s.mem.accessible a n w) ∧
    m.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8

theorem rtpre_at {M : MapModel (BitVec 64) (BitVec 64)} {s : State} {m : Memory} {f} {k : BitVec 64}
    (h : RTPre M 3 s) (hi : Inv M s m f) : RTPre M 3 (callAt s m k) := by
  obtain ⟨-, ⟨g1, g2, g3⟩, ⟨c1, c2, c3, c4, c5, c6, c7⟩, ho⟩ := h
  obtain ⟨he, -, hacc, hgw⟩ := hi
  refine ⟨he, ⟨g1, ?_, ?_⟩, ⟨c1, c2, c3, c4, c5, c6, ?_⟩, ho⟩
  · show m.accessible _ _ _ = true; rw [hacc]; exact g2
  · show m.readLE ((s.regs 28).toNat + stackguard0Offset) 8 + M.depth < s.sp.toNat
    have : m.readLE ((s.regs 28).toNat + stackguard0Offset) 8 = s.mem.readLE ((s.regs 28).toNat + stackguard0Offset) 8 := hgw
    rw [this]; exact g3
  · show m.accessible _ _ _ = true; rw [hacc]; exact c7

theorem chain {p : Program} {addr : Nat} {M : MapModel (BitVec 64) (BitVec 64)} {H : RtReady} (hA : Assign p addr M H)
    {s : State} {f : AMap (BitVec 64) (BitVec 64)}
    (hpc : s.pc = BitVec.ofNat 64 addr) (hpre : RTPre M 3 s) (ht : M.Typ (s.regs 0).toNat)
    (hm : (s.regs 1).toNat ≠ 0) (hgw : Outside ((s.regs 28).toNat + 16) 8 (rtWrites M s 3)) :
    ∀ n, Inv M s s.mem f → ∃ m, Inv M s m (insN f n)
  | 0, h0 => ⟨_, h0⟩
  | n + 1, h0 => by
    obtain ⟨m, hi⟩ := chain hA hpc hpre ht hm hgw n h0
    have hp := rtpre_at (k := BitVec.ofNat 64 n) hpre hi
    obtain ⟨-, s', -, -, r, v, fl, m', hs', hfr, -, -, hacc, hin, hall⟩ :=
      hA (insN f n) (callAt s m (BitVec.ofNat 64 n)) hpc ⟨hp, ht, hm, hi.2.1⟩
    obtain ⟨hrep, henv, -⟩ := hall 0
    refine ⟨m'.writeLE (r 0).toNat 8 (0 : BitVec 64).toNat, henv, hrep, fun a k w => ?_, ?_⟩
    · rw [Memory.accessible_writeLE, hfr.accessible]; exact hi.2.2.1 a k w
    · have hg' := hgw
      simp only [rtWrites, outside_append] at hg'
      rw [readLE_writeLE_disjoint m' _ (InRanges.disjoint hin hg'.1)]
      rw [hfr.readLE _ _ (by rw [List.append_nil]; exact hgw)]; exact hi.2.2.2

/-- `Assign`, `M.Laws` and one call state meeting `Assign`'s precondition (with the stack-guard
word outside what the call may write) are contradictory. -/
theorem assign_unsat {p : Program} {addr : Nat} {M : MapModel (BitVec 64) (BitVec 64)}
    (hl : M.Laws) {H : RtReady} (hA : Assign p addr M H) {s : State} {f : AMap (BitVec 64) (BitVec 64)}
    (hpc : s.pc = BitVec.ofNat 64 addr) (hpre : RTPre M 3 s) (ht : M.Typ (s.regs 0).toNat)
    (hm : (s.regs 1).toNat ≠ 0) (hrep : M.Rep s.mem (s.regs 1).toNat f)
    (hgw : Outside ((s.regs 28).toNat + 16) 8 (rtWrites M s 3)) : False := by
  obtain ⟨m, -, hr, -, -⟩ := chain hA hpc hpre ht hm hgw (2 ^ 64)
    ⟨hpre.1, hrep, fun _ _ _ => rfl, rfl⟩
  obtain ⟨ks, hks⟩ := hl.finite _ _ _ hr
  have hlen := (hl.len _ _ _ hr).2.2 ks hks
  have hge := nodup_len_ge (2 ^ 64) ks (Nat.le_refl _) hks.1
    (fun i hi => (hks.2 _).2 (insN_some f _ i hi))
  have := Memory.readLE_lt m (s.regs 1).toNat 8
  omega

/-! `MakeSmall`: every call returns a map distinct from every map represented before, and keeps
them all (`OthersKept`), with `M.Env` again. `2^48 + 1` calls give `2^48 + 1` distinct headers,
each below `2^48` (`Laws.len`). -/

theorem nodup_bounded : ∀ (B : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < B) → l.length ≤ B
  | 0, [], _, _ => Nat.le_refl _
  | 0, x :: _, _, h => absurd (h x (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | B + 1, l, hnd, h => by
    have ih := nodup_bounded B (l.erase B) (hnd.erase _) (fun x hx => by
      rw [List.Nodup.mem_erase_iff hnd] at hx
      have := h x hx.2; have := hx.1; omega)
    by_cases hB : B ∈ l
    · have := List.length_erase_of_mem hB
      have : 0 < l.length := List.length_pos_of_mem hB
      omega
    · rw [List.erase_of_not_mem hB] at ih; omega

def callAt0 (s : State) (m : Memory) : State := { s with mem := m }

def Inv0 (M : MapModel (BitVec 64) (BitVec 64)) (s : State) (m : Memory) (l : List Nat) : Prop :=
  M.Env m (s.regs 28) ∧ l.Nodup ∧ (∀ x ∈ l, x ≠ 0 ∧ M.Rep m x AMap.empty) ∧
    (∀ a n w, m.accessible a n w = s.mem.accessible a n w) ∧
    m.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8

theorem rtpre0_at {M : MapModel (BitVec 64) (BitVec 64)} {s : State} {m : Memory} {l}
    (h : RTPre M 0 s) (hi : Inv0 M s m l) : RTPre M 0 (callAt0 s m) := by
  obtain ⟨-, ⟨g1, g2, g3⟩, ⟨c1, c2, c3, c4, c5, c6, c7⟩, ho⟩ := h
  obtain ⟨he, -, -, hacc, hgw⟩ := hi
  refine ⟨he, ⟨g1, ?_, ?_⟩, ⟨c1, c2, c3, c4, c5, c6, ?_⟩, ho⟩
  · show m.accessible _ _ _ = true; rw [hacc]; exact g2
  · show m.readLE ((s.regs 28).toNat + stackguard0Offset) 8 + M.depth < s.sp.toNat
    have : m.readLE ((s.regs 28).toNat + stackguard0Offset) 8 = s.mem.readLE ((s.regs 28).toNat + stackguard0Offset) 8 := hgw
    rw [this]; exact g3
  · show m.accessible _ _ _ = true; rw [hacc]; exact c7

theorem chain0 {p : Program} {addr : Nat} {M : MapModel (BitVec 64) (BitVec 64)} {H : RtReady} (hA : MakeSmall p addr M H)
    {s : State} (hpc : s.pc = BitVec.ofNat 64 addr) (hpre : RTPre M 0 s)
    (hgw : Outside ((s.regs 28).toNat + 16) 8 (rtWrites M s 0)) :
    ∀ n, ∃ m l, Inv0 M s m l ∧ l.length = n
  | 0 => ⟨s.mem, [], ⟨hpre.1, List.nodup_nil, by simp, fun _ _ _ => rfl, rfl⟩, rfl⟩
  | n + 1 => by
    obtain ⟨m, l, hi, hl⟩ := chain0 hA hpc hpre hgw n
    obtain ⟨-, s', -, -, r, v, fl, m', hs', hfr, henv, hok, hne, hrep, hfresh⟩ :=
      hA (callAt0 s m) hpc (rtpre0_at hpre hi)
    refine ⟨m', (r 0).toNat :: l, ⟨henv, ?_, ?_, fun a k w => ?_, ?_⟩, by simp [hl]⟩
    · exact List.nodup_cons.2 ⟨fun hx => hfresh _ _ (hi.2.2.1 _ hx).2 rfl, hi.2.1⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hne, hrep⟩
      · exact ⟨(hi.2.2.1 x hx).1, hok x _ (hi.2.2.1 x hx).1 (hi.2.2.1 x hx).2⟩
    · rw [hfr.accessible]; exact hi.2.2.2.1 a k w
    · rw [hfr.readLE _ _ (by rw [List.append_nil]; exact hgw)]; exact hi.2.2.2.2

/-- `MakeSmall`, `M.Laws` and one call state meeting its precondition are contradictory. -/
theorem makeSmall_unsat {p : Program} {addr : Nat} {M : MapModel (BitVec 64) (BitVec 64)}
    (hl : M.Laws) {H : RtReady} (hA : MakeSmall p addr M H) {s : State}
    (hpc : s.pc = BitVec.ofNat 64 addr) (hpre : RTPre M 0 s)
    (hgw : Outside ((s.regs 28).toNat + 16) 8 (rtWrites M s 0)) : False := by
  obtain ⟨m, l, ⟨-, hnd, hall, -, -⟩, hlen⟩ := chain0 hA hpc hpre hgw (2 ^ 48 + 1)
  have := nodup_bounded (2 ^ 48) l hnd (fun x hx => by
    have := (hl.len _ _ _ (hall x hx).2).2.1; omega)
  omega

end R10
