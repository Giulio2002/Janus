import Extracted

/-! Round 10 V2a: the map contract `Assign` with `M.Laws` is unsatisfiable together with
Insert's own precondition (`audit/round10/model/MapUnsat.lean`, copied below), so Insert's
theorem is vacuous: here it "proves" that `m[k] = v` stores `v + 1`. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map

namespace Proof
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

theorem chain {p : Program} {addr : Nat} {M : MapModel (BitVec 64) (BitVec 64)} (hA : Assign p addr M)
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
    (hl : M.Laws) (hA : Assign p addr M) {s : State} {f : AMap (BitVec 64) (BitVec 64)}
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


def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x24) (segWord Extracted.program "example.com/basic.Insert" 9)
    (segWord Extracted.program "example.com/basic.Insert" 10) 0

def callState (s : State) (a t : Nat) (m : BitVec 64) : State :=
  { s with pc := BitVec.ofNat 64 a, sp := BitVec.ofNat 64 (s.sp.toNat - 48),
           regs := fun i => if i = 0 then BitVec.ofNat 64 t else if i = 1 then m else if i = 30 then 0 else s.regs i }

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (hasn : Assign (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast64") M)
    (m k v : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k, v]
      (fun s => CallerOK M s 48 32 ∧ M.Typ mapType ∧ m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f)
      (fun s s' => M.Rep s'.mem m.toNat (f.set k (v + 1)) ∧ M.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hc, hty, hm0, hmap⟩
  exfalso
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_eval_nat hT : mapType
  let S := callState s (Extracted.program.contractAddr "runtime.mapassign_fast64") mapType m
  have hsp : S.sp.toNat = s.sp.toNat - 48 := by
    show (BitVec.ofNat 64 (s.sp.toNat - 48)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)]
  have h28 : S.regs 28 = s.regs 28 := rfl
  have h30 : S.regs 30 = 0 := rfl
  have h0 : (S.regs 0).toNat = mapType := by
    show (BitVec.ofNat 64 mapType).toNat = _
    rw [hT]; rfl
  have h1 : S.regs 1 = m := rfl
  have hpre : RTPre M 3 S := RTPre.of_parts (frame := 48) (above := 32) hc henv (fun _ _ _ => rfl) rfl hsp h28
    (by rw [h30]; decide) (by rw [h30]; decide) (by decide) (by decide)
  refine assign_unsat hl hasn (s := S) (f := f) rfl hpre (by rw [h0]; exact hty) (by rw [h1]; exact hm0)
    (by rw [h1]; exact hmap) ?_
  simp only [rtWrites, calleeStack, outside_append, outside_cons, outside_nil, and_true, hsp, h28]
  exact ⟨hgo, by omega, by omega⟩

end Proof
