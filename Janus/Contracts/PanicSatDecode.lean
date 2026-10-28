import Janus.Contracts.PanicSatLoop

/-!
# The model's records, read as the contracts' defer chain

How one step of the model engine's loop (`PanicSatLoop`) changes the chain `defers0` of
`PanicModel`, and the calls (`Panic.recItems`) it still has to make afterwards.
-/

namespace Janus.Contracts.PanicSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic
open Janus.Contracts.PanicModel Janus.Spec.Map

/-! ## The invariant `Env0`, taken apart -/

theorem _root_.Janus.Contracts.PanicModel.Env0.acc {T : List FuncInfo} {m : Memory} (h : Env0 T m) : m.accessible B 0x1000 true = true := by
  unfold Env0 at h; exact h.1

theorem _root_.Janus.Contracts.PanicModel.Env0.npan_le {T : List FuncInfo} {m : Memory} (h : Env0 T m) : npan m ≤ 8 := by
  unfold Env0 at h; exact h.2.1

theorem _root_.Janus.Contracts.PanicModel.Env0.ndef_le {T : List FuncInfo} {m : Memory} (h : Env0 T m) : ndef m ≤ 8 := by
  unfold Env0 at h; exact h.2.2.1

theorem _root_.Janus.Contracts.PanicModel.Env0.rec {T : List FuncInfo} {m : Memory} (h : Env0 T m) :
    ∀ i, i < ndef m → recN m i ≤ 8 ∧ ((recTok m i = 0 ∨ recConv m i ≠ 0) → 1 ≤ recN m i) := by
  unfold Env0 at h; exact h.2.2.2.1

theorem _root_.Janus.Contracts.PanicModel.Env0.table {T : List FuncInfo} {m : Memory} (h : Env0 T m) : TableOK m T := by
  unfold Env0 at h; exact h.2.2.2.2

theorem _root_.Janus.Contracts.PanicModel.Env0.mk {T : List FuncInfo} {m : Memory} (h1 : m.accessible B 0x1000 true = true) (h2 : npan m ≤ 8)
    (h3 : ndef m ≤ 8)
    (h4 : ∀ i, i < ndef m → recN m i ≤ 8 ∧ ((recTok m i = 0 ∨ recConv m i ≠ 0) → 1 ≤ recN m i))
    (h5 : TableOK m T) : Env0 T m := by
  unfold Env0; exact ⟨h1, h2, h3, h4, h5⟩

/-! ## Records -/

/-- The plain record of one funcval. -/
abbrev pl (sp f : Nat) : DeferRec := { sp := sp, fns := [f] }

theorem defers0_top {T : List FuncInfo} {m : Memory} (h : Env0 T m) {j : Nat} (hj : ndef m = j + 1) :
    defers0 m = decRec m j ++ recList m j := by
  rw [defers0_eq, hj, Nat.min_eq_left (by have := h.ndef_le; omega)]; rfl

theorem defers0_nil {m : Memory} (h : ndef m = 0) : defers0 m = [] := by
  rw [defers0_eq, h]; rfl

theorem decRec_plain {m : Memory} {i : Nat} (h : recTok m i = 0 ∨ recConv m i ≠ 0) (hn : recN m i ≤ 8) :
    decRec m i = (recFns m i (recN m i)).map (pl (recSp m i)) := by
  unfold decRec; rw [if_pos h, Nat.min_eq_left hn]

theorem decRec_rf {m : Memory} {i : Nat} (h : ¬ (recTok m i = 0 ∨ recConv m i ≠ 0)) (hn : recN m i ≤ 8) :
    decRec m i = [{ sp := recSp m i, fns := recFns m i (recN m i), token := some (recTok m i) }] := by
  unfold decRec; rw [if_neg h, Nat.min_eq_left hn]

theorem recItems_plain_map (sp : Nat) (rs : List DeferRec) :
    ∀ fs : List Nat, recItems sp ((fs.map (pl sp)) ++ rs) = fnItems sp rs fs ++ recItems sp rs
  | [] => rfl
  | f :: fs => by
    have ih := recItems_plain_map sp rs fs
    simp [recItems, fnItems, ih, pl]

/-- The memory after the model took funcval `n` off the top record `j` (written with the record's
address). -/
theorem recTake_eq (m : Memory) (j n : Nat) : recTake m j n =
    if n = 0 then (((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 0).writeLE (B + 8) 8 j)
    else (m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 n := by
  unfold recTake
  have e1 : j * 96 + 66064 = recAt j + 16 := by simp only [recAt, B]; omega
  have e2 : j * 96 + 66072 = recAt j + 24 := by simp only [recAt, B]; omega
  rw [e1, e2]
  by_cases hn : n = 0
  · subst hn; simp [B]
  · simp [hn]


/-! ## Writes to the defer-record area -/

/-- A store into `ndef` or into the record area `[recAt 0, recAt 8)`. -/
def DefArea (a n : Nat) : Prop := (B + 8 ≤ a ∧ a + n ≤ B + 0x10) ∨ (recAt 0 ≤ a ∧ a + n ≤ recAt 8)

theorem panics0_wd {m : Memory} {a n v : Nat} (h : DefArea a n) : panics0 (m.writeLE a n v) = panics0 m := by
  rw [panics0_eq, panics0_eq, show npan (m.writeLE a n v) = npan m from
    rd_w (by unfold DefArea at h; simp only [recAt, B] at *; omega)]
  exact panList_w _ (by unfold DefArea at h; simp only [panAt, recAt, B] at *; omega)

theorem saved0_wd {m : Memory} {a n v : Nat} (h : DefArea a n) : saved0 (m.writeLE a n v) = saved0 m := by
  rw [saved0_eq, saved0_eq, rd_w (by unfold DefArea at h; simp only [recAt, B] at *; omega),
    rd_w (by unfold DefArea at h; simp only [recAt, B] at *; omega),
    rd_w (by unfold DefArea at h; simp only [recAt, B] at *; omega)]

theorem tableOK_wd {T : List FuncInfo} {m : Memory} {a n v : Nat} (h : DefArea a n) (ht : TableOK m T) :
    TableOK (m.writeLE a n v) T :=
  tableOK_w (by unfold DefArea at h; simp only [recAt, tabAt, B] at *; omega) ht

theorem npan_wd {m : Memory} {a n v : Nat} (h : DefArea a n) : npan (m.writeLE a n v) = npan m :=
  rd_w (by unfold DefArea at h; simp only [recAt, B] at *; omega)

theorem recField_w {m : Memory} {a n v i : Nat} (h : a + n ≤ recAt i ∨ recAt i + 96 ≤ a) :
    recSp (m.writeLE a n v) i = recSp m i ∧ recTok (m.writeLE a n v) i = recTok m i ∧
    recConv (m.writeLE a n v) i = recConv m i ∧ recN (m.writeLE a n v) i = recN m i := by
  refine ⟨rd_w ?_, rd_w ?_, rd_w ?_, rd_w ?_⟩ <;> (unfold recAt at h ⊢; omega)

theorem accessible_wd {m : Memory} {a n v : Nat} (b k : Nat) (w : Bool) :
    (m.writeLE a n v).accessible b k w = m.accessible b k w := Memory.accessible_writeLE ..

/-! ## One call off the top record -/

theorem defArea_conv {j : Nat} (hj : j < 8) : DefArea (recAt j + 16) 8 := by
  right; simp only [recAt, B]; omega

theorem defArea_n {j : Nat} (hj : j < 8) : DefArea (recAt j + 24) 8 := by
  right; simp only [recAt, B]; omega

theorem defArea_ndef : DefArea (B + 8) 8 := by
  left; simp only [B]; omega

/-- The chain after the model took funcval `n` off the top record `j` (`recN m j = n + 1`). -/
theorem defers0_recTake {T : List FuncInfo} {m : Memory} (h : Env0 T m) {j n : Nat}
    (hnd : ndef m = j + 1) (hn : recN m j = n + 1) :
    defers0 (recTake m j n) = (recFns m j n).map (pl (recSp m j)) ++ recList m j := by
  have hj : j < 8 := by have := h.ndef_le; omega
  have hn8 : n < 8 := by have := (h.rec j (by omega)).1; omega
  have hrl : ∀ {m' : Memory} {a k v : Nat}, (recAt j ≤ a) → recList (m'.writeLE a k v) j = recList m' j := fun {m' a k v} ha =>
    recList_w j (Or.inr ha)
  have hc : recAt j + 16 < recAt j + 96 := by omega
  have h256 : (256:Nat)^8 = 2^64 := by decide
  rw [recTake_eq]
  by_cases h0 : n = 0
  · subst h0
    rw [if_pos rfl, defers0_eq]
    have hnd' : ndef (((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 0).writeLE (B + 8) 8 j) = j := by
      simp only [ndef, rd]; rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
    rw [hnd', Nat.min_eq_left (by omega)]
    rw [recList_w j (Or.inl (by simp only [B, recAt]; omega)), hrl (by omega), hrl (by omega)]
    rfl
  · rw [if_neg h0, defers0_eq]
    have hnd' : ndef ((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 n) = j + 1 := by
      rw [← hnd]; simp only [ndef, rd]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp only [recAt, B]; omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by simp only [recAt, B]; omega)]
    rw [hnd', Nat.min_eq_left (by omega), recList_succ, hrl (by omega), hrl (by omega)]
    have f1 : recSp ((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 n) j = recSp m j := by
      simp only [recSp, rd]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp only [recAt, B]; omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by simp only [recAt, B]; omega)]
    have f2 : recConv ((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 n) j = 1 := by
      simp only [recConv, rd]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp only [recAt, B]; omega),
        Memory.readLE_writeLE_self]
    have f3 : recN ((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 n) j = n := by
      simp only [recN, rd]
      rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
    have f4 : recFns ((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 n) j n = recFns m j n := by
      rw [recFns_w j (by omega) n (by omega), recFns_w j (by omega) n (by omega)]
    rw [decRec_plain (by rw [f2]; right; omega) (by rw [f3]; omega), f1, f3, f4]

/-- The calls of a frame `sp` when its top record `j` still holds funcval `n`: that call, then the
calls of the chain after the model took it. -/
theorem rec_call_items {T : List FuncInfo} {m : Memory} (h : Env0 T m) {j n sp : Nat}
    (hnd : ndef m = j + 1) (hrs : recSp m j = sp) (hn : recN m j = n + 1) :
    recItems sp (defers0 m) = { fn := recFn m j n, bits := none, chain := defers0 (recTake m j n) } ::
      recItems sp (defers0 (recTake m j n)) := by
  have hn8 : n + 1 ≤ 8 := by have := (h.rec j (by omega)).1; omega
  have hd := defers0_top h hnd
  have ht := defers0_recTake h hnd hn
  rw [hd]
  rw [hrs] at ht
  by_cases hp : recTok m j = 0 ∨ recConv m j ≠ 0
  · rw [decRec_plain hp (by omega), hn, recFns_succ, hrs]
    simp only [List.map_cons, List.cons_append]
    rw [recItems, if_pos rfl, ht, fnItems]
    simp [fnItems]
  · rw [decRec_rf hp (by omega), hn, recFns_succ, hrs]
    simp only [List.singleton_append]
    rw [recItems, if_pos rfl, fnItems, ht, recItems_plain_map]
    simp only [List.cons_append]

theorem defers0_head {T : List FuncInfo} {m : Memory} (h : Env0 T m) {j : Nat} (hnd : ndef m = j + 1) :
    ∃ r rs, defers0 m = r :: rs ∧ r.sp = recSp m j ∧ (recN m j = 0 → rs = recList m j ∧ r.fns = []) := by
  have hr := h.rec j (by omega)
  rw [defers0_top h hnd]
  by_cases hp : recTok m j = 0 ∨ recConv m j ≠ 0
  · have h1 := hr.2 hp
    obtain ⟨k, hk⟩ : ∃ k, recN m j = k + 1 := ⟨recN m j - 1, by omega⟩
    rw [decRec_plain hp hr.1, hk, recFns_succ]
    exact ⟨_, _, rfl, rfl, fun h0 => by omega⟩
  · rw [decRec_rf hp hr.1]
    refine ⟨_, _, rfl, rfl, fun h0 => ?_⟩
    rw [h0]; exact ⟨rfl, rfl⟩

/-- No call left for frame `sp`: the chain is empty or its top record belongs to another frame. -/
theorem fin_items {T : List FuncInfo} {m : Memory} (h : Env0 T m) {sp : Nat}
    (hend : ndef m = 0 ∨ ∃ j, ndef m = j + 1 ∧ recSp m j ≠ sp) :
    recItems sp (defers0 m) = [] ∧ frameRest sp (defers0 m) = defers0 m := by
  rcases hend with hend | ⟨j, hnd, hs⟩
  · rw [defers0_nil hend]; exact ⟨rfl, rfl⟩
  · obtain ⟨r, rs, hd, hrs, -⟩ := defers0_head h hnd
    rw [hd]
    have : (r.sp == sp) = false := by simp only [beq_eq_false_iff_ne]; rw [hrs]; exact hs
    refine ⟨?_, ?_⟩
    · simp only [recItems]; rw [if_neg (by rw [hrs]; exact hs)]
    · simp [frameRest, List.dropWhile, this]

/-- The memory after the model popped the empty top record `j`. -/
def popMem (m : Memory) (j : Nat) : Memory := (m.writeLE (recAt j + 16) 8 1).writeLE (B + 8) 8 j

theorem popMem_eq (m : Memory) (j : Nat) :
    (m.writeLE (j * 96 + 66064) 8 1).writeLE 65544 8 j = popMem m j := by
  have e1 : j * 96 + 66064 = recAt j + 16 := by simp only [recAt, B]; omega
  unfold popMem; rw [e1]

theorem defers0_pop {T : List FuncInfo} {m : Memory} (h : Env0 T m) {j : Nat} (hnd : ndef m = j + 1)
    (hn : recN m j = 0) : defers0 (popMem m j) = recList m j := by
  have hj : j < 8 := by have := h.ndef_le; omega
  rw [defers0_eq]
  have hnd' : ndef (popMem m j) = j := by
    simp only [popMem, ndef, rd]; rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have : (256:Nat)^8 = 2^64 := by decide
                               omega)
  rw [hnd', Nat.min_eq_left (by omega), popMem,
    recList_w j (Or.inl (by simp only [B, recAt]; omega)), recList_w j (Or.inr (by omega))]

theorem pop_items {T : List FuncInfo} {m : Memory} (h : Env0 T m) {j sp : Nat} (hnd : ndef m = j + 1)
    (hrs : recSp m j = sp) (hn : recN m j = 0) :
    recItems sp (defers0 m) = recItems sp (defers0 (popMem m j)) ∧
      frameRest sp (defers0 m) = frameRest sp (defers0 (popMem m j)) := by
  obtain ⟨r, rs, hd, hsp, hh⟩ := defers0_head h hnd
  obtain ⟨hrs', hfns⟩ := hh hn
  rw [defers0_pop h hnd hn, hd, hrs']
  have : (r.sp == sp) = true := by simp [hsp, hrs]
  refine ⟨?_, ?_⟩
  · simp only [recItems]; rw [if_pos (by rw [hsp, hrs]), hfns]; rfl
  · simp [frameRest, List.dropWhile, this]

/-! ### The invariant and the bookkeeping across a step -/

theorem env0_popMem {T : List FuncInfo} {m : Memory} (h : Env0 T m) {j : Nat} (hnd : ndef m = j + 1) :
    Env0 T (popMem m j) := by
  have hj : j < 8 := by have := h.ndef_le; omega
  have hnd' : ndef (popMem m j) = j := by
    simp only [popMem, ndef, rd]; rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have : (256:Nat)^8 = 2^64 := by decide
                               omega)
  have hc := defArea_conv (j := j) hj
  refine Env0.mk ?_ ?_ (by rw [hnd']; omega) (fun i hi => ?_) ?_
  · unfold popMem; rw [accessible_wd, accessible_wd]; exact h.acc
  · unfold popMem; rw [npan_wd defArea_ndef, npan_wd hc]; exact h.npan_le
  · rw [hnd'] at hi
    unfold popMem
    obtain ⟨a1, a2, a3, a4⟩ := recField_w (m := m.writeLE (recAt j + 16) 8 1) (a := B + 8) (n := 8) (v := j) (i := i)
      (Or.inl (by simp only [B, recAt]; omega))
    obtain ⟨b1, b2, b3, b4⟩ := recField_w (m := m) (a := recAt j + 16) (n := 8) (v := 1) (i := i)
      (Or.inr (by simp only [recAt]; omega))
    rw [a2, a3, a4, b2, b3, b4]
    exact h.rec i (by omega)
  · unfold popMem; exact tableOK_wd defArea_ndef (tableOK_wd hc h.table)

theorem env0_recTake {T : List FuncInfo} {m : Memory} (h : Env0 T m) {j n : Nat} (hnd : ndef m = j + 1)
    (hn : recN m j = n + 1) : Env0 T (recTake m j n) := by
  have hj : j < 8 := by have := h.ndef_le; omega
  have hn8 : n + 1 ≤ 8 := by have := (h.rec j (by omega)).1; omega
  have hc := defArea_conv (j := j) hj
  have hcn := defArea_n (j := j) hj
  rw [recTake_eq]
  by_cases h0 : n = 0
  · subst h0
    rw [if_pos rfl]
    have hnd' : ndef (((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 0).writeLE (B + 8) 8 j) = j := by
      simp only [ndef, rd]; rw [Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256:Nat)^8 = 2^64 := by decide
                                 omega)
    refine Env0.mk ?_ ?_ (by rw [hnd']; omega) (fun i hi => ?_) ?_
    · rw [accessible_wd, accessible_wd, accessible_wd]; exact h.acc
    · rw [npan_wd defArea_ndef, npan_wd hcn, npan_wd hc]; exact h.npan_le
    · rw [hnd'] at hi
      obtain ⟨a1, a2, a3, a4⟩ := recField_w (m := (m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 0)
        (a := B + 8) (n := 8) (v := j) (i := i) (Or.inl (by simp only [B, recAt]; omega))
      obtain ⟨c1, c2, c3, c4⟩ := recField_w (m := m.writeLE (recAt j + 16) 8 1) (a := recAt j + 24) (n := 8)
        (v := 0) (i := i) (Or.inr (by simp only [recAt]; omega))
      obtain ⟨b1, b2, b3, b4⟩ := recField_w (m := m) (a := recAt j + 16) (n := 8) (v := 1) (i := i)
        (Or.inr (by simp only [recAt]; omega))
      rw [a2, a3, a4, c2, c3, c4, b2, b3, b4]
      exact h.rec i (by omega)
    · exact tableOK_wd defArea_ndef (tableOK_wd hcn (tableOK_wd hc h.table))
  · rw [if_neg h0]
    have hnd' : ndef ((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 n) = j + 1 := by
      rw [← hnd]; simp only [ndef, rd]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp only [recAt, B]; omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by simp only [recAt, B]; omega)]
    refine Env0.mk ?_ ?_ (by rw [hnd']; omega) (fun i hi => ?_) ?_
    · rw [accessible_wd, accessible_wd]; exact h.acc
    · rw [npan_wd hcn, npan_wd hc]; exact h.npan_le
    · rw [hnd'] at hi
      by_cases hij : i = j
      · subst hij
        have f2 : recConv ((m.writeLE (recAt i + 16) 8 1).writeLE (recAt i + 24) 8 n) i = 1 := by
          simp only [recConv, rd]
          rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp only [recAt, B]; omega),
            Memory.readLE_writeLE_self]
        have f3 : recN ((m.writeLE (recAt i + 16) 8 1).writeLE (recAt i + 24) 8 n) i = n := by
          simp only [recN, rd]
          rw [Memory.readLE_writeLE_self]
          exact Nat.mod_eq_of_lt (by have : (256:Nat)^8 = 2^64 := by decide
                                     omega)
        rw [f3]
        exact ⟨by omega, fun _ => by omega⟩
      · obtain ⟨c1, c2, c3, c4⟩ := recField_w (m := m.writeLE (recAt j + 16) 8 1) (a := recAt j + 24) (n := 8)
          (v := n) (i := i) (Or.inr (by simp only [recAt]; omega))
        obtain ⟨b1, b2, b3, b4⟩ := recField_w (m := m) (a := recAt j + 16) (n := 8) (v := 1) (i := i)
          (Or.inr (by simp only [recAt]; omega))
        rw [c2, c3, c4, b2, b3, b4]
        exact h.rec i (by omega)
    · exact tableOK_wd hcn (tableOK_wd hc h.table)

theorem panics0_recTake {m : Memory} {j n : Nat} (hj : j < 8) : panics0 (recTake m j n) = panics0 m := by
  rw [recTake_eq]; split
  · rw [panics0_wd defArea_ndef, panics0_wd (defArea_n hj), panics0_wd (defArea_conv hj)]
  · rw [panics0_wd (defArea_n hj), panics0_wd (defArea_conv hj)]

theorem saved0_recTake {m : Memory} {j n : Nat} (hj : j < 8) : saved0 (recTake m j n) = saved0 m := by
  rw [recTake_eq]; split
  · rw [saved0_wd defArea_ndef, saved0_wd (defArea_n hj), saved0_wd (defArea_conv hj)]
  · rw [saved0_wd (defArea_n hj), saved0_wd (defArea_conv hj)]

theorem panics0_popMem {m : Memory} {j : Nat} (hj : j < 8) : panics0 (popMem m j) = panics0 m := by
  unfold popMem; rw [panics0_wd defArea_ndef, panics0_wd (defArea_conv hj)]

theorem saved0_popMem {m : Memory} {j : Nat} (hj : j < 8) : saved0 (popMem m j) = saved0 m := by
  unfold popMem; rw [saved0_wd defArea_ndef, saved0_wd (defArea_conv hj)]

theorem room0_recTake {T : List FuncInfo} {m : Memory} (h : Env0 T m) {j n : Nat} (hnd : ndef m = j + 1)
    (hn : recN m j = n + 1) : room0 m ≤ room0 (recTake m j n) := by
  have hj : j < 8 := by have := h.ndef_le; omega
  have hn8 : n + 1 ≤ 8 := by have := (h.rec j (by omega)).1; omega
  have hc := defArea_conv (j := j) hj
  have hcn := defArea_n (j := j) hj
  have hcap : capMin m (min (ndef m) 8) = min (8 - (n + 1)) (capMin m j) := by
    rw [hnd, Nat.min_eq_left (by omega), capMin_succ, hn]
  rw [room0_eq, room0_eq, recTake_eq, hcap, hnd]
  have hnp : ∀ {m' : Memory} {a k v : Nat}, DefArea a k → npan (m'.writeLE a k v) = npan m' := fun h => npan_wd h
  by_cases h0 : n = 0
  · subst h0
    rw [if_pos rfl]
    have hnd' : ndef (((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 0).writeLE (B + 8) 8 j) = j := by
      simp only [ndef, rd]; rw [Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256:Nat)^8 = 2^64 := by decide
                                 omega)
    have hcm : capMin (((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 0).writeLE (B + 8) 8 j) j = capMin m j := by
      rw [capMin_w j (Or.inl (by simp only [B, recAt]; omega)), capMin_w j (Or.inr (by omega)),
        capMin_w j (Or.inr (by omega))]
    rw [hnp defArea_ndef, hnp hcn, hnp hc, hnd', Nat.min_eq_left (by omega : j ≤ 8), hcm]
    omega
  · rw [if_neg h0]
    have hnd' : ndef ((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 n) = j + 1 := by
      rw [← hnd]; simp only [ndef, rd]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp only [recAt, B]; omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by simp only [recAt, B]; omega)]
    have f3 : recN ((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 n) j = n := by
      simp only [recN, rd]
      rw [Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256:Nat)^8 = 2^64 := by decide
                                 omega)
    have hcm : capMin ((m.writeLE (recAt j + 16) 8 1).writeLE (recAt j + 24) 8 n) (j + 1) =
        min (8 - n) (capMin m j) := by
      rw [capMin_succ, capMin_w j (Or.inr (by omega)), capMin_w j (Or.inr (by omega)), f3]
    rw [hnp hcn, hnp hc, hnd', Nat.min_eq_left (by omega : j + 1 ≤ 8), hcm]
    omega

theorem room0_popMem {T : List FuncInfo} {m : Memory} (h : Env0 T m) {j : Nat} (hnd : ndef m = j + 1) :
    room0 m ≤ room0 (popMem m j) := by
  have hj : j < 8 := by have := h.ndef_le; omega
  have hc := defArea_conv (j := j) hj
  have hnd' : ndef ((m.writeLE (recAt j + 16) 8 1).writeLE (B + 8) 8 j) = j := by
    simp only [ndef, rd]; rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have : (256:Nat)^8 = 2^64 := by decide
                               omega)
  have hcap : capMin m (min (ndef m) 8) ≤ capMin m j := by
    rw [hnd, Nat.min_eq_left (by omega), capMin_succ]; omega
  have hcm : capMin ((m.writeLE (recAt j + 16) 8 1).writeLE (B + 8) 8 j) j = capMin m j := by
    rw [capMin_w j (Or.inl (by simp only [B, recAt]; omega)), capMin_w j (Or.inr (by omega))]
  rw [room0_eq, room0_eq]
  unfold popMem
  rw [npan_wd defArea_ndef, npan_wd hc, hnd', Nat.min_eq_left (by omega : j ≤ 8), hcm]
  rw [hnd] at hcap ⊢
  omega

theorem frameRest_pl_map (sp : Nat) (rs : List DeferRec) :
    ∀ fs : List Nat, frameRest sp ((fs.map (pl sp)) ++ rs) = frameRest sp rs
  | [] => rfl
  | f :: fs => by
    have ih := frameRest_pl_map sp rs fs
    simpa [frameRest, List.dropWhile, pl] using ih

theorem rec_call_rest {T : List FuncInfo} {m : Memory} (h : Env0 T m) {j n sp : Nat}
    (hnd : ndef m = j + 1) (hrs : recSp m j = sp) (hn : recN m j = n + 1) :
    frameRest sp (defers0 m) = frameRest sp (defers0 (recTake m j n)) := by
  have hn8 : n + 1 ≤ 8 := by have := (h.rec j (by omega)).1; omega
  have hd := defers0_top h hnd
  have ht := defers0_recTake h hnd hn
  rw [hd]
  rw [hrs] at ht
  by_cases hp : recTok m j = 0 ∨ recConv m j ≠ 0
  · rw [decRec_plain hp (by omega), hn, recFns_succ, hrs]
    simp only [List.map_cons, List.cons_append]
    rw [ht]; simp [frameRest, List.dropWhile, pl]
  · rw [decRec_rf hp (by omega), hn, recFns_succ, hrs]
    simp only [List.singleton_append]
    rw [ht, frameRest_pl_map]; simp [frameRest, List.dropWhile]

/-! ## The open-coded part -/

theorem openItems_congr {m m' : Memory} {sa b : Nat} {ds : List DeferRec}
    (h : ∀ i ∈ openBits b, m'.readLE (sa + 8 * i) 8 = m.readLE (sa + 8 * i) 8) :
    openItems m' sa b ds = openItems m sa b ds := by
  unfold openItems
  exact List.map_congr_left fun i hi => by simp only [h i hi]

set_option maxRecDepth 100000 in
theorem openBits_le_top : ∀ b, b < 256 → ∀ i ∈ openBits b, i ≤ topBit b := by decide

theorem openItems_top {m : Memory} {sa b : Nat} {ds : List DeferRec} (hb : b < 256) (hb0 : 0 < b) :
    openItems m sa b ds = { fn := m.readLE (sa + 8 * topBit b) 8, bits := some (b % 2 ^ topBit b), chain := ds } ::
      openItems m sa (b % 2 ^ topBit b) ds := by
  unfold openItems
  rw [openBits_top b hb hb0, List.map_cons]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have := openBits_le_top b hb i (openBits_mod_sub b hb hb0 i hi)
  simp only [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 this)]


/-! ## The records are read from the words a recovery leaves alone -/

/-- The words of the model's bookkeeping a recovery does not write (`npan` and the saved state are
the two it does). -/
def R2 : List (Nat × Nat) := [(B + 8, B + 0x10), (B + 0x28, B + 0x1000)]

theorem rd_agree2 {m m' : Memory} (h : Agrees m m' R2) {a : Nat} (h1 : B + 0x28 ≤ a)
    (h2 : a + 8 ≤ B + 0x1000) : rd m' a = rd m a :=
  h.readLE ⟨(B + 0x28, B + 0x1000), by simp [R2], h1, h2⟩

theorem decPan_agree2 {m m' : Memory} (h : Agrees m m' R2) {i : Nat} (hi : i < 8) :
    decPan m' i = decPan m i := by
  simp only [decPan, panAt]
  rw [rd_agree2 h (by simp [B]; omega) (by simp [B]; omega), rd_agree2 h (by simp [B]; omega) (by simp [B]; omega),
    rd_agree2 h (by simp [B]; omega) (by simp [B]; omega), rd_agree2 h (by simp [B]; omega) (by simp [B]; omega)]

theorem panList_agree2 {m m' : Memory} (h : Agrees m m' R2) :
    ∀ k, k ≤ 8 → panList m' k = panList m k
  | 0, _ => rfl
  | k + 1, hk => by simp only [panList, decPan_agree2 h (by omega : k < 8), panList_agree2 h k (by omega)]

theorem recFields_agree2 {m m' : Memory} (h : Agrees m m' R2) {i : Nat} (hi : i < 8) :
    recSp m' i = recSp m i ∧ recTok m' i = recTok m i ∧ recConv m' i = recConv m i ∧
      recN m' i = recN m i := by
  simp only [recSp, recTok, recConv, recN, recAt]
  refine ⟨rd_agree2 h (by simp [B]; omega) (by simp [B]; omega), rd_agree2 h (by simp [B]; omega) (by simp [B]; omega),
    rd_agree2 h (by simp [B]; omega) (by simp [B]; omega), rd_agree2 h (by simp [B]; omega) (by simp [B]; omega)⟩

theorem recFns_agree2 {m m' : Memory} (h : Agrees m m' R2) {i : Nat} (hi : i < 8) :
    ∀ j, j ≤ 8 → recFns m' i j = recFns m i j
  | 0, _ => rfl
  | j + 1, hj => by
    simp only [PanicModel.recFns, recFn, recAt]
    rw [rd_agree2 h (by simp [B]; omega) (by simp [B]; omega), recFns_agree2 h hi j (by omega)]

theorem decRec_agree2 {m m' : Memory} (h : Agrees m m' R2) {i : Nat} (hi : i < 8) :
    decRec m' i = decRec m i := by
  obtain ⟨h1, h2, h3, h4⟩ := recFields_agree2 h hi
  simp only [decRec, h1, h2, h3, h4, recFns_agree2 h hi _ (Nat.min_le_right _ _)]

theorem recList_agree2 {m m' : Memory} (h : Agrees m m' R2) :
    ∀ k, k ≤ 8 → recList m' k = recList m k
  | 0, _ => rfl
  | k + 1, hk => by simp only [recList, decRec_agree2 h (by omega : k < 8), recList_agree2 h k (by omega)]

theorem capMin_agree2 {m m' : Memory} (h : Agrees m m' R2) :
    ∀ k, k ≤ 8 → capMin m' k = capMin m k
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [capMin, (recFields_agree2 h (by omega : k < 8)).2.2.2, capMin_agree2 h k (by omega)]

theorem tableOK_agree2 {m m' : Memory} (h : Agrees m m' R2) {T : List FuncInfo}
    (ht : TableOK m T) : TableOK m' T := by
  obtain ⟨hl, hn, he⟩ := ht
  refine ⟨hl, by rw [rd_agree2 h (by simp [B]) (by simp [B])]; exact hn, fun i hi => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := he i hi
  have hb : ∀ k, k ≤ 48 → rd m' (tabAt i + k) = rd m (tabAt i + k) := fun k hk =>
    rd_agree2 h (by simp only [tabAt, B]; omega) (by simp only [tabAt, B]; omega)
  exact ⟨by rw [show tabAt i = tabAt i + 0 from rfl, hb 0 (by omega)]; exact e1,
    by rw [hb 8 (by omega)]; exact e2, by rw [hb 16 (by omega)]; exact e3,
    by rw [hb 24 (by omega)]; exact e4, by rw [hb 32 (by omega)]; exact e5,
    by rw [hb 40 (by omega)]; exact e6, by rw [hb 48 (by omega)]; exact e7⟩



/-- The two words a recovery writes (`npan` and the saved state). -/
def RecWords : List (Nat × Nat) := [(B, B + 8), (B + 0x10, B + 0x28)]

theorem agrees2_of_frame {m m' : Memory} (hf : MemFrame m m' RecWords) : Agrees m m' R2 :=
  Agrees.of_memFrame hf fun a ha => by
    obtain ⟨r, hr, h1, h2⟩ := ha
    simp only [R2, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    simp only [RecWords, outside_cons, outside_nil, and_true]
    rcases hr with rfl | rfl <;> simp only [B] at * <;> omega

theorem ndef_agree2 {m m' : Memory} (h : Agrees m m' R2) : ndef m' = ndef m :=
  h.readLE ⟨(B + 8, B + 0x10), by simp [R2], by simp [B], by simp [B]⟩

theorem recov_frame {T : List FuncInfo} {m m' : Memory} (h : Env0 T m) (hf : MemFrame m m' RecWords)
    (hnp : npan m' ≤ npan m) :
    Env0 T m' ∧ defers0 m' = defers0 m ∧ room0 m ≤ room0 m' ∧ (∀ k, k ≤ 8 → panList m' k = panList m k) := by
  have ha := agrees2_of_frame hf
  have hnd := ndef_agree2 ha
  have hnp8 := h.npan_le
  refine ⟨?_, ?_, ?_, fun k hk => panList_agree2 ha k hk⟩
  · refine Env0.mk (by rw [hf.accessible]; exact h.acc) (by omega) (by rw [hnd]; exact h.ndef_le) (fun i hi => ?_)
      (tableOK_agree2 ha h.table)
    rw [hnd] at hi
    obtain ⟨-, h2, h3, h4⟩ := recFields_agree2 ha (by have := h.ndef_le; omega : i < 8)
    rw [h2, h3, h4]; exact h.rec i hi
  · rw [defers0_eq, defers0_eq, hnd]; exact recList_agree2 ha _ (Nat.min_le_right _ _)
  · rw [room0_eq, room0_eq, hnd, capMin_agree2 ha _ (Nat.min_le_right _ _)]; omega


/-! ## Memory that agrees on the records, the table and `ndef` -/

/-- `m'` reads like `m` at `ndef`, the table's header and the table, and the records. -/
def RdSame (m m' : Memory) : Prop :=
  ∀ a, (a = B + 8 ∨ (B + 0x28 ≤ a ∧ a + 8 ≤ B + 0x100) ∨ (B + 0x200 ≤ a ∧ a + 8 ≤ B + 0x1000)) → rd m' a = rd m a

theorem RdSame.ndef {m m' : Memory} (h : RdSame m m') : ndef m' = ndef m := h _ (Or.inl rfl)

theorem rd_same {m m' : Memory} (h : RdSame m m') {a : Nat}
    (ha : a = B + 8 ∨ (B + 0x28 ≤ a ∧ a + 8 ≤ B + 0x100) ∨ (B + 0x200 ≤ a ∧ a + 8 ≤ B + 0x1000)) :
    rd m' a = rd m a := h a ha

theorem recFields_same {m m' : Memory} (h : RdSame m m') {i : Nat} (hi : i < 8) :
    recSp m' i = recSp m i ∧ recTok m' i = recTok m i ∧ recConv m' i = recConv m i ∧
      recN m' i = recN m i := by
  simp only [recSp, recTok, recConv, recN, recAt]
  refine ⟨rd_same h (by simp only [B]; omega), rd_same h (by simp only [B]; omega),
    rd_same h (by simp only [B]; omega), rd_same h (by simp only [B]; omega)⟩

theorem recFns_same {m m' : Memory} (h : RdSame m m') {i : Nat} (hi : i < 8) :
    ∀ j, j ≤ 8 → PanicModel.recFns m' i j = PanicModel.recFns m i j
  | 0, _ => rfl
  | j + 1, hj => by
    simp only [PanicModel.recFns, recFn, recAt]
    rw [rd_same h (by simp only [B]; omega), recFns_same h hi j (by omega)]

theorem decRec_same {m m' : Memory} (h : RdSame m m') {i : Nat} (hi : i < 8) : decRec m' i = decRec m i := by
  obtain ⟨h1, h2, h3, h4⟩ := recFields_same h hi
  simp only [decRec, h1, h2, h3, h4, recFns_same h hi _ (Nat.min_le_right _ _)]

theorem recList_same {m m' : Memory} (h : RdSame m m') : ∀ k, k ≤ 8 → recList m' k = recList m k
  | 0, _ => rfl
  | k + 1, hk => by simp only [recList, decRec_same h (by omega : k < 8), recList_same h k (by omega)]

theorem capMin_same {m m' : Memory} (h : RdSame m m') : ∀ k, k ≤ 8 → capMin m' k = capMin m k
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [capMin, (recFields_same h (by omega : k < 8)).2.2.2, capMin_same h k (by omega)]

theorem tableOK_same {m m' : Memory} (h : RdSame m m') {T : List FuncInfo} (ht : TableOK m T) : TableOK m' T := by
  obtain ⟨hl, hn, he⟩ := ht
  refine ⟨hl, by rw [rd_same h (by simp only [B]; omega)]; exact hn, fun i hi => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := he i hi
  have hl16 := hl
  have hb : ∀ k, k ≤ 48 → rd m' (tabAt i + k) = rd m (tabAt i + k) := fun k hk =>
    rd_same h (by simp only [tabAt, B]; omega)
  exact ⟨by rw [show tabAt i = tabAt i + 0 from rfl, hb 0 (by omega)]; exact e1,
    by rw [hb 8 (by omega)]; exact e2, by rw [hb 16 (by omega)]; exact e3,
    by rw [hb 24 (by omega)]; exact e4, by rw [hb 32 (by omega)]; exact e5,
    by rw [hb 40 (by omega)]; exact e6, by rw [hb 48 (by omega)]; exact e7⟩


theorem bundle3 {T : List FuncInfo} {m m' : Memory} (henv : Env0 T m) (hs : RdSame m m')
    (hacc : m'.accessible B 0x1000 true = true) (hnp : npan m' ≤ 8) :
    Env0 T m' ∧ defers0 m' = defers0 m ∧
      room0 m' = min (8 - npan m') (min (8 - ndef m) (capMin m (min (ndef m) 8))) := by
  have hnd := hs.ndef
  refine ⟨?_, ?_, ?_⟩
  · refine Env0.mk hacc hnp (by rw [hnd]; exact henv.ndef_le) (fun i hi => ?_) (tableOK_same hs henv.table)
    rw [hnd] at hi
    obtain ⟨-, h2, h3, h4⟩ := recFields_same hs (by have := henv.ndef_le; omega : i < 8)
    rw [h2, h3, h4]; exact henv.rec i hi
  · rw [defers0_eq, defers0_eq, hnd]; exact recList_same hs _ (Nat.min_le_right _ _)
  · rw [room0_eq, hnd, capMin_same hs _ (Nat.min_le_right _ _)]

theorem panList_frame {m m' : Memory} {ws : List (Nat × Nat)} (hf : MemFrame m m' ws) :
    ∀ k, (∀ i, i < k → Outside (panAt i) 32 ws) → panList m' k = panList m k
  | 0, _ => rfl
  | k + 1, h => by
    have ho := h k (by omega)
    have hd : decPan m' k = decPan m k := by
      simp only [decPan]
      have r : ∀ d, d ≤ 24 → rd m' (panAt k + d) = rd m (panAt k + d) := fun d hd =>
        hf.readLE _ _ (Outside.of_sub ho (by omega) (by omega))
      have r0 := r 0 (by omega)
      rw [Nat.add_zero] at r0
      rw [r0, r 8 (by omega), r 16 (by omega), r 24 (by omega)]
    simp only [panList, hd, panList_frame hf k (fun i hi => h i (by omega))]

end Janus.Contracts.PanicSat
